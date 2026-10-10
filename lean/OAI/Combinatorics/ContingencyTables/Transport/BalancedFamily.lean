import OAI.Combinatorics.ContingencyTables.Transport.BalancedBox
import OAI.Combinatorics.ContingencyTables.Transport.IntegerReflection

namespace OAI

/-!
# All finite balanced-pair eliminations

The coordinates are the retained small coordinates followed by the actual
finite list of large-cell pairs. The recursion performs their finite
balanced sums and proves the total-slice positivity and removal signature
at every step.
-/

namespace ContingencyTables.BalancedFamily

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox

universe u

@[reducible] def Coordinates (I : Type u) : List ℕ → Type u
  | [] => I
  | _ :: Ms => Coordinates I Ms ⊕ Bool

@[reducible] instance coordinatesFintype {I : Type*} [Fintype I] (Ms : List ℕ) :
    Fintype (Coordinates I Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (Fintype I)
  | cons M Ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Coordinates I Ms ⊕ Bool))

@[reducible] instance coordinatesDecidableEq {I : Type*} [DecidableEq I] (Ms : List ℕ) :
    DecidableEq (Coordinates I Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (DecidableEq I)
  | cons M Ms ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Coordinates I Ms ⊕ Bool))

def bounds {I : Type*} (m : I → ℕ) : (Ms : List ℕ) → Coordinates I Ms → ℕ
  | [] => m
  | M :: Ms => profile (bounds m Ms) M M

noncomputable def eliminate {I : Type*} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], F => F
  | M :: Ms, F => eliminate Ms (marginal F M)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every actual large-cell pair has width at least two; eliminating all
of them preserves precisely the required box-valid total slice. -/
theorem eliminate_slices (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M)
    (hpos : PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : RemovalSlice F (bounds m Ms) (R+Ms.sum)) :
    PositiveSlice (eliminate Ms F) m R ∧ RemovalSlice (eliminate Ms F) m R := by
  induction Ms with
  | nil => simpa only [List.sum_nil,add_zero,eliminate,bounds] using And.intro hpos hsig
  | cons M Ms ih =>
    have htotal : R+(M::Ms).sum = (R+Ms.sum)+M := by simp only [List.sum_cons]; omega
    rw [htotal] at hpos hsig
    have hp := marginal_positive_slice F (bounds m Ms) (R+Ms.sum) M hpos
    have hs := marginal_removal_slice F (bounds m Ms) (R+Ms.sum) M
      (hwidth M (by simp)) hpos hsig
    exact ih (marginal F M) (fun N hN => hwidth N (by simp [hN])) hp hs

omit [DecidableEq I] in
/-- Only the paper's finite box and required total slice are ever read
by a balanced marginal. In particular its zero extension is harmless. -/
theorem eliminate_congr_slice (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (F f : (Coordinates I Ms → ℕ) → ℝ)
    (heq : ∀ x, InBox (bounds m Ms) x → (∑ i, x i)=R+Ms.sum → F x=f x)
    (z : I → ℕ) (hz : InBox m z) (htotal : (∑ i, z i)=R) :
    eliminate Ms F z=eliminate Ms f z := by
  induction Ms with
  | nil => exact heq z hz (by simpa using htotal)
  | cons M Ms ih =>
    apply ih (marginal F M) (marginal f M)
    intro x hx hxtotal
    apply Finset.sum_congr rfl
    intro j hj
    have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
    apply heq _ (profile_inBox (bounds m Ms) x M j (M-j) hx hjM (Nat.sub_le _ _))
    rw [profile_total,hxtotal]
    simp only [List.sum_cons]
    omega

omit [Fintype I] [DecidableEq I] in
theorem eliminate_nonnegative (Ms : List ℕ) (F : (Coordinates I Ms → ℕ) → ℝ)
    (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) : 0 ≤ eliminate Ms F z := by
  induction Ms with
  | nil => exact hF z
  | cons M Ms ih =>
    apply ih (marginal F M)
    intro x
    apply Finset.sum_nonneg
    intro j _
    exact hF (profile x j (M-j))

omit [Fintype I] [DecidableEq I] in
/-- Reflection reverses the finite index in every summed large pair and
also reflects every retained coordinate. -/
theorem eliminate_reflect (Ms : List ℕ) (m : I → ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms (fun x => F (IntegerReflection.reflect (bounds m Ms) x)) z =
      eliminate Ms F (IntegerReflection.reflect m z) := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    have he : marginal (fun x => F (IntegerReflection.reflect (bounds m (M::Ms)) x)) M =
        fun x => marginal F M (IntegerReflection.reflect (bounds m Ms) x) := by
      funext x
      exact IntegerReflection.marginal_reflect F (bounds m Ms) x M
    change eliminate Ms (marginal (fun x => F (IntegerReflection.reflect (bounds m (M::Ms)) x)) M) z = _
    rw [he]
    exact ih (marginal F M)

omit [Fintype I] [DecidableEq I] in
/-- All balanced eliminations are finite sums, so their actual values
commute with the equality-softening limit. -/
theorem eliminate_tendsto {K : Type*} {l : Filter K} (Ms : List ℕ)
    (F : K → (Coordinates I Ms → ℕ) → ℝ) (f : (Coordinates I Ms → ℕ) → ℝ)
    (hlim : ∀ z, Filter.Tendsto (fun t => F t z) l (nhds (f z))) (z : I → ℕ) :
    Filter.Tendsto (fun t => eliminate Ms (F t) z) l (nhds (eliminate Ms f z)) := by
  induction Ms with
  | nil => exact hlim z
  | cons M Ms ih =>
    apply ih (fun t => marginal (F t) M) (marginal f M)
    intro x
    unfold marginal
    apply tendsto_finsetSum
    intro j _
    exact hlim (profile x j (M-j))

end ContingencyTables.BalancedFamily

end OAI
