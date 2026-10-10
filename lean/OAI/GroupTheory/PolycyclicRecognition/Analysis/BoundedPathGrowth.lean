import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseMultiplicity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GromovInput
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-!
# From bounded-height word paths to polynomial growth

Word chains and a uniform metric multiplicity bound turn polynomial packing
of bounded-height chains into polynomial growth. Gromov's theorem then gives
virtual nilpotence of the subgroup.
-/

namespace PolycyclicRecognition

variable {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]

/-- A finite chain whose steps and heights are uniformly bounded. -/
inductive BoundedHeightChain (π : X → W) (L M : ℝ) : ℕ → X → X → Prop
  | nil (x : X) (hheight : ‖π x‖ ≤ M) : BoundedHeightChain π L M 0 x x
  | cons {n : ℕ} {x y z : X} (hheight : ‖π x‖ ≤ M) (hstep : dist x y ≤ L)
      (tail : BoundedHeightChain π L M n y z) : BoundedHeightChain π L M (n + 1) x z

/-- A pointwise height domination transfers every bounded-height chain. -/
theorem BoundedHeightChain.change_height
    {V : Type*} [NormedAddCommGroup V] {π : X → W} {π' : X → V}
    {L M M' : ℝ} {n : ℕ} {x y : X}
    (h : BoundedHeightChain π L M n x y)
    (hheight : ∀ z, ‖π z‖ ≤ M → ‖π' z‖ ≤ M') :
    BoundedHeightChain π' L M' n x y := by
  induction h with
  | nil x hx => exact .nil x (hheight x hx)
  | cons hx hstep _ ih => exact .cons (hheight _ hx) hstep ih

/-- Polynomial packing of bounded-height chains in the Lie model. -/
def PolynomialBoundedChainPacking [DecidableEq X] (π : X → W) : Prop :=
  ∀ (x : X) (L M : ℝ), 0 ≤ L → 0 ≤ M →
    ∃ (C b : ℕ) (centers : ℕ → Finset X),
      (∀ n, (centers n).card ≤ C * (1 + n) ^ b) ∧
      ∀ n m, m ≤ n → ∀ y, BoundedHeightChain π L M m x y →
        ∃ c ∈ centers n, dist y c ≤ 1

/-- It suffices to pack chains for a height dominated by the height in the
application, as when all representation characters factor through the
canonical quotient. -/
theorem polynomialBoundedChainPacking_of_height_domination
    {V : Type*} [NormedAddCommGroup V] [DecidableEq X]
    (π : X → W) (π' : X → V) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ x, ‖π' x‖ ≤ C * ‖π x‖)
    (packing : PolynomialBoundedChainPacking π') : PolynomialBoundedChainPacking π := by
  intro x L M hL hM
  obtain ⟨A, b, centers, hcard, hcover⟩ := packing x L (C * M) hL (mul_nonneg hC hM)
  refine ⟨A, b, centers, hcard, ?_⟩
  intro n m hm y hy
  apply hcover n m hm y
  exact hy.change_height fun z hz => (hdom z).trans (mul_le_mul_of_nonneg_left hz hC)

theorem boundedHeightChain_of_word {J : Type*} [Monoid J]
    (f : J → X) (π : X → W) (T : Finset J) {L M : ℝ}
    (hheight : ∀ j, ‖π (f j)‖ ≤ M)
    (hstep : ∀ j t, t ∈ T → dist (f j) (f (j * t)) ≤ L)
    (l : List J) (hl : ∀ t ∈ l, t ∈ T) (j : J) :
    BoundedHeightChain π L M l.length (f j) (f (j * l.prod)) := by
  induction l generalizing j with
  | nil => simpa using BoundedHeightChain.nil (L := L) (f j) (hheight j)
  | cons t l ih =>
    have ht := hl t (by simp)
    have htail : ∀ a ∈ l, a ∈ T := fun a ha => hl a (by simp [ha])
    simpa only [List.length_cons, List.prod_cons, mul_assoc] using
      BoundedHeightChain.cons (hheight j) (hstep j t ht) (ih htail (j * t))

theorem boundedHeightChain_of_mem_wordBall {J : Type*} [Monoid J] [DecidableEq J]
    (f : J → X) (π : X → W) (T : Finset J) {L M : ℝ}
    (hheight : ∀ j, ‖π (f j)‖ ≤ M)
    (hstep : ∀ j t, t ∈ T → dist (f j) (f (j * t)) ≤ L)
    {n : ℕ} {j : J} (hj : j ∈ wordBall T n) :
    ∃ m ≤ n, BoundedHeightChain π L M m (f 1) (f j) := by
  obtain ⟨l, hlen, hl, rfl⟩ := (mem_wordBall_iff T n j).mp hj
  exact ⟨l.length, hlen, by simpa using boundedHeightChain_of_word f π T hheight hstep l hl 1⟩

/-- A generating set, bounded steps and bounded multiplicity suffice for the
intrinsic growth argument. No metric or undistortion hypothesis on the domain
is required. -/
theorem virtuallyNilpotent_of_boundedHeight_steps
    {J : Type*} [Group J] [DecidableEq J] [DecidableEq X]
    (gromov : GromovPolynomialGrowthInput J)
    (f : J → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (T : Finset J) (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set J) = ⊤)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hheight : ∀ j, ‖π (f j)‖ ≤ M)
    (hstep : ∀ j t, t ∈ T → dist (f j) (f (j * t)) ≤ L)
    (N : ℕ) (hN : ∀ (c : X) (A : Finset J),
      (∀ j ∈ A, dist (f j) c ≤ 1) → A.card ≤ N) :
    Group.IsVirtuallyNilpotent J := by
  obtain ⟨A, b, centers, hcard, hcover⟩ := packing (f 1) L M hL hM
  apply virtuallyNilpotent_of_polynomial_cover gromov T hsymm hgen f A b N centers hcard
  · intro n j hj
    obtain ⟨m, hm, hchain⟩ := boundedHeightChain_of_mem_wordBall f π T hheight hstep hj
    exact hcover n m hm (f j) hchain
  · exact hN

/-- Intrinsic word growth follows from bounded height and the geometric chain
packing property, even when the chosen proper group metric is distorted with
respect to the intrinsic word metric. -/
theorem virtuallyNilpotent_of_boundedHeight
    {J : Type*} [Group J] [MetricSpace J] [IsIsometricSMul J J]
    [Group.FG J] [DecidableEq J] [DecidableEq X]
    (gromov : GromovPolynomialGrowthInput J)
    (f : J → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : J) R).Finite)
    {K C K' C' M : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hM : 0 ≤ M)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ j, ‖π (f j)‖ ≤ M) : Group.IsVirtuallyNilpotent J := by
  obtain ⟨T, hsymm, hgen⟩ := exists_symmetric_finite_generating_set (J := J)
  let R : ℝ := ∑ t ∈ T, dist (1 : J) t
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => dist_nonneg
  have hRbound (t : J) (ht : t ∈ T) : dist (1 : J) t ≤ R := by
    exact Finset.single_le_sum (f := fun t : J => dist 1 t) (fun _ _ => dist_nonneg) ht
  let L := K * R + C
  have hL : 0 ≤ L := add_nonneg (mul_nonneg hK hR) hC
  have hstep (j t : J) (ht : t ∈ T) : dist (f j) (f (j * t)) ≤ L := by
    apply (hupper j (j * t)).trans
    have hd : dist j (j * t) = dist (1 : J) t := by
      simpa only [mul_one] using dist_mul_left j (1 : J) t
    rw [hd]
    exact add_le_add (mul_le_mul_of_nonneg_left (hRbound t ht) hK) le_rfl
  obtain ⟨N, hN⟩ := exists_uniform_ball_multiplicity (r := 1) f hfinite hK' hlower
  obtain ⟨A, b, centers, hcard, hcover⟩ := packing (f 1) L M hL hM
  apply virtuallyNilpotent_of_polynomial_cover gromov T hsymm hgen f A b N centers hcard
  · intro n j hj
    obtain ⟨m, hm, hchain⟩ := boundedHeightChain_of_mem_wordBall f π T hheight hstep hj
    exact hcover n m hm (f j) hchain
  · exact hN

end PolycyclicRecognition

end OAI
