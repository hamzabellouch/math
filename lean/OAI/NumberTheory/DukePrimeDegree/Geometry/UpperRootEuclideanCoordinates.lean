import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationRootOrder
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootDilation
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootWindows

namespace OAI

/-!
# One real coordinate for each positive root

The elimination time space is canonically a finite product of real
lines, indexed without repetition by the positive roots. Diagonal
conjugation scales each coordinate by its own root character.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def realVectorConsHomeomorph (m : ℕ) : ((Fin m → ℝ) × ℝ) ≃ₜ (Fin (m + 1) → ℝ) where
  toFun p := Fin.cons p.2 p.1
  invFun v := (Fin.tail v, v 0)
  left_inv p := by simp
  right_inv v := Fin.cons_self_tail v
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => ℝ) continuous_snd continuous_fst
  continuous_invFun := (continuous_pi (fun _ => continuous_apply _)).prodMk (continuous_apply 0)

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def timeVectorHomeomorph : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.Time ≃ₜ (Fin c.roots.length → ℝ)
  | _, _, .done => Homeomorph.homeomorphOfUnique PUnit (Fin 0 → ℝ)
  | _, _, .step _ _ _ _ _ tail =>
      ((tail.timeVectorHomeomorph).prodCongr (Homeomorph.refl ℝ)).trans
        (realVectorConsHomeomorph tail.roots.length)

lemma timeVectorHomeomorph_cube (c : EliminationChain P D) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ k, |c.timeVectorHomeomorph t k| < R := by
  induction c with
  | done => simp [cube, roots]
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change t.1 ∈ tail.cube R ∧ t.2 ∈ Ioo (-R) R ↔
        ∀ k : Fin (tail.roots.length + 1),
          |Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ) t.2 (tail.timeVectorHomeomorph t.1) k| < R
      rw [ih, Set.mem_Ioo, ←abs_lt]
      constructor
      · rintro ⟨h₁, h₂⟩ k
        refine Fin.cases ?_ (fun j => ?_) k
        · simpa only [Fin.cons_zero] using h₂
        · simpa only [Fin.cons_succ] using h₁ j
      · intro h
        exact ⟨fun j => by simpa only [Fin.cons_succ] using h j.succ,
          by simpa only [Fin.cons_zero] using h 0⟩

lemma timeVectorHomeomorph_dilation (c : EliminationChain P D) (ell : Fin n → ℝ)
    (r : ℝ) (t : c.Time) (k : Fin c.roots.length) :
    c.timeVectorHomeomorph (c.rootDilation ell r t) k =
      Real.exp ((ell (c.roots.get k).1 - ell (c.roots.get k).2) * r) *
        c.timeVectorHomeomorph t k := by
  induction c with
  | done => exact Fin.elim0 k
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change Fin (tail.roots.length + 1) at k
      change Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
        (Real.exp ((ell a - ell b) * r) * t.2)
          (tail.timeVectorHomeomorph (tail.rootDilation ell r t.1)) k =
        Real.exp ((ell (((a, b) :: tail.roots).get k).1 -
          ell (((a, b) :: tail.roots).get k).2) * r) *
            Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
              t.2 (tail.timeVectorHomeomorph t.1) k
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · exact ih t.1 j

end EliminationChain

def upperRootIndexEquiv (n : ℕ) :
    Fin (completeRootChain n).roots.length ≃ (allPositiveRoots n) :=
  (List.Nodup.getEquiv _ (completeRootChain_roots_nodup n)).trans
    (Set.equivOfEq (by
      ext p
      change p ∈ (completeRootChain n).roots ↔ p ∈ allPositiveRoots n
      rw [←List.mem_toFinset, completeRootChain_roots_toFinset]))

def realCoordinatesReindex {α β : Type*} (e : α ≃ β) : (α → ℝ) ≃ₜ (β → ℝ) where
  toFun f b := f (e.symm b)
  invFun g a := g (e a)
  left_inv f := by funext a; simp
  right_inv g := by funext b; simp
  continuous_toFun := continuous_pi (fun _ => continuous_apply _)
  continuous_invFun := continuous_pi (fun _ => continuous_apply _)

def upperRootEuclideanCoordinates (n : ℕ) :
    UpperRootTime n ≃ₜ ((allPositiveRoots n) → ℝ) :=
  (completeRootChain n).timeVectorHomeomorph.trans (realCoordinatesReindex (upperRootIndexEquiv n))

@[simp] lemma upperRootIndexEquiv_val (n : ℕ) (k : Fin (completeRootChain n).roots.length) :
    (upperRootIndexEquiv n k).val = (completeRootChain n).roots.get k := rfl

lemma upperRootEuclideanCoordinates_cube (n : ℕ) (R : ℝ) (t : UpperRootTime n) :
    t ∈ (completeRootChain n).cube R ↔ ∀ p, |upperRootEuclideanCoordinates n t p| < R := by
  rw [(completeRootChain n).timeVectorHomeomorph_cube]
  constructor
  · intro h p
    exact h ((upperRootIndexEquiv n).symm p)
  · intro h k
    have H := h (upperRootIndexEquiv n k)
    change |(completeRootChain n).timeVectorHomeomorph t
      ((upperRootIndexEquiv n).symm (upperRootIndexEquiv n k))| < R at H
    simpa only [Equiv.symm_apply_apply] using H

lemma upperRootEuclideanCoordinates_dilation (n : ℕ) (ell : Fin n → ℝ)
    (r : ℝ) (t : UpperRootTime n) (p : allPositiveRoots n) :
    upperRootEuclideanCoordinates n ((completeRootChain n).rootDilation ell r t) p =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) * upperRootEuclideanCoordinates n t p := by
  have h := (completeRootChain n).timeVectorHomeomorph_dilation ell r t
    ((upperRootIndexEquiv n).symm p)
  have he : (completeRootChain n).roots.get ((upperRootIndexEquiv n).symm p) = p.val := by
    exact congrArg Subtype.val ((upperRootIndexEquiv n).apply_symm_apply p)
  change (completeRootChain n).timeVectorHomeomorph
    ((completeRootChain n).rootDilation ell r t) ((upperRootIndexEquiv n).symm p) =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) *
        (completeRootChain n).timeVectorHomeomorph t ((upperRootIndexEquiv n).symm p)
  simpa only [he] using h

end DukePrimeDegree

end

end OAI
