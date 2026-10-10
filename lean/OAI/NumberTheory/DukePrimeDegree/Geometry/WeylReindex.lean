import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalConditionalEntropy

namespace OAI

/-! # Permuting coordinates on the arithmetic quotient

Coordinate reversal transfers the increasing regular weight construction
to its decreasing counterpart. Reindexing preserves determinant one and
the integral lattice, so it acts on the actual quotient.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

def reindexSpecialLinear {n : ℕ} (R : Type*) [CommRing R]
    (e : Equiv.Perm (Fin n)) :
    Matrix.SpecialLinearGroup (Fin n) R ≃* Matrix.SpecialLinearGroup (Fin n) R where
  toFun M := ⟨Matrix.reindex e e M.val, by rw [Matrix.det_reindex_self]; exact M.prop⟩
  invFun M := ⟨Matrix.reindex e.symm e.symm M.val,
    by rw [Matrix.det_reindex_self]; exact M.prop⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (e.symm (e i)) (e.symm (e j)) = M.val i j
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (e (e.symm i)) (e (e.symm j)) = M.val i j
    rw [e.apply_symm_apply, e.apply_symm_apply]
  map_mul' A B := by
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv R e).map_mul A.val B.val

lemma continuous_reindexSpecialLinear {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Continuous (reindexSpecialLinear ℝ e) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (e.symm j)).comp
      ((continuous_apply (e.symm i)).comp continuous_subtype_val)

lemma reindexSpecialLinear_integral {n : ℕ} (e : Equiv.Perm (Fin n))
    {g : G n} (hg : g ∈ integralGroup n) :
    reindexSpecialLinear ℝ e g ∈ integralGroup n := by
  obtain ⟨a, rfl⟩ := hg
  refine ⟨reindexSpecialLinear ℤ e a, ?_⟩
  apply Subtype.ext
  rfl

def quotientReindex {n : ℕ} (e : Equiv.Perm (Fin n)) : X n → X n :=
  Quotient.map (reindexSpecialLinear ℝ e) (by
    intro a b hab
    change (QuotientGroup.rightRel (integralGroup n)) a b at hab
    change (QuotientGroup.rightRel (integralGroup n))
      (reindexSpecialLinear ℝ e a) (reindexSpecialLinear ℝ e b)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [map_mul, map_inv] using reindexSpecialLinear_integral e hab)

lemma quotientReindex_rightAction {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : X n) (g : G n) :
    quotientReindex e (rightAction x g) =
      rightAction (quotientReindex e x) (reindexSpecialLinear ℝ e g) := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) ((reindexSpecialLinear ℝ e).map_mul a g)

lemma quotientReindex_symm_apply {n : ℕ} (e : Equiv.Perm (Fin n)) (x : X n) :
    quotientReindex e.symm (quotientReindex e x) = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change Quotient.mk _ ((reindexSpecialLinear ℝ e).symm (reindexSpecialLinear ℝ e a)) =
      Quotient.mk _ a
    rw [MulEquiv.symm_apply_apply]

lemma continuous_quotientReindex {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Continuous (quotientReindex e) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_reindexSpecialLinear e)

def quotientReindexHomeomorph {n : ℕ} (e : Equiv.Perm (Fin n)) : X n ≃ₜ X n where
  toFun := quotientReindex e
  invFun := quotientReindex e.symm
  left_inv := quotientReindex_symm_apply e
  right_inv x := by simpa only [Equiv.symm_symm] using quotientReindex_symm_apply e.symm x
  continuous_toFun := continuous_quotientReindex e
  continuous_invFun := continuous_quotientReindex e.symm

end DukePrimeDegree

end

end OAI
