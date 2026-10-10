import OAI.NumberTheory.CubicMoment.Estimates.IndependentMellin
import OAI.NumberTheory.CubicMoment.Angular.AngularShortUnsplitTuple

namespace OAI

/-! Independent smooth weights on the original arithmetic factors, with the
exact Mellin representation by the unweighted convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularCoordinateWeightedTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    primaryAngularTupleCore ℓ A a b q η t V Y n * ∏ i, W i (norm (n i)/X i)

omit [DecidableEq ι] in
lemma primaryAngularTupleCore_shift (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t τ : ι → ℝ)
    (V : ℝ → ℂ) (Y : ℝ) (n : ι → Eisenstein) :
    primaryAngularTupleCore ℓ A a b q η t V Y n * ∏ i, mellinPhase (-(τ i)) (norm (n i)) =
      primaryAngularTupleCore ℓ A a b q η (fun i => t i-τ i) V Y n := by
  unfold primaryAngularTupleCore
  rw [mul_right_comm,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_assoc,mul_assoc,← mellinPhase_add]
  congr 2

lemma continuous_primaryAngularUnsplitTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (V : ℝ → ℂ) (Y : ℝ) :
    Continuous (fun t : ι → ℝ => primaryAngularUnsplitTuple ℓ A a b q η t V Y) := by
  unfold primaryAngularUnsplitTuple primaryAngularTupleCore mellinPhase
  fun_prop

 theorem primaryAngularCoordinateWeightedTuple_mellin (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    primaryAngularCoordinateWeightedTuple ℓ A a b q η t W X V Y =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        primaryAngularUnsplitTuple ℓ A a b q η (fun i => t i-τ i) V Y := by
  let S := Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))
  have hN (i : ι) (n : S) : 0 < norm (n.val i) :=
    norm_pos_of_ne_zero (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp n.property) i)).1)
  have hm := independent_mellin_finite
    (fun n : S => primaryAngularTupleCore ℓ A a b q η t V Y n.val)
    (fun i (n : S) => norm (n.val i)) hN W X hW hpos hsm hX
  have hl : (∑ n : S, primaryAngularTupleCore ℓ A a b q η t V Y n.val *
      ∏ i, W i (norm (n.val i)/X i)) = primaryAngularCoordinateWeightedTuple ℓ A a b q η t W X V Y := by
    change (∑ n ∈ S.attach, _) = _
    rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
      primaryAngularTupleCore ℓ A a b q η t V Y n * ∏ i, W i (norm (n i)/X i))]
    rfl
  rw [hl] at hm
  rw [hm]
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  simp_rw [primaryAngularTupleCore_shift ℓ]
  change (∑ n ∈ S.attach, primaryAngularTupleCore ℓ A a b q η (fun i => t i-τ i) V Y n.val) = _
  rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
    primaryAngularTupleCore ℓ A a b q η (fun i => t i-τ i) V Y n)]
  rfl

end CubicFirstMoment

end

end OAI
