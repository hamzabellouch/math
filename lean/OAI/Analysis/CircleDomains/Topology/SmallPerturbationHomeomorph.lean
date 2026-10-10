import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! Small globally Lipschitz perturbations of the identity give actual
ambient homeomorphisms. These are the deformation maps for regular collars. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma approximatesLinearOn_id_add {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) :
    ApproximatesLinearOn (fun z => z + V z) ((ContinuousLinearEquiv.refl ℝ ℂ) : ℂ →L[ℝ] ℂ)
      univ L := by
  apply LipschitzOnWith.approximatesLinearOn
  rw [lipschitzOnWith_univ]
  convert hV using 1
  ext z
  simp

 def smallPerturbationHomeomorph (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) : ℂ ≃ₜ ℂ :=
  (approximatesLinearOn_id_add hV).toHomeomorph (fun z => z + V z)
    (Or.inr (by simpa using hL))

@[simp] lemma smallPerturbationHomeomorph_apply (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (z : ℂ) :
    smallPerturbationHomeomorph V hV hL z = z + V z := rfl

lemma smallPerturbationHomeomorph_inverse_dist (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (M : ℝ)
    (hM : ∀ z, ‖V z‖ ≤ M) (z : ℂ) :
    dist ((smallPerturbationHomeomorph V hV hL).symm z) z ≤ M := by
  let T := smallPerturbationHomeomorph V hV hL
  have hz : T.symm z + V (T.symm z) = z := T.apply_symm_apply z
  rw [dist_eq_norm]
  have he : T.symm z - z = - V (T.symm z) := by
    calc
      T.symm z - z = T.symm z - (T.symm z + V (T.symm z)) := congrArg (fun w => T.symm z - w) hz.symm
      _ = _ := by abel
  change ‖T.symm z - z‖ ≤ M
  rw [he, norm_neg]
  exact hM _

lemma smallPerturbationHomeomorph_smooth {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (hs : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (smallPerturbationHomeomorph V hV hL) :=
  contDiff_id.add hs

lemma id_add_fderiv_injective {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) {z : ℂ}
    (hd : DifferentiableAt ℝ V z) :
    Injective (fderiv ℝ (fun w => w + V w) z) := by
  have hb := norm_fderiv_le_of_lipschitz ℝ hV (x₀ := z)
  change Injective (fderiv ℝ (id + V) z)
  rw [fderiv_add differentiableAt_id hd, fderiv_id]
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have he : (fderiv ℝ V z) v = -v := by
    change v + (fderiv ℝ V z) v = 0 at hv
    exact eq_neg_of_add_eq_zero_right hv
  have hh : ‖v‖ ≤ (L : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖(fderiv ℝ V z) v‖ := by rw [he, norm_neg]
      _ ≤ ‖fderiv ℝ V z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hL' : (L : ℝ) < 1 := hL
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

lemma smallPerturbationHomeomorph_inverse_smooth {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L<1) (hs : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ ((smallPerturbationHomeomorph V hV hL).symm : ℂ → ℂ) := by
  let H := smallPerturbationHomeomorph V hV hL
  have hinj (z : ℂ) := id_add_fderiv_injective hV hL (hs.differentiable (by simp) z)
  let A (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ (fun w => w+V w) z).toLinearMap
      ⟨hinj z,(LinearMap.injective_iff_surjective).mp (hinj z)⟩).toContinuousLinearEquiv
  have hd (z : ℂ) : HasFDerivAt (H : ℂ → ℂ) (A z : ℂ →L[ℝ] ℂ) z :=
    ((contDiff_id.add hs).differentiable (by simp) z).hasFDerivAt
  exact H.contDiff_symm hd (contDiff_id.add hs)

end CircleDomainRigidity

end

end OAI
