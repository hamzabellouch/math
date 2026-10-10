import OAI.Analysis.CircleDomains.Modulus.FiniteCircleLinePayment
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! A quarter turn preserves the actual gradient energy used by line payment. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def quarterTurn : ℂ ≃ₗᵢ[ℝ] ℂ := rotation
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

@[simp] theorem quarterTurn_apply (z : ℂ) : quarterTurn z = Complex.I * z := rfl

@[simp] theorem quarterTurn_one : quarterTurn 1 = Complex.I := by simp

@[simp] theorem quarterTurn_I : quarterTurn Complex.I = -1 := by simp

theorem euclideanGradientEnergy_quarterTurn {v : ℂ → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (quarterTurn z)) :
    euclideanGradientEnergy (v ∘ quarterTurn) z = euclideanGradientEnergy v (quarterTurn z) := by
  have hd := (hv.hasFDerivAt.comp z quarterTurn.hasFDerivAt).fderiv
  unfold euclideanGradientEnergy
  rw [hd]
  change (fderiv ℝ v (quarterTurn z) (quarterTurn 1)) ^ 2 +
      (fderiv ℝ v (quarterTurn z) (quarterTurn Complex.I)) ^ 2 = _
  rw [quarterTurn_one, quarterTurn_I, map_neg, neg_sq]
  exact add_comm _ _

theorem integral_energy_quarterTurn
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v U)
    (hi : IntegrableOn (euclideanGradientEnergy v) U) :
    IntegrableOn (euclideanGradientEnergy (v ∘ quarterTurn)) (quarterTurn ⁻¹' U) ∧
      (∫ z in quarterTurn ⁻¹' U, euclideanGradientEnergy (v ∘ quarterTurn) z) =
        ∫ z in U, euclideanGradientEnergy v z := by
  have hm := quarterTurn.measurePreserving.restrict_preimage_emb
    quarterTurn.toMeasurableEquiv.measurableEmbedding U
  have hc : IntegrableOn (euclideanGradientEnergy v ∘ quarterTurn) (quarterTurn ⁻¹' U) :=
    (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : euclideanGradientEnergy (v ∘ quarterTurn) =ᵐ[volume.restrict (quarterTurn ⁻¹' U)]
      euclideanGradientEnergy v ∘ quarterTurn := by
    filter_upwards [ae_restrict_mem (hU.preimage quarterTurn.continuous).measurableSet] with z hz
    exact euclideanGradientEnergy_quarterTurn
      ((hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  refine ⟨hc.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact quarterTurn.measurePreserving.setIntegral_preimage_emb
    quarterTurn.toMeasurableEquiv.measurableEmbedding (euclideanGradientEnergy v) U

end CircleDomainRigidity

end

end OAI
