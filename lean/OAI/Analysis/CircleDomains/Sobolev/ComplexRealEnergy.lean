import OAI.Analysis.CircleDomains.Sobolev.PlanarGradientDensity
import OAI.Analysis.CircleDomains.Sobolev.CoordinateEstimates

namespace OAI

/-!
# Identifying the line-payment energy with the transferred real energy

The finite transfer uses real coordinate pairs, while round disks and
line payment use complex coordinates. The canonical linear equivalence
preserves volume and identifies the two ordinary gradient integrands.
-/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem euclideanGradientEnergy_eq_real_gradientEnergy
    {F : (ℝ × ℝ) → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℝ F (Complex.equivRealProdCLM z)) :
    euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM) z =
      gradientEnergy F (fun _ => 1) (Complex.equivRealProdCLM z) := by
  have hd := (hF.hasFDerivAt.comp z Complex.equivRealProdCLM.hasFDerivAt).fderiv
  unfold euclideanGradientEnergy gradientEnergy
  rw [hd, covectorEnergy_identity]
  rfl

theorem real_gradient_energy_in_complex_coordinates
    {O S : Set (ℝ × ℝ)} (hO : IsOpen O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    {F : (ℝ × ℝ) → ℝ} (hF : ContDiffOn ℝ 1 F O)
    (hi : IntegrableOn (gradientEnergy F (fun _ => 1)) S) :
    IntegrableOn (euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM))
      (Complex.equivRealProdCLM ⁻¹' S) ∧
      (∫ z in Complex.equivRealProdCLM ⁻¹' S,
        euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM) z) =
        ∫ x in S, gradientEnergy F (fun _ => 1) x := by
  have hmp := Complex.volume_preserving_equiv_real_prod.restrict_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding S
  have hcomp : IntegrableOn (fun z : ℂ => gradientEnergy F (fun _ => 1)
      (Complex.equivRealProdCLM z)) (Complex.equivRealProdCLM ⁻¹' S) :=
    (hmp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have heq : euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM) =ᵐ[
      volume.restrict (Complex.equivRealProdCLM ⁻¹' S)]
      (fun z => gradientEnergy F (fun _ => 1) (Complex.equivRealProdCLM z)) := by
    filter_upwards [ae_restrict_mem (hS.preimage Complex.equivRealProdCLM.continuous.measurable)] with z hz
    exact euclideanGradientEnergy_eq_real_gradientEnergy
      ((hF.contDiffAt (hO.mem_nhds (hSO hz))).differentiableAt (by norm_num))
  refine ⟨hcomp.congr heq.symm, ?_⟩
  calc
    _ = ∫ z in Complex.equivRealProdCLM ⁻¹' S,
        gradientEnergy F (fun _ => 1) (Complex.equivRealProdCLM z) := integral_congr_ae heq
    _ = _ := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding _ S

end CircleDomainRigidity

end

end OAI
