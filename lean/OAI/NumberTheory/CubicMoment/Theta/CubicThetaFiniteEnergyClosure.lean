import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspExhaustionBounds
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaL2Dominated
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactC1Energy

namespace OAI

/-! Every C1 automorphic section with square-integrable value and gradient
belongs to the actual closed energy graph. Compact cusp exhaustion supplies
the approximants, with no extra boundary condition imposed at the cusps. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaFiniteEnergy_mem_graph (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hv : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    (hg : MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure) :
    WithLp.toLp 2 (hv.toLp _,hg.toLp _)∈cubicThetaGlobalEnergySpace := by
  obtain ⟨S,T,hcover,hdisj⟩ := cubicThetaDisjointCuspCover
  let G := fun n : ℕ => cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F
  have hG (n : ℕ) : ContDiffOn ℝ 1 (cubicThetaSectionFunction (G n)) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaSectionCutoff_regular _ ((cubicThetaCuspExhaustion_smooth T n).of_le (by simp)) F hF
  have hcG (n : ℕ) : HasCompactSupport (cubicThetaSectionNorm (G n)) :=
    cubicThetaSectionCutoff_compact _ F (cubicThetaCuspExhaustion_compact S T hcover hdisj n)
  have hvG (n : ℕ) := cubicThetaCompactSection_memLp (G n) (hcG n)
  have hgG (n : ℕ) := cubicThetaC1Gradient_memLp (G n) (hG n) (hcG n)
  have hiv := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hig := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hvlim : Tendsto (fun n => (hvG n).toLp _) atTop (𝓝 (hv.toLp _)) := by
    apply cubicThetaL2_tendsto_of_dominated_sq _ _ hvG hv
      (fun q => (2+(T.card:ℝ))^2*‖cubicThetaSectionRepresentative F q‖^2)
      (hiv.const_mul _)
    · intro n
      exact Filter.Eventually.of_forall (cubicThetaCuspExhaustion_value_bound T F n)
    · apply Filter.Eventually.of_forall
      intro q
      have he : (fun n => cubicThetaSectionRepresentative (G n) q)=ᶠ[atTop]
          (fun _ => cubicThetaSectionRepresentative F q) := cubicThetaCuspExhaustion_value_agrees T F q
      exact tendsto_const_nhds.congr' he.symm
  obtain ⟨B,_,hbound⟩ := cubicThetaCuspExhaustion_gradient_bound T F hF
  have hglim : Tendsto (fun n => (hgG n).toLp _) atTop (𝓝 (hg.toLp _)) := by
    apply cubicThetaL2_tendsto_of_dominated_sq _ _ hgG hg
      (fun q => 2*(2+(T.card:ℝ))^2*‖cubicThetaGradientRepresentative F q‖^2+
        2*B*‖cubicThetaSectionRepresentative F q‖^2)
      ((hig.const_mul _).add (hiv.const_mul _))
    · intro n
      exact Filter.Eventually.of_forall (hbound n)
    · apply Filter.Eventually.of_forall
      intro q
      have he : (fun n => cubicThetaGradientRepresentative (G n) q)=ᶠ[atTop]
          (fun _ => cubicThetaGradientRepresentative F q) := cubicThetaCuspExhaustion_gradient_agrees T F q
      exact tendsto_const_nhds.congr' he.symm
  have hlim : Tendsto (fun n => cubicThetaC1EnergyData (G n) (hG n) (hcG n)) atTop
      (𝓝 (WithLp.toLp 2 (hv.toLp _,hg.toLp _))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).symm.continuous.tendsto
      (hv.toLp _,hg.toLp _)).comp (hvlim.prodMk_nhds hglim)
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n => cubicThetaCompactC1_mem_energy (G n) (hG n) (hcG n)))

end CubicFirstMoment

end

end OAI
