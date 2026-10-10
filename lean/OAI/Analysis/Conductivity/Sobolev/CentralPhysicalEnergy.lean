import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalChildIntegral
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma centralPhysicalWholeCLM_norm (f : CentralL2) :
    ‖centralPhysicalWholeCLM f‖=‖f‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℝ sourcePairMeasurable sourcePair_volume)
    (lpZeroExtensionCLM centralClosed_compact.measurableSet f)‖=‖f‖
  rw [LinearIsometry.norm_map]
  exact lpZeroExtensionL_norm centralClosed_compact.measurableSet f

def centralPhysicalWholeLI : CentralL2 →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) where
  toLinearMap := centralPhysicalWholeCLM.toLinearMap
  norm_map' := centralPhysicalWholeCLM_norm

lemma centralPhysicalWholeCLM_ae (f : CentralL2) :
    centralPhysicalWholeCLM f=ᵐ[volume]
      (fun y => centralPhysical.indicator (fun y => f (sourcePairCoordinates y)) y) := by
  apply (Lp.coeFn_compMeasurePreserving _ sourcePair_volume).trans
  have he := sourcePair_volume.quasiMeasurePreserving.ae_eq_comp
    (lpZeroExtensionCLM_ae centralClosed_compact.measurableSet f)
  apply he.trans
  filter_upwards [] with y
  by_cases h : sourcePairCoordinates y∈centralClosed <;>
    simp [sourcePairMeasurable_apply,centralPhysical,h]
  rfl

lemma centralPhysicalWholeCLM_integral (f g : CentralL2) :
    IntegrableOn (fun y => centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y)
      centralPhysical volume ∧
    (∫ y in centralPhysical,centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y)=
      inner ℝ f g := by
  have hi := (Lp.memLp (centralPhysicalWholeCLM f)).integrable_mul
    (Lp.memLp (centralPhysicalWholeCLM g))
  refine ⟨hi.integrableOn,?_⟩
  rw [←centralPhysicalWholeLI.inner_map_map f g,L2.inner_def,
    ←integral_indicator centralPhysical_compact.measurableSet]
  apply integral_congr_ae
  filter_upwards [centralPhysicalWholeCLM_ae f,centralPhysicalWholeCLM_ae g] with y hf hg
  change centralPhysical.indicator
    (fun y => centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y) y=
      inner ℝ (centralPhysicalWholeCLM f y) (centralPhysicalWholeCLM g y)
  rw [Real.inner_apply]
  by_cases hy : y∈centralPhysical
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy,hf,hg,indicator_of_notMem hy,indicator_of_notMem hy]; ring

lemma H1JetOn.central_gradient {s : Fin 3 → ℝ} {p : centralEnergySpace s} {w : H1}
    (hw : H1JetOn w centralPhysical (centralFullJetCLM s p.val)) :
    ∀ᵐ y : Fin 3 → ℝ,y∈centralPhysical → originalPiGradient w y=
      (fun i : Fin 3 => centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y) := by
  apply originalPiGradient_eq_on_ball (fun _ => centralPhysical_subset_ball) w _
  filter_upwards [hw,physicalFourJetCLM_ae
    (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p.val))] with x hx he hy
  have h := (hx hy).trans he
  intro i
  exact congrArg (fun v : JetFiber => v i.succ) h

lemma central_physical_energy {s : Fin 3 → ℝ} (p q : centralEnergySpace s) (w v : H1)
    (hw : H1JetOn w centralPhysical (centralFullJetCLM s p.val))
    (hv : H1JetOn v centralPhysical (centralFullJetCLM s q.val)) :
    (∫ y in centralPhysical,originalPiGradient w y ⬝ᵥ originalPiGradient v y)=
      inner ℝ (centralD s p) (centralD s q) := by
  calc
    _ = ∫ y in centralPhysical,∑ i : Fin 3,
        centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y*
          centralPhysicalWholeCLM (centralAmbientComponent s i.succ q.val) y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hw.central_gradient,ae_restrict_of_ae hv.central_gradient,
        ae_restrict_mem centralPhysical_compact.measurableSet] with y hp hq hy
      rw [hp hy,hq hy]
      rfl
    _ = ∑ i : Fin 3,inner ℝ (centralAmbientComponent s i.succ p.val)
        (centralAmbientComponent s i.succ q.val) := by
      rw [integral_finsetSum (f:=fun i : Fin 3 => fun y =>
        centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y*
          centralPhysicalWholeCLM (centralAmbientComponent s i.succ q.val) y) Finset.univ (fun i _ =>
        (centralPhysicalWholeCLM_integral (centralAmbientComponent s i.succ p.val)
          (centralAmbientComponent s i.succ q.val)).1)]
      exact Finset.sum_congr rfl (fun i _ =>
        (centralPhysicalWholeCLM_integral (centralAmbientComponent s i.succ p.val)
          (centralAmbientComponent s i.succ q.val)).2)
    _ = _ := by rw [PiLp.inner_apply]; rfl

end ScalarConductivity

end
end

end OAI
