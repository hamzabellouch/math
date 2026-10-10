import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalOpenBlock
import OAI.Analysis.Conductivity.Flux.AttachedPhysicalSmoothGreen

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix UnitAddTorus

lemma smoothCollarTrace_eq_zero (s : Fin 3 → ℝ) (t : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hz : ∀ θ : UnitAddTorus (Fin 2),φ (sourceAngularCollar t θ)=0) :
    smoothCollarTrace s t hφ=0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  ext h
  rw [smoothCollarTrace_fst]
  simp [hz,Complex.ofReal_zero,mFourierCoeff]

lemma physicalSmoothOuterTrace_compact_zero (s : Fin 3 → ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hφs : tsupport φ⊆(WithLp.toLp 2) ⁻¹' sourceOpenBlock) (i : Fin 3) :
    physicalSmoothOuterTrace s hφ i=0 := by
  revert i
  refine Fin.cases ?_ (fun k => ?_)
  · apply smoothCollarTrace_eq_zero
    intro θ
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := (sourceOpenBlock_time_iff _).mp (hφs h)
    rw [sourceAngular_time (by norm_num)] at hb
    exact (lt_irrefl 0) hb.1
  · apply smoothCollarTrace_eq_zero
    intro θ
    change φ (sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ))=0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := ((sourceOpenBlock_time_iff _).mp (hφs h)).2 k
    have he : (sourceChildHomeomorph (actualChildSign k)).symm
        (sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ))=
        sourceAngularCollar 0 θ :=
      (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply _
    rw [he,sourceAngular_time (by norm_num)] at hb
    exact (lt_irrefl 0) hb

lemma cylinderTerminalFlux_zero_test (s : Fin 3 → ℝ) (κ R : ℝ)
    (p : spectralTraceGraph (torusRate s)) : cylinderTerminalFlux s κ R p 0=0 := by
  simp [cylinderTerminalFlux]

theorem physical_attached_weak_exists (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (hκ : ∑ i,κ i=0) :
    ∃ (p : centralEnergySpace s) (w : H1),w∈H10 ∧ centralM s p=0 ∧
      H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
      (∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i)) ∧
      ∀ (φ : (Fin 3 → ℝ) → ℝ), ContDiff ℝ (↑(⊤:ℕ∞)) φ →
        tsupport φ⊆(WithLp.toLp 2) ⁻¹' sourceOpenBlock →
        (∫ y in (WithLp.toLp 2) ⁻¹' sourceOpenBlock,originalPiGradient w y ⬝ᵥ
          (physicalBlockTensor s a y*ᵥphysicalTestCovector φ y))=0 := by
  obtain ⟨p,w,hw0,hpm,hwc,hwe,hg⟩ := physical_attached_smooth_green_exists s a κ hs ha₀ ha hκ
  refine ⟨p,w,hw0,hpm,hwc,hwe,?_⟩
  intro φ hφ hφs
  have he := hg φ hφ
  simp only [physicalSmoothOuterTrace_compact_zero s hφ hφs,
    cylinderTerminalFlux_zero_test,Finset.sum_const_zero,mul_zero] at he
  rw [←physicalBlockRegion_openBlock_restrict]
  refine (integral_congr_ae ?_).trans he
  filter_upwards [ae_restrict_of_ae (piSmoothH1_gradient hφ
    (fun _ => physicalBlockRegion_subset_ball)),ae_restrict_mem physicalBlockRegion_compact.measurableSet]
    with y hy hm
  rw [hy hm]

end ScalarConductivity

end

end OAI
