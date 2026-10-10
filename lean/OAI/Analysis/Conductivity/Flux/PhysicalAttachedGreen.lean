import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalOuterTrace
import OAI.Analysis.Conductivity.Fourier.SpectralTerminalL2
import OAI.Analysis.Conductivity.Variational.PhysicalEnergyContinuous

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma physicalEndLength_pos (a : Fin 3 → ℝ) (ha : ∀ i,a i≠0) (i : Fin 3) :
    0<physicalEndLength a i :=
  mul_pos (abs_pos.mpr (ha i)) (by norm_num [centralThickness])

def physicalTerminalFluxCLM (s a κ : Fin 3 → ℝ) (ha : ∀ i,a i≠0)
    (f : Fin 3 → spectralTraceGraph (torusRate s)) : H1 →L[ℝ] ℝ :=
  angularArea • ∑ i : Fin 3,
    (terminalFluxL2CLM s (κ i) (physicalEndLength_pos a ha i) (f i)).comp (physicalOuterTraceCLM i)

lemma physicalTerminalFlux_smooth (s a κ : Fin 3 → ℝ) (ha : ∀ i,a i≠0)
    (f : Fin 3 → spectralTraceGraph (torusRate s))
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    physicalTerminalFluxCLM s a κ ha f (piSmoothH1 hφ)=
      angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
        (f i) (physicalSmoothOuterTrace s hφ i) := by
  simp only [physicalTerminalFluxCLM,_root_.smul_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalOuterTrace_smooth i hφ s,terminalFluxL2CLM_trace]

lemma physical_block_green_extension (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (f : Fin 3 → spectralTraceGraph (torusRate s)) (w : H1)
    (hw : ∀ (φ : (Fin 3 → ℝ) → ℝ) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ),
      (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
        (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
        angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
          (f i) (physicalSmoothOuterTrace s hφ i)) (v : H1) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
      physicalTerminalFluxCLM s a κ ha f v := by
  refine smoothPiH1L_dense.induction_on v ?_ ?_
  · exact isClosed_eq (physicalBlockEnergy_continuous s a hs ha w)
      (physicalTerminalFluxCLM s a κ ha f).continuous
  intro φ
  change (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
    (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 (smoothScalar_contDiff φ)) y))=
      physicalTerminalFluxCLM s a κ ha f (piSmoothH1 (smoothScalar_contDiff φ))
  rw [hw φ.val (smoothScalar_contDiff φ),physicalTerminalFlux_smooth]

theorem physical_attached_green_exists (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (hκ : ∑ i,κ i=0) :
    ∃ (p : centralEnergySpace s) (w : H1),w∈H10 ∧ centralM s p=0 ∧
      H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
      (∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i)) ∧
      ∀ v : H1,
        (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
          (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
          physicalTerminalFluxCLM s a κ (fun i => Fin.cases ha₀.ne (fun k => (ha k).ne') i)
            (fun i => centralT s i p) v := by
  obtain ⟨p,w,hw0,hpm,hwc,hwe,hg⟩ := physical_attached_smooth_green_exists s a κ hs ha₀ ha hκ
  exact ⟨p,w,hw0,hpm,hwc,hwe,fun v => physical_block_green_extension s a κ hs
    (fun i => Fin.cases ha₀.ne (fun k => (ha k).ne') i) (fun i => centralT s i p) w hg v⟩

end ScalarConductivity

end
end

end OAI
