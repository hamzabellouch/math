import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPieceRegular
import OAI.Analysis.Conductivity.Flux.PhysicalAttachedGreen

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

theorem physical_central_regular_pair_exists (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) :
    ∃ (p : Fin 2 → centralEnergySpace s) (w : Fin 2 → H1),
      (∀ j,w j∈H10 ∧ centralM s (p j)=0 ∧
        CentralVariationalEquation s (centralBasisSlopes j) (p j) ∧
        H1JetOn (w j) centralPhysical (centralFullJetCLM s (p j).val) ∧
        (∀ i : Fin 3,H1JetOn (w j) (physicalEndRegion i)
          (attachedPhysicalJet s a (centralBasisSlopes j) (p j) i)) ∧
        ∀ v : H1,
          (∫ y in physicalBlockRegion,originalPiGradient (w j) y ⬝ᵥ
            (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
            physicalTerminalFluxCLM s a (centralBasisSlopes j)
              (fun i => Fin.cases ha₀.ne (fun k => (ha k).ne') i)
              (fun i => centralT s i (p j)) v) ∧
      (∀ j,WeaklyHarmonicOn (centralWholeL2
        (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion) ∧
      ∀ (b : R3) (R : ℝ),0<R → Metric.closedBall b R⊆centralHarmonicRegion →
        (∀ j,AnalyticOnNhd ℝ
          (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4))
            (Metric.ball b (R/4)) ∧
          (centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
            =ᵐ[volume.restrict (Metric.ball b (R/4))]
            radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) ∧
        ∀ᵐ x∂volume,x∈Metric.ball b (R/4) → ∃ r>0,
          Metric.ball x r⊆Metric.ball b (R/4) ∧
          HarmonicPairRegularOn
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 0).val)) (R/4))
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 1).val)) (R/4))
            (Metric.ball x r) := by
  obtain ⟨p,hm,hvar,hweak,hreg⟩ := central_pair_regular_exists s
  have hatt (j : Fin 2) := complete_physical_attachment s hs a (centralBasisSlopes j) ha₀ ha (p j)
  choose w hw0 hwc hwe using hatt
  refine ⟨p,w,?_,hweak,hreg⟩
  intro j
  refine ⟨hw0 j,hm j,hvar j,hwc j,hwe j,?_⟩
  exact physical_block_green_extension s a (centralBasisSlopes j) hs
    (fun i => Fin.cases ha₀.ne (fun k => (ha k).ne') i)
    (fun i => centralT s i (p j)) (w j)
    (fun _ hφ => attached_block_smooth_green s a (centralBasisSlopes j) hs ha₀ ha
      (p j) (hvar j) (w j) (hwc j) (hwe j) hφ)

theorem physical_central_regular_jets_pair_exists (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) :
    ∃ (p : Fin 2 → centralEnergySpace s) (w : Fin 2 → H1),
      (∀ j,w j∈H10 ∧ centralM s (p j)=0 ∧
        CentralVariationalEquation s (centralBasisSlopes j) (p j) ∧
        H1JetOn (w j) centralPhysical (centralFullJetCLM s (p j).val) ∧
        (∀ i : Fin 3,H1JetOn (w j) (physicalEndRegion i)
          (attachedPhysicalJet s a (centralBasisSlopes j) (p j) i)) ∧
        ∀ v : H1,
          (∫ y in physicalBlockRegion,originalPiGradient (w j) y ⬝ᵥ
            (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
            physicalTerminalFluxCLM s a (centralBasisSlopes j)
              (fun i => Fin.cases ha₀.ne (fun k => (ha k).ne') i)
              (fun i => centralT s i (p j)) v) ∧
      ∀ (b : R3) (R : ℝ),0<R → Metric.closedBall b R⊆centralHarmonicRegion →
        ∃ g : Fin 2 → R3 → ℝ,
          (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (g j) ∧
            AnalyticOnNhd ℝ (g j) (Metric.ball b (R/4))) ∧
          (∀ j,(centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
              =ᵐ[volume.restrict (Metric.ball b (R/4))] g j) ∧
          (∀ j (i : Fin 3),∀ᵐ x∂volume,x∈Metric.ball b (R/4) →
            centralWholeL2 (centralAmbientComponent s i.succ (p j).val) x=
              fderiv ℝ (g j) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) ∧
          ∀ᵐ x∂volume,x∈Metric.ball b (R/4) → ∃ r>0,
            Metric.ball x r⊆Metric.ball b (R/4) ∧
            HarmonicPairRegularOn (g 0) (g 1) (Metric.ball x r) := by
  obtain ⟨p,hm,hvar,hreg⟩ := central_piece_regular s
  have hatt (j : Fin 2) := complete_physical_attachment s hs a (centralBasisSlopes j) ha₀ ha (p j)
  choose w hw0 hwc hwe using hatt
  refine ⟨p,w,?_,hreg⟩
  intro j
  refine ⟨hw0 j,hm j,hvar j,hwc j,hwe j,?_⟩
  exact physical_block_green_extension s a (centralBasisSlopes j) hs
    (fun i => Fin.cases ha₀.ne (fun k => (ha k).ne') i)
    (fun i => centralT s i (p j)) (w j)
    (fun _ hφ => attached_block_smooth_green s a (centralBasisSlopes j) hs ha₀ ha
      (p j) (hvar j) (w j) (hwc j) (hwe j) hφ)

end ScalarConductivity

end
end

end OAI
