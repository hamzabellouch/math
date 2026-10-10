import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPairRegularity
import OAI.Analysis.Conductivity.Variational.CentralEuclideanJets

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem central_piece_regular (s : Fin 3 → ℝ) :
    ∃ p : Fin 2 → centralEnergySpace s,
      (∀ j,centralM s (p j)=0) ∧
      (∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)) ∧
      ∀ (a : R3) (R : ℝ),0<R → Metric.closedBall a R⊆centralHarmonicRegion →
        ∃ g : Fin 2 → R3 → ℝ,
          (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (g j) ∧
            AnalyticOnNhd ℝ (g j) (Metric.ball a (R/4))) ∧
          (∀ j,(centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
              =ᵐ[volume.restrict (Metric.ball a (R/4))] g j) ∧
          (∀ j (i : Fin 3),∀ᵐ x∂volume,x∈Metric.ball a (R/4) →
            centralWholeL2 (centralAmbientComponent s i.succ (p j).val) x=
              fderiv ℝ (g j) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) ∧
          ∀ᵐ x∂volume,x∈Metric.ball a (R/4) → ∃ r>0,
            Metric.ball x r⊆Metric.ball a (R/4) ∧ HarmonicPairRegularOn (g 0) (g 1) (Metric.ball x r) := by
  obtain ⟨p,hm,hv,hw,hreg⟩ := central_pair_regular_exists s
  refine ⟨p,hm,hv,?_⟩
  intro a R hR hball
  obtain ⟨ha,hr⟩ := hreg a R hR hball
  let g : Fin 2 → R3 → ℝ := fun j => radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)
  have hgs (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (g j) := (weakWeyl_local (hw j) hR hball).1
  have hU : Metric.ball a (R/4)⊆centralEuclideanCLE ⁻¹' centralClosed := by
    intro x hx
    exact (hball (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith : R/4≤R) hx))).1
  exact ⟨g,fun j => ⟨hgs j,(ha j).1⟩,fun j => (ha j).2,
    fun j => central_smooth_representative_jets s (p j) Metric.isOpen_ball hU (g j) (hgs j) (ha j).2,hr⟩

end ScalarConductivity

end
end

end OAI
