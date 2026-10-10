import Mathlib
import OAI.Analysis.Conductivity.Variational.WeakHarmonicClassical
import OAI.Analysis.Conductivity.Variational.CentralEuclideanBridge

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralBasisSlopes (j : Fin 2) : Fin 3 → ℝ :=
  ![![-1,1,0],![-1,0,1]] j

lemma centralBasisSlopes_sum (j : Fin 2) : ∑ i,centralBasisSlopes j i=0 := by
  fin_cases j <;> norm_num [centralBasisSlopes,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]

theorem central_pair_regular_exists (s : Fin 3 → ℝ) :
    ∃ p : Fin 2 → centralEnergySpace s,
      (∀ j,centralM s (p j)=0) ∧
      (∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)) ∧
      (∀ j,WeaklyHarmonicOn (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion) ∧
      ∀ (a : R3) (R : ℝ),0<R → Metric.closedBall a R⊆centralHarmonicRegion →
        (∀ j,AnalyticOnNhd ℝ
          (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) (Metric.ball a (R/4)) ∧
          (centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
            =ᵐ[volume.restrict (Metric.ball a (R/4))]
            radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) ∧
        ∀ᵐ x∂volume,x∈Metric.ball a (R/4) → ∃ r>0,
          Metric.ball x r⊆Metric.ball a (R/4) ∧
          HarmonicPairRegularOn
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 0).val)) (R/4))
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 1).val)) (R/4))
            (Metric.ball x r) := by
  classical
  have hp (j : Fin 2) := central_variational_euclidean_weak s (centralBasisSlopes j)
    (centralBasisSlopes_sum j)
  choose p hm hv hw using hp
  refine ⟨p,hm,hv,hw,?_⟩
  intro a R hR hball
  exact ⟨fun j => weakWeyl_analytic_local (hw j) hR hball,
    weakWeyl_pair_ae_regular (hw 0) (hw 1) hR hball⟩

end ScalarConductivity

end
end

end OAI
