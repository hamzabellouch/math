import OAI.NumberTheory.Jacobsthal.Estimates.BoundaryGateSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem boundary_prime_step_control : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → (primeMeasure w 2).real (Icc 1 2) ≤ 1 ∧
      ∀ (n : ℕ) (i : Side) (r b : ℝ) (closed : Bool),
        |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then
          (p:ℝ)⁻¹*boundaryTerm n i.flip (r-primeExponent w p) (primeExponent w p) else 0)-
          boundaryTerm (n+1) i r b| ≤ (12*(n:ℝ)+15)*boundaryPrimeError c C w := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := boundary_measure_control
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw
  obtain ⟨hmass,hdiscr⟩ := h w hw
  refine ⟨hmass,?_⟩
  intro n i r b closed
  have hJ := boundaryGateSet_orderConnected i r b closed
  have hsub := boundaryGateSet_subset i r b closed
  let := referenceMeasure_finite (u:=1) (v:=2) (by norm_num)
  have hq := lipschitz_measure_discrepancy (primeMeasure w 2) (referenceMeasure 1 2)
    (fun x => boundaryTerm n i.flip (r-x) x) ((n:NNReal)+1) 1 (boundaryPrimeError c C w)
    (by norm_num) (boundaryTerm_child_lipschitz n i.flip r).lipschitzOnWith
    (fun x _ => boundaryTerm_abs_le_one n i.flip (r-x) x) hdiscr hJ hsub
  rw [primeMeasure_setIntegral w 2 _ hJ.measurableSet,boundaryTerm_gate_integral] at hq
  simp only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hq
  calc
    _ ≤ 3*boundaryPrimeError c C w*(1+4*((n:ℝ)+1)) := hq
    _ = _ := by ring

end ErdosContinuousBoundary

end

end Erdos970

end OAI
