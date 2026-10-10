import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import OAI.NumberTheory.Jacobsthal.Harmonic.CompactAnomalyTest
import OAI.NumberTheory.Jacobsthal.Renewal.OccupationDensityIntegral

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.OccupationDensityIntegral NumberTheoryLean.CompactTestMeasurable
open NumberTheoryLean.ActualCouplingUpdates

noncomputable def fullAnomalyTest (i : Side) (x : ℝ×ℝ) : ℝ := extendedSignedAnomaly i x.1

theorem fullAnomalyTest_continuous (i : Side) : Continuous (fullAnomalyTest i) :=
  (extendedSignedAnomaly_continuous i).comp continuous_fst

theorem rawTest_measurable {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i, Continuous (H i)) :
    Measurable (rawTest H) := by
  have hp : Measurable (fun x : ℝ×State => (Real.exp x.1,stateRatio x.2)) :=
    (Real.measurable_exp.comp measurable_fst).prodMk (stateRatio_measurable.comp measurable_snd)
  have hs : MeasurableSet {x : ℝ×State | stateSide x.2=.even} :=
    measurable_snd (side_set_measurable .even)
  have he : rawTest H = fun x => if stateSide x.2=.even then H .even (Real.exp x.1,stateRatio x.2)
      else H .odd (Real.exp x.1,stateRatio x.2) := by
    funext x
    rcases x with ⟨u,s⟩
    cases s <;> rfl
  rw [he]
  exact Measurable.ite hs ((hH .even).measurable.comp hp) ((hH .odd).measurable.comp hp)

theorem full_anomaly_exponential :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧ ∀ i r,|extendedSignedAnomaly i r| ≤ C*Real.exp (-c*r) := by
  obtain ⟨C,c,_w,hC,hc,_hw,_hd,ha⟩ := common_anomaly_exponential
  refine ⟨C,c,hC,hc,?_⟩
  intro i r
  have hsign : |sideSign i|=1 := by cases i <;> norm_num [sideSign]
  rw [extendedSignedAnomaly,abs_mul,hsign,one_mul]
  apply (ha (max 2 r) (le_max_left _ _) i).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith [le_max_right (2:ℝ) r]

theorem exp_gap_moment_integrable (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => (Real.exp u)^(n+1)*Real.exp (-c*Real.exp u)) := by
  have hg : IntegrableOn (fun r : ℝ => r^n*Real.exp (-c*r)) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
    simpa only [Real.rpow_natCast,Real.rpow_one] using! hh
  have hd : ∀ u ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp u) univ u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have him : Real.exp '' (univ : Set ℝ)=Ioi 0 := by rw [image_univ,Real.range_exp]
  have hh := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd
    Real.exp_injective.injOn (fun r : ℝ => r^n*Real.exp (-c*r))).mp (by rwa [him])
  have hh' : Integrable (fun u : ℝ => Real.exp u*((Real.exp u)^n*Real.exp (-c*Real.exp u))) := by
    simpa only [abs_of_pos (Real.exp_pos _),smul_eq_mul,integrableOn_univ] using! hh
  simpa only [pow_succ',mul_assoc] using! hh'

end ErdosCorrectionLimit

end

end Erdos970

end OAI
