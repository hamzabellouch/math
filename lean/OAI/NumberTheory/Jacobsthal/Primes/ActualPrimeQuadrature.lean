import Mathlib
import OAI.NumberTheory.Jacobsthal.Analysis.HarmonicReferenceMeasure
import OAI.NumberTheory.Jacobsthal.Analysis.LipschitzMeasureQuadrature

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HarmonicPrimeAtomicMeasure

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def primeAtom (w : ℝ) (p : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((p:ℝ)⁻¹) • Measure.dirac (primeExponent w p)

noncomputable def primeMeasure (w V : ℝ) : Measure ℝ :=
  ∑ p ∈ Nat.primesLE ⌊w^V⌋₊,primeAtom w p

instance primeAtom_finite (w : ℝ) (p : ℕ) : IsFiniteMeasure (primeAtom w p) := by
  constructor
  simp [primeAtom,Measure.smul_apply]

instance primeMeasure_finite (w V : ℝ) : IsFiniteMeasure (primeMeasure w V) := by
  unfold primeMeasure
  infer_instance

theorem integrable_primeAtom (w : ℝ) (p : ℕ) (F : ℝ → ℝ) : Integrable F (primeAtom w p) := by
  unfold primeAtom
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem primeMeasure_integral (w V : ℝ) (F : ℝ → ℝ) :
    (∫ x,F x ∂primeMeasure w V)=∑ p ∈ Nat.primesLE ⌊w^V⌋₊,(p:ℝ)⁻¹*F (primeExponent w p) := by
  unfold primeMeasure
  rw [integral_finsetSum_measure (fun p _ => integrable_primeAtom w p F)]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [primeAtom,integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem primeMeasure_setIntegral (w V : ℝ) (F : ℝ → ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫ x in J,F x ∂primeMeasure w V)=
      ∑ p ∈ Nat.primesLE ⌊w^V⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F (primeExponent w p) else 0 := by
  rw [← integral_indicator hJ,primeMeasure_integral]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hp : primeExponent w p ∈ J <;> simp [hp]

theorem primeMeasure_real (w V : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    (primeMeasure w V).real J=
      ∑ p ∈ Nat.primesLE ⌊w^V⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹ else 0 := by
  have h := primeMeasure_setIntegral w V (fun _ => (1:ℝ)) hJ
  simpa only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_one] using h

theorem intervalGuard_measurable (lc rc : Bool) (a b : ℝ) :
    MeasurableSet {x | intervalGuard lc rc a b x} := by
  cases lc <;> cases rc <;> simp only [intervalGuard,ite_true,Bool.false_eq_true,ite_false] <;> measurability

theorem primeMeasure_interval {w a b V : ℝ} (hw : 1 < w) (hbV : b ≤ V) (lc rc : Bool) :
    (primeMeasure w V).real {x | intervalGuard lc rc a b x}=harmonicMass w lc rc a b := by
  rw [primeMeasure_real w V (intervalGuard_measurable lc rc a b),harmonicMass]
  have hw0 : 0 < w := by linarith
  have hpow : w^b ≤ w^V := Real.rpow_le_rpow_of_exponent_le hw.le hbV
  have hsub : Nat.primesLE ⌊w^b⌋₊ ⊆ Nat.primesLE ⌊w^V⌋₊ := by
    intro p hp
    obtain ⟨hpB,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpB.trans (Nat.floor_mono hpow),hprime⟩
  symm
  apply Finset.sum_subset hsub
  intro p hpV hpB
  have hprime := (Nat.mem_primesLE.mp hpV).2
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
  have hnot : ¬intervalGuard lc rc a b (primeExponent w p) := by
    intro hguard
    have hxp : primeExponent w p ≤ b := by
      have hh := hguard.2
      cases rc with
      | false => exact hh.le
      | true => exact hh
    have hpx := (exponent_le_iff hw hp0).mp hxp
    exact hpB (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos hw0 b).le).mpr hpx,hprime⟩)
  exact ite_eq_right hnot

end NumberTheoryLean.HarmonicPrimeAtomicMeasure

end

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open ErdosMonotoneQuadrature ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure

noncomputable def boundaryPrimeError (c C w : ℝ) : ℝ := C*Real.exp (-c*Real.sqrt (Real.log w))

theorem boundaryPrimeError_tendsto_zero {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (boundaryPrimeError c C) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) c hc).const_mul C
  have h' : Tendsto (fun x : ℝ => C*Real.exp (-c*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero,one_mul,mul_zero] using h
  exact h'.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

theorem boundary_interval_discrepancy : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc 1 2 →
      |(primeMeasure w 2).real J-(referenceMeasure 1 2).real J| ≤ boundaryPrimeError c C w := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw J hJ hsub
  have hw1 : 1 < w := hw₀.trans_le hw
  apply orderConnected_measure_discrepancy (primeMeasure w 2) (referenceMeasure 1 2) 1 2
    (boundaryPrimeError c C w) (by unfold boundaryPrimeError; positivity) _ hJ hsub
  intro a b ha hab hb
  have hall (lc rc : Bool) :
      |(primeMeasure w 2).real {x | intervalGuard lc rc a b x}-
        (referenceMeasure 1 2).real {x | intervalGuard lc rc a b x}| ≤ boundaryPrimeError c C w := by
    rw [primeMeasure_interval hw1 hb,referenceMeasure_interval (by norm_num : (0:ℝ)<1) ha hab hb]
    have hh := h w hw a b (by linarith) hab lc rc
    have hs : Real.sqrt (Real.log w) ≤ Real.sqrt (a*Real.log w) := by
      apply Real.sqrt_le_sqrt
      have hlog := (Real.log_pos hw1).le
      nlinarith
    have he : Real.exp (-c*Real.sqrt (a*Real.log w)) ≤ Real.exp (-c*Real.sqrt (Real.log w)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact hh.trans (mul_le_mul_of_nonneg_left he hC.le)
  exact ⟨hall true true,hall true false,hall false true,hall false false⟩

theorem reference_unit_interval_mass : (referenceMeasure 1 2).real (Icc 1 2)=Real.log 2 := by
  have h := referenceMeasure_interval (u:=1) (v:=2) (a:=1) (b:=2)
    (by norm_num) le_rfl (by norm_num) le_rfl true true
  simpa only [intervalGuard,ite_true,Real.log_one,sub_zero] using! h

theorem boundary_measure_control : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w →
      (primeMeasure w 2).real (Icc 1 2) ≤ 1 ∧
      ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc 1 2 →
        |(primeMeasure w 2).real J-(referenceMeasure 1 2).real J| ≤ boundaryPrimeError c C w := by
  obtain ⟨c,C,wH,hc,hC,hwH,h⟩ := boundary_interval_discrepancy
  have hlog : Real.log 2 < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
    norm_num at hh
    exact hh
  have he := (boundaryPrimeError_tendsto_zero hc C).eventually
    (Iio_mem_nhds (by linarith : (0:ℝ)<1-Real.log 2))
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp he
  refine ⟨c,C,max wH wE,hc,hC,hwH.trans_le (le_max_left _ _),?_⟩
  intro w hw
  have hwh : wH ≤ w := (le_max_left _ _).trans hw
  have hwe := hwE w ((le_max_right _ _).trans hw)
  refine ⟨?_,h w hwh⟩
  have hm := h w hwh (Icc 1 2) ordConnected_Icc (subset_refl _)
  rw [reference_unit_interval_mass] at hm
  have hmass := (abs_le.mp hm).2
  change boundaryPrimeError c C w < 1-Real.log 2 at hwe
  linarith

end ErdosContinuousBoundary

end

section

namespace NumberTheoryLean.ActualPrimeQuadrature

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open ErdosMonotoneQuadrature ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints
open HarmonicPrimeAtomicMeasure HarmonicReferenceMeasure

theorem actual_interval_discrepancy : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ u v : ℝ,2 ≤ u → u ≤ v → ∀ a b : ℝ,u ≤ a → a ≤ b → b ≤ v →
      ∀ lc rc : Bool,
        |(primeMeasure w v).real {x | intervalGuard lc rc a b x}-
          (referenceMeasure u v).real {x | intervalGuard lc rc a b x}| ≤
          C*Real.exp (-c*Real.sqrt (u*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw u v hu _huv a b hua hab hbv lc rc
  have hw1 : 1 < w := hw₀.trans_le hw
  have hu0 : 0 < u := by linarith
  rw [primeMeasure_interval hw1 hbv,referenceMeasure_interval hu0 hua hab hbv]
  have hh := h w hw a b (by linarith) hab lc rc
  have hm : Real.exp (-c*Real.sqrt (a*Real.log w)) ≤ Real.exp (-c*Real.sqrt (u*Real.log w)) := by
    apply Real.exp_le_exp.mpr
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hua (Real.log_pos hw1).le)
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left hm hC.le)

theorem actual_weighted_prime_quadrature : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ u v : ℝ,2 ≤ u → u ≤ v → ∀ D : ℝ,0 ≤ D → ∀ g : ℝ → ℝ,
      (MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v)) →
      (∀ x ∈ Icc u v,|g x| ≤ D) → ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc u v →
        |(∑ p ∈ Nat.primesLE ⌊w^v⌋₊,if primeExponent w p ∈ J then
            (p:ℝ)⁻¹*g (primeExponent w p)/primeExponent w p else 0)-
          ∫ x in J,g x/x^2| ≤ (C*D/u)*Real.exp (-c*Real.sqrt (u*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := actual_interval_discrepancy
  refine ⟨c,3*C,w₀,hc,by positivity,hw₀,?_⟩
  intro w hw u v hu huv D hD g hg hbound J hJ hsub
  have hu0 : 0 < u := by linarith
  let := referenceMeasure_finite (v:=v) hu0
  let E := C*Real.exp (-c*Real.sqrt (u*Real.log w))
  have hinter : ∀ a b : ℝ,u ≤ a → a ≤ b → b ≤ v →
      |(primeMeasure w v).real (Icc a b)-(referenceMeasure u v).real (Icc a b)| ≤ E ∧
      |(primeMeasure w v).real (Ico a b)-(referenceMeasure u v).real (Ico a b)| ≤ E ∧
      |(primeMeasure w v).real (Ioc a b)-(referenceMeasure u v).real (Ioc a b)| ≤ E ∧
      |(primeMeasure w v).real (Ioo a b)-(referenceMeasure u v).real (Ioo a b)| ≤ E := by
    intro a b hua hab hbv
    have hh := h w hw u v hu huv a b hua hab hbv
    exact ⟨hh true true,hh true false,hh false true,hh false false⟩
  have hq := weighted_from_all_endpoint_intervals (primeMeasure w v) (referenceMeasure u v)
    u v D E hu0 hD (by dsimp [E]; positivity) g hg hbound hinter hJ hsub
  rw [primeMeasure_setIntegral w v _ hJ.measurableSet,
    referenceMeasure_weightedIntegral hu0 g hJ.measurableSet hsub] at hq
  calc
    _ ≤ 3*E*D/u := by simpa only [mul_div_assoc] using hq
    _ = _ := by dsimp [E]; ring

end NumberTheoryLean.ActualPrimeQuadrature

end

end Erdos970

end OAI
