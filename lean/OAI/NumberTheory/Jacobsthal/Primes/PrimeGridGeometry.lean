import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Kernel.Composition.Comp
import OAI.NumberTheory.Jacobsthal.Estimates.FiniteMonotoneComparison
import OAI.NumberTheory.Jacobsthal.Estimates.LowStateHorizon
import OAI.NumberTheory.Jacobsthal.Primes.PrimeRatioBins
import OAI.NumberTheory.Jacobsthal.Sieve.AdmittedExponentMarginal

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeTiltMonotone

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltBounds DerivativeWeights TransitionKernels
open HarmonicExponentMeasure

theorem multiplier_measurable (i : Side) (s : ℝ) : Measurable (multiplier i s) := by
  have hw : Measurable (weight i.flip) := by
    cases i with
    | even => exact phiOdd_continuous.measurable
    | odd => exact phiEven_measurable
  exact ((((measurable_id.add_const 1).div measurable_id).pow_const 2).mul hw).div_const (weight i s)

theorem minRatio_pos {i : Side} {s : ℝ} (hs : Valid i s) : 0 < minRatio i s :=
  valid_pos (valid_next hs le_rfl)

theorem multiplier_antitone {i : Side} {s : ℝ} (hs : Valid i s) :
    AntitoneOn (multiplier i s) (Ici (minRatio i s)) := by
  intro u hu v hv huv
  have hu0 := valid_pos (valid_next hs hu)
  have hv0 := valid_pos (valid_next hs hv)
  have hphi : weight i.flip v ≤ weight i.flip u := by
    cases i with
    | even => exact phiOdd_antitone huv
    | odd =>
      have h2 : 2 ≤ minRatio .odd s := le_max_left _ _
      apply phiEven_strictAntiOn.antitoneOn
      · change 1 < u
        change minRatio .odd s ≤ u at hu
        linarith
      · change 1 < v
        change minRatio .odd s ≤ v at hv
        linarith
      · exact huv
  have hq : (v+1)/v ≤ (u+1)/u := by
    have h := one_div_le_one_div_of_le hu0 huv
    have heU : (u+1)/u = 1+1/u := by field_simp
    have heV : (v+1)/v = 1+1/v := by field_simp
    rw [heU,heV]
    linarith
  have hqU : 0 ≤ (u+1)/u := (div_pos (by linarith) hu0).le
  have hqV : 0 ≤ (v+1)/v := (div_pos (by linarith) hv0).le
  have hsq : ((v+1)/v)^2 ≤ ((u+1)/u)^2 := by nlinarith
  unfold multiplier
  apply div_le_div_of_nonneg_right _ (weight_pos hs).le
  exact mul_le_mul hsq hphi (weight_pos (valid_next hs hv)).le (sq_nonneg _)

theorem ratioMeasure_ae_above (a : ℝ) : ∀ᵐ t ∂ratioMeasure a, a ≤ t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ici)

theorem multiplier_nonnegative_ae {i : Side} {s : ℝ} (hs : Valid i s) :
    0 ≤ᵐ[ratioMeasure (minRatio i s)] multiplier i s :=
  (ratioMeasure_ae_above _).mono (fun _ ht => (multiplier_pos hs (valid_next hs ht)).le)

theorem weighted_ratio_density_eq {i : Side} {s : ℝ} (hs : Valid i s) (t : ℝ) :
    (Ici (minRatio i s)).indicator (fun t => ENNReal.ofReal (1/(t+1)) * ENNReal.ofReal (multiplier i s t)) t =
      ENNReal.ofReal (transitionDensity i s t) := by
  classical
  by_cases ht : minRatio i s ≤ t
  · have ht0 := valid_pos (valid_next hs ht)
    rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(t+1)), transitionDensity, tailDensity,
      indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
    congr 1
    unfold multiplier W
    field_simp
  · rw [indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht), transitionDensity, tailDensity,
      indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht), ENNReal.ofReal_zero]

theorem transitionDensity_mass {i : Side} {s : ℝ} (hs : Valid i s) :
    (∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity i s t)) = 1 := by
  cases i with
  | even =>
    let x : EvenState := ⟨s,hs⟩
    have h := evenKernel_apply x univ
    simp only [setLIntegral_univ, measure_univ] at h
    exact h.symm
  | odd =>
    let x : OddState := ⟨s,hs⟩
    have h := oddKernel_apply x univ
    simp only [setLIntegral_univ, measure_univ] at h
    exact h.symm

theorem multiplier_ratio_integral {i : Side} {s : ℝ} (hs : Valid i s) :
    (∫⁻ t, ENNReal.ofReal (multiplier i s t) ∂ratioMeasure (minRatio i s)) = 1 := by
  rw [ratioMeasure, lintegral_withDensity_eq_lintegral_mul _ (f := fun t : ℝ => ENNReal.ofReal (1/(t+1)))
    (g := fun t : ℝ => ENNReal.ofReal (multiplier i s t)) (by fun_prop)
    (ENNReal.measurable_ofReal.comp (multiplier_measurable i s)), ← lintegral_indicator measurableSet_Ici]
  calc
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity i s t) := lintegral_congr (fun t => weighted_ratio_density_eq hs t)
    _ = 1 := transitionDensity_mass hs

end NumberTheoryLean.PrimeTiltMonotone



namespace NumberTheoryLean.PrimeRatioMeasure

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioBins HarmonicExponentMeasure

noncomputable def primeAtoms (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) : Finset ℝ := by
  classical
  exact (children w ell S i s r cap closed).image (childRatio w r)

noncomputable def finitePrimeMeasure (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) : Measure ℝ :=
  ∑ p ∈ children w ell S i s r cap closed, ENNReal.ofReal (p : ℝ)⁻¹ • Measure.dirac (childRatio w r p)

theorem finitePrimeMeasure_apply (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool)
    {B : Set ℝ} [DecidablePred (fun x => x ∈ B)] (hB : MeasurableSet B) :
    finitePrimeMeasure w ell S i s r cap closed B =
      ∑ p ∈ children w ell S i s r cap closed, if childRatio w r p ∈ B then ENNReal.ofReal (p : ℝ)⁻¹ else 0 := by
  classical
  simp only [finitePrimeMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hB, Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

theorem finitePrimeMeasure_support (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) :
    ∀ᵐ t ∂finitePrimeMeasure w ell S i s r cap closed, t ∈ primeAtoms w ell S i s r cap closed := by
  classical
  apply ae_iff.mpr
  change finitePrimeMeasure w ell S i s r cap closed ((↑(primeAtoms w ell S i s r cap closed) : Set ℝ)ᶜ) = 0
  rw [finitePrimeMeasure_apply _ _ _ _ _ _ _ _ (Finset.finite_toSet _).measurableSet.compl]
  apply Finset.sum_eq_zero
  intro p hp
  have hm : childRatio w r p ∈ primeAtoms w ell S i s r cap closed := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  simp only [Set.mem_compl_iff, Finset.mem_coe, hm, not_true_eq_false, ite_false]

theorem primeAtoms_above (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) :
    ∀ t ∈ primeAtoms w ell S i s r cap closed, minRatio i s ≤ t := by
  classical
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  exact (Finset.mem_filter.mp hp).2.2.2.1

theorem finitePrimeMeasure_Icc (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (x : ℝ) :
    finitePrimeMeasure w ell S i s r cap closed (Icc (minRatio i s) x) =
      ENNReal.ofReal (∑ p ∈ children w ell S i s r cap closed,
        if childRatio w r p ≤ x then (p : ℝ)⁻¹ else 0) := by
  classical
  rw [finitePrimeMeasure_apply _ _ _ _ _ _ _ _ measurableSet_Icc,
    ENNReal.ofReal_sum_of_nonneg (fun p _ => by split_ifs <;> positivity)]
  apply Finset.sum_congr rfl
  intro p hp
  have ha : minRatio i s ≤ childRatio w r p := (Finset.mem_filter.mp hp).2.2.2.1
  by_cases hx : childRatio w r p ≤ x <;> simp [Set.mem_Icc,ha,hx]

theorem finitePrimeMeasure_tilt (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (hs : Valid i s) :
    (∫⁻ t, ENNReal.ofReal (multiplier i s t) ∂finitePrimeMeasure w ell S i s r cap closed) =
      ENNReal.ofReal (∑ p ∈ children w ell S i s r cap closed, primeTilt w r i s p) := by
  rw [finitePrimeMeasure, lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac' _ (f := fun t => ENNReal.ofReal (multiplier i s t))
    (ENNReal.measurable_ofReal.comp (multiplier_measurable i s))]
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_sum_of_nonneg (fun p hp => primeTilt_nonneg hs hp)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeTilt_eq_multiplier, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg p))]

theorem ratioMeasure_Icc {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    ratioMeasure a (Icc a x) = ENNReal.ofReal (Real.log (x+1)-Real.log (a+1)) := by
  rw [ratioMeasure, withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (show Icc a x ⊆ Ici a from fun _ ht => ht.1)]
  have hi : IntegrableOn (fun t : ℝ => 1/(t+1)) (Icc a x) := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_const.div (continuousOn_id.add continuousOn_const)
    intro t ht
    change t+1 ≠ 0
    linarith [ht.1]
  have hn : ∀ᵐ t ∂volume.restrict (Icc a x), 0 ≤ 1/(t+1) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    exact (one_div_pos.mpr (by linarith [ht.1] : 0 < t+1)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hax,
    intervalIntegral.integral_comp_add_right (f := fun t : ℝ => 1/t) 1,
    integral_one_div_of_pos (by linarith : 0 < a+1) (by linarith : 0 < x+1),
    Real.log_div (by linarith : x+1 ≠ 0) (by linarith : a+1 ≠ 0)]

end NumberTheoryLean.PrimeRatioMeasure



namespace NumberTheoryLean.PrimeCumulativeBound

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltMonotone PrimeRatioBins
open PrimeRatioMeasure HarmonicExponentMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def closedBin (w r a b : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w^(r/(a+1))⌋₊).filter (fun p => a ≤ childRatio w r p ∧ childRatio w r p ≤ b)

noncomputable def closedMass (w r a b : ℝ) : ℝ := ∑ p ∈ closedBin w r a b, (p : ℝ)⁻¹

theorem closed_interval_iff {r a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    (a ≤ r/x-1 ∧ r/x-1 ≤ b) ↔ r/(b+1) ≤ x ∧ x ≤ r/(a+1) := by
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  constructor
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply (div_le_iff₀ hb1).mpr
      have h := (div_le_iff₀ hx).mp (show r/x ≤ b+1 by linarith)
      nlinarith
    · apply (le_div_iff₀ ha1).mpr
      have h := (le_div_iff₀ hx).mp (show a+1 ≤ r/x by linarith)
      nlinarith
  · rintro ⟨hlo,hhi⟩
    constructor
    · have h := (le_div_iff₀ ha1).mp hhi
      have hh : a+1 ≤ r/x := (le_div_iff₀ hx).mpr (by nlinarith)
      linarith
    · have h := (div_le_iff₀ hb1).mp hlo
      have hh : r/x ≤ b+1 := (div_le_iff₀ hx).mpr (by nlinarith)
      linarith

theorem closedMass_eq_harmonic {w r a b : ℝ} (hw : 1 < w) (ha : 0 < a) (hab : a ≤ b) :
    closedMass w r a b = harmonicMass w true true (r/(b+1)) (r/(a+1)) := by
  classical
  unfold closedMass closedBin harmonicMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have h := closed_interval_iff (r := r) ha hab (PrimeRatioBins.primeExponent_pos hw (Nat.mem_primesLE.mp hp).2)
  simp only [childRatio, intervalGuard, ite_true, h]

theorem cumulative_subset_closed {w ell S s r cap b : ℝ} (hw : 1 < w) {i : Side} (hs : Valid i s) (closed : Bool) :
    (children w ell S i s r cap closed).filter (fun p => childRatio w r p ≤ b) ⊆
      closedBin w r (minRatio i s) b := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hchild,hb⟩
  have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hchild).1).2
  have ha : minRatio i s ≤ childRatio w r p := (Finset.mem_filter.mp hchild).2.2.2.1
  have hab : minRatio i s ≤ b := ha.trans hb
  have hinterval := (closed_interval_iff (r := r) (minRatio_pos hs) hab (PrimeRatioBins.primeExponent_pos hw hprime)).mp ⟨ha,hb⟩
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,ha,hb⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hreal : (p : ℝ) ≤ w^(r/(minRatio i s+1)) := (exponent_le_iff hw hp0).mp hinterval.2
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hreal

theorem cumulative_sum_le_closed {w ell S s r cap b : ℝ} (hw : 1 < w) {i : Side} (hs : Valid i s) (closed : Bool) :
    (∑ p ∈ children w ell S i s r cap closed, if childRatio w r p ≤ b then (p : ℝ)⁻¹ else 0) ≤
      closedMass w r (minRatio i s) b := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (cumulative_subset_closed hw hs closed)
    (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem actual_cumulative_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → ∀ x ∈ primeAtoms w ell S i s r cap closed,
        finitePrimeMeasure w ell S i s r cap closed (Icc (minRatio i s) x) ≤
          ratioMeasure (minRatio i s) (Icc (minRatio i s) x) +
            ENNReal.ofReal (C * Real.exp (-c * Real.sqrt ((1/2 : ℝ) * Real.log w))) := by
  classical
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S i s r cap closed hell hr hs x hx
  have hw1 := hw₀.trans_le hw
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  let x := childRatio w r p
  have ha := minRatio_pos hs
  have hax : minRatio i s ≤ x := (Finset.mem_filter.mp hp).2.2.2.1
  have hxp : r/(x+1) = primeExponent w p := nextExponent_childRatio hr (child_exponent_positive (by linarith) hp)
  have hlow : (1/2 : ℝ) ≤ r/(x+1) := by
    rw [hxp]
    have h := (Finset.mem_filter.mp hp).2.1
    linarith
  have hend : r/(x+1) ≤ r/(minRatio i s+1) :=
    div_le_div_of_nonneg_left hr.le (by linarith : 0 < minRatio i s+1) (by linarith)
  have hprime := hbound w hw (r/(x+1)) (r/(minRatio i s+1)) hlow hend true true
  rw [← closedMass_eq_harmonic hw1 ha hax, bin_log_width hr ha hax] at hprime
  have hE : C * Real.exp (-c * Real.sqrt ((r/(x+1))*Real.log w)) ≤
      C * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w)) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlow (Real.log_pos hw1).le)) (by linarith)
  have hraw : (∑ q ∈ children w ell S i s r cap closed, if childRatio w r q ≤ x then (q : ℝ)⁻¹ else 0) ≤
      (Real.log (x+1)-Real.log (minRatio i s+1)) + C * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w)) := by
    have h := cumulative_sum_le_closed (ell := ell) (S := S) (r := r) (cap := cap) (b := x) hw1 hs closed
    have hh := (abs_le.mp hprime).2
    linarith
  change finitePrimeMeasure w ell S i s r cap closed (Icc (minRatio i s) x) ≤ _
  rw [finitePrimeMeasure_Icc, ratioMeasure_Icc ha hax]
  have hmain : 0 ≤ Real.log (x+1)-Real.log (minRatio i s+1) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  rw [← ENNReal.ofReal_add hmain (by positivity)]
  exact ENNReal.ofReal_le_ofReal hraw

end NumberTheoryLean.PrimeCumulativeBound



namespace NumberTheoryLean.PrimeRowMass

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioMeasure PrimeCumulativeBound HarmonicExponentMeasure FiniteMonotoneComparison

theorem retained_row_mass : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → s ≤ S →
      (∑ p ∈ children w ell S i s r cap closed, primeTilt w r i s p) ≤
        1 + C*(1+S)^2 * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hcdf⟩ := actual_cumulative_error
  obtain ⟨D,hD,henv⟩ := multiplier_envelope
  refine ⟨c,C*D,w₀,hc,mul_pos hC hD,hw₀,?_⟩
  intro w hw ell S i s r cap closed hell hr hs hsS
  let μ := finitePrimeMeasure w ell S i s r cap closed
  let ν := ratioMeasure (minRatio i s)
  let A := primeAtoms w ell S i s r cap closed
  let E := C * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hloc : ∀ t ∈ A, minRatio i s ≤ t := primeAtoms_above w ell S i s r cap closed
  have hcomp := finite_monotone_integral_le μ ν A (multiplier i s) (minRatio i s)
    (multiplier i s (minRatio i s)) (ENNReal.ofReal E) (multiplier_measurable i s)
    (finitePrimeMeasure_support w ell S i s r cap closed) hloc
    (fun t ht => (multiplier_pos hs (valid_next hs (hloc t ht))).le)
    (multiplier_nonnegative_ae hs) (multiplier_antitone hs)
    (fun t ht => multiplier_antitone hs (a := minRatio i s) (b := t)
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (hloc t ht)) (hloc t ht))
    (hcdf w hw ell S i s r cap closed hell hr hs)
  rw [finitePrimeMeasure_tilt w ell S i s r cap closed hs, multiplier_ratio_integral hs] at hcomp
  have hM := henv S i s (minRatio i s) hs hsS le_rfl
  have hn : 0 ≤ 1 + (C*D)*(1+S)^2 * Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w)) := by positivity
  apply (ENNReal.ofReal_le_ofReal_iff hn).mp
  calc
    _ ≤ 1 + ENNReal.ofReal E * ENNReal.ofReal (multiplier i s (minRatio i s)) := hcomp
    _ ≤ 1 + ENNReal.ofReal E * ENNReal.ofReal (D*(1+S)^2) :=
      add_le_add le_rfl (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal hM) zero_le zero_le)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hE]
      have hprod : 0 ≤ E*(D*(1+S)^2) := by positivity
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num, ← ENNReal.ofReal_add (by norm_num) hprod]
      congr 1
      dsimp [E]
      ring

end NumberTheoryLean.PrimeRowMass



namespace NumberTheoryLean.PrimeRowNormalization

open _root_.Filter _root_.Set _root_.Finset
open _root_.Erdos970.Filter _root_.Erdos970.Set _root_.Erdos970.Finset
open scoped Topology
open FinitePathGeometry PrimeTiltGeometry PrimeRowMass

 theorem polynomial_absorption {c C : ℝ} (hc : 0 < c) (hC : 0 < C) : ∀ᶠ w : ℝ in atTop,
    ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 →
      C*(1+S)^2 * Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w)) ≤
        Real.exp (-(c/4)*Real.sqrt (Real.log w)) := by
  have hd : 0 < c/4 := by positivity
  have ht : Tendsto (fun x : ℝ => 4*C*x^12 * Real.exp (-(c/4)*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (12 : ℝ) (c/4) hd).const_mul (4*C)
    simpa only [Real.rpow_ofNat, mul_zero, mul_assoc] using h
  have hcomp := ht.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hcomp.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with w hsmall hlog
  intro S hS0 hS
  let L := Real.log w
  let Y := Real.sqrt L
  have hL : 1 ≤ L := hlog
  have hL0 : 0 ≤ L := by linarith
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y^2 = L := Real.sq_sqrt hL0
  have hY12 : Y^12 = L^6 := by
    calc
      _ = (Y^2)^6 := by ring
      _ = _ := by rw [hY2]
  have hL3 : 1 ≤ L^3 := one_le_pow₀ hL
  have hlin : 1+S ≤ 2*L^3 := by change S ≤ L^3 at hS; linarith
  have hpoly : (1+S)^2 ≤ 4*Y^12 := by
    calc
      _ ≤ (2*L^3)^2 := pow_le_pow_left₀ (by linarith) hlin 2
      _ = _ := by rw [hY12]; ring
  have hhalf : Y/2 ≤ Real.sqrt ((1/2 : ℝ)*L) := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ Y/2) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ (1/2 : ℝ)*L)]
    nlinarith [hY2]
  have he : Real.exp (-c*Real.sqrt ((1/2 : ℝ)*L)) ≤ Real.exp (-(c/2)*Y) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf hc.le]
  have hsml : 4*C*Y^12*Real.exp (-(c/4)*Y) ≤ 1 := hsmall.le
  calc
    _ ≤ (4*C*Y^12) * Real.exp (-(c/2)*Y) :=
      mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_left hpoly hC.le]) he (Real.exp_pos _).le (by positivity)
    _ = (4*C*Y^12*Real.exp (-(c/4)*Y)) * Real.exp (-(c/4)*Y) := by
      rw [show -(c/2)*Y = -(c/4)*Y + -(c/4)*Y by ring, Real.exp_add]
      ring
    _ ≤ 1 * Real.exp (-(c/4)*Y) := mul_le_mul_of_nonneg_right hsml (Real.exp_pos _).le
    _ = _ := one_mul _

theorem retained_row_mass_one_add : ∃ c w₀ : ℝ, 0 < c ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 →
    ∀ i : Side, ∀ s r cap : ℝ, ∀ closed : Bool, 1 ≤ ell → 0 < r → Valid i s → s ≤ S →
      (∑ p ∈ children w ell S i s r cap closed, primeTilt w r i s p) ≤
        1 + Real.exp (-c * Real.sqrt (Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hrow⟩ := retained_row_mass
  obtain ⟨w₁,hw₁⟩ := (eventually_atTop.1 (polynomial_absorption hc hC))
  refine ⟨c/4,max w₀ w₁,by positivity,hw₀.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S hS0 hS i s r cap closed hell hr hs hsS
  exact (hrow w ((le_max_left _ _).trans hw) ell S i s r cap closed hell hr hs hsS).trans
    (add_le_add le_rfl (hw₁ w ((le_max_right _ _).trans hw) S hS0 hS))

end NumberTheoryLean.PrimeRowNormalization



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

noncomputable def normalizationRate : ℝ := Classical.choose retained_row_mass_one_add
noncomputable def normalizationThreshold : ℝ := Classical.choose (Classical.choose_spec retained_row_mass_one_add)

 theorem normalizationRate_pos : 0 < normalizationRate :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).1

theorem normalizationThreshold_gt_one : 1 < normalizationThreshold :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.1

noncomputable def epsilon (w : ℝ) : ℝ := Real.exp (-normalizationRate * Real.sqrt (Real.log w))

theorem epsilon_pos (w : ℝ) : 0 < epsilon w := Real.exp_pos _
theorem normalizer_pos (w : ℝ) : 0 < 1+epsilon w := by linarith [epsilon_pos w]

theorem actual_row_bound {w ell S : ℝ} (hw : normalizationThreshold ≤ w) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (z : Node) (hell : 1 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hsS : z.ratio ≤ S) :
    (∑ p ∈ nodeChildren w ell S z, primeTilt w z.gap z.side z.ratio p) ≤ 1+epsilon w := by
  exact (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.2
    w hw ell S hS0 hS z.side z.ratio z.gap z.cutoff z.closed hell hr hs hsS

variable (w ell S : ℝ) (start : Node)
abbrev ChainState := Option (History w ell S start)

instance : MeasurableSpace (ChainState w ell S start) := ⊤
instance : MeasurableSingletonClass (ChainState w ell S start) := ⟨fun _ => trivial⟩

noncomputable def childProbability (h : History w ell S start) (p : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (primeTilt w h.node.gap h.node.side h.node.ratio p / (1+epsilon w))

noncomputable def liveMass (h : History w ell S start) : ℝ≥0∞ :=
  ∑ p ∈ nodeChildren w ell S h.node, childProbability w ell S start h p

noncomputable def liveLaw (h : History w ell S start) : Measure (ChainState w ell S start) :=
  ∑ p ∈ (nodeChildren w ell S h.node).attach,
    childProbability w ell S start h p.1 • Measure.dirac (some (h.append p.1 p.2))

theorem liveLaw_univ (h : History w ell S start) : liveLaw w ell S start h univ = liveMass w ell S start h := by
  simp only [liveLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one,
    Finset.sum_attach, liveMass]

noncomputable def completedLaw (h : History w ell S start) : Measure (ChainState w ell S start) :=
  liveLaw w ell S start h + (1-liveMass w ell S start h) • Measure.dirac none

noncomputable def chain : Kernel (ChainState w ell S start) (ChainState w ell S start) where
  toFun z := match z with
    | none => Measure.dirac none
    | some h => completedLaw w ell S start h
  measurable' := measurable_of_countable _

@[simp] theorem chain_none : chain w ell S start none = Measure.dirac none := rfl
@[simp] theorem chain_some (h : History w ell S start) : chain w ell S start (some h) = completedLaw w ell S start h := rfl

variable {w ell S : ℝ} {start : Node}

theorem liveMass_le_one (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (h : History w ell S start) :
    liveMass w ell S start h ≤ 1 := by
  have hnvalid := terminal_valid hs h.admissible
  have hngap := terminal_gap_positive (by linarith : 0 ≤ ell) hr hs h.admissible
  have hnS := terminal_ratio_le hsS h.admissible
  have hrow := actual_row_bound hw hS0 hS h.node hell hngap hnvalid hnS
  have hZ := normalizer_pos w
  unfold liveMass childProbability
  have hnonneg : ∀ p ∈ nodeChildren w ell S h.node,
      0 ≤ primeTilt w h.node.gap h.node.side h.node.ratio p / (1+epsilon w) := by
    intro p hp
    exact div_nonneg (primeTilt_nonneg (w := w) (r := h.node.gap) (i := h.node.side) (s := h.node.ratio) hnvalid hp) hZ.le
  rw [← ENNReal.ofReal_sum_of_nonneg (s := nodeChildren w ell S h.node)
    (f := fun p => primeTilt w h.node.gap h.node.side h.node.ratio p / (1+epsilon w)) hnonneg, ← Finset.sum_div]
  have hreal : (∑ p ∈ nodeChildren w ell S h.node, primeTilt w h.node.gap h.node.side h.node.ratio p) /
      (1+epsilon w) ≤ 1 := (div_le_iff₀ hZ).mpr (by simpa only [one_mul] using hrow)
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal

theorem chain_isMarkov (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) :
    IsMarkovKernel (chain w ell S start) := by
  constructor
  intro z
  constructor
  cases z with
  | none => simp only [chain_none, measure_univ]
  | some h =>
    rw [chain_some, completedLaw, Measure.add_apply, liveLaw_univ, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (liveMass_le_one hw hell hS0 hS hr hs hsS h)

instance chain_pow_markov [IsMarkovKernel (chain w ell S start)] (n : ℕ) :
    IsMarkovKernel ((chain w ell S start)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (ChainState w ell S start) (ChainState w ell S start)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    rw [hp]
    infer_instance

noncomputable def pathLaw (w ell S : ℝ) (start : Node) (n : ℕ) : Measure (ChainState w ell S start) :=
  ((chain w ell S start)^n) (some History.empty)

theorem pathLaw_isProbability (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (n : ℕ) :
    IsProbabilityMeasure (pathLaw w ell S start n) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold pathLaw
  infer_instance

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeChainProbabilities

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeKilledChain

variable {w ell S : ℝ} {start : Node}

theorem history_append_eq_iff (h k : History w ell S start) (p q : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (hq : q ∈ nodeChildren w ell S k.node) :
    h.append p hp = k.append q hq ↔ h = k ∧ p = q := by
  constructor
  · intro heq
    have hl := congrArg History.primes heq
    have hh := List.append_singleton_inj.mp hl
    exact ⟨History.ext hh.1,hh.2⟩
  · rintro ⟨rfl,rfl⟩
    exact History.ext rfl

theorem liveLaw_at_append (g h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    liveLaw w ell S start g {some (h.append p hp)} =
      ({h} : Set (History w ell S start)).indicator (fun _ => childProbability w ell S start h p) g := by
  classical
  simp only [liveLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Option.some.injEq, history_append_eq_iff,
    mul_ite, mul_one, mul_zero]
  by_cases hgh : g = h
  · subst g
    simp only [true_and, ite_true]
    calc
      _ = ∑ q ∈ nodeChildren w ell S h.node, if q = p then childProbability w ell S start h q else 0 :=
        Finset.sum_attach _ (fun q : ℕ => if q = p then childProbability w ell S start h q else 0)
      _ = _ := by simp [hp]
  · simp [hgh]

theorem chain_at_append (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (z : ChainState w ell S start) :
    chain w ell S start z {some (h.append p hp)} =
      ({some h} : Set (ChainState w ell S start)).indicator (fun _ => childProbability w ell S start h p) z := by
  classical
  cases z with
  | none => simp [chain_none, Set.indicator]
  | some g =>
    rw [chain_some, completedLaw, Measure.add_apply, liveLaw_at_append, Measure.smul_apply]
    simp [Set.indicator]

theorem pathLaw_append (n : ℕ) (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    pathLaw w ell S start (n+1) {some (h.append p hp)} =
      childProbability w ell S start h p * pathLaw w ell S start n {some h} := by
  unfold pathLaw
  have hpow : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
  rw [hpow, Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
  calc
    _ = ∫⁻ z, ({some h} : Set (ChainState w ell S start)).indicator
        (fun _ => childProbability w ell S start h p) z ∂((chain w ell S start)^n) (some History.empty) :=
      lintegral_congr (fun z => chain_at_append h p hp z)
    _ = _ := by rw [lintegral_indicator (measurableSet_singleton _), lintegral_const, Measure.restrict_apply_univ]

noncomputable def nodeProduct (e w : ℝ) (z : Node) (ps : List ℕ) : ℝ :=
  normalizedTiltProduct e w z.side z.ratio z.gap ps

theorem nodeProduct_append (e w : ℝ) (z : Node) (ps qs : List ℕ) :
    nodeProduct e w z (ps++qs) = nodeProduct e w z ps * nodeProduct e w (terminal w z ps) qs := by
  induction ps generalizing z with
  | nil => simp [nodeProduct, normalizedTiltProduct, terminal]
  | cons p ps ih =>
    change (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) (ps++qs) =
      ((primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps) *
        nodeProduct e w (terminal w (step w z p) ps) qs
    rw [ih, mul_assoc]

theorem nodeProduct_nonnegative {e : ℝ} (he : 0 ≤ e) {z : Node} {ps : List ℕ}
    (hs : Valid z.side z.ratio) (hp : allowed w ell S z ps) : 0 ≤ nodeProduct e w z ps := by
  induction ps generalizing z with
  | nil => exact zero_le_one
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hrest⟩
    change 0 ≤ (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps
    exact mul_nonneg (div_nonneg (primeTilt_nonneg hs hchild) (by linarith)) (ih (child_valid hs hchild) hrest)

theorem pathLaw_singleton_weight (hs : Valid start.side start.ratio) (h : History w ell S start) :
    pathLaw w ell S start h.primes.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start h.primes) := by
  classical
  have main : ∀ ps : List ℕ, ∀ h : History w ell S start, h.primes = ps →
      pathLaw w ell S start ps.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start ps) := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil =>
      intro h heq
      have hh : h = History.empty := History.ext heq
      subst h
      change Measure.dirac (some (History.empty : History w ell S start)) {some History.empty} = ENNReal.ofReal (1 : ℝ)
      simp
    | append_singleton ps p ih =>
      intro h heq
      have hall : allowed w ell S start (ps++[p]) := heq ▸ h.admissible
      obtain ⟨hpre,hlast⟩ := (allowed_append w ell S start ps [p]).mp hall
      let g : History w ell S start := ⟨ps,hpre⟩
      have hp : p ∈ nodeChildren w ell S g.node := (allowed_cons w ell S g.node p []).mp hlast |>.1
      have hh : h = g.append p hp := History.ext heq
      rw [hh, List.length_append, List.length_singleton, pathLaw_append, ih g rfl, nodeProduct_append]
      have hgn : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
      have hn : 0 ≤ primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) :=
        div_nonneg (primeTilt_nonneg (w := w) (r := g.node.gap) (i := g.node.side) (s := g.node.ratio) hgn hp) (normalizer_pos w).le
      change ENNReal.ofReal (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w)) *
          ENNReal.ofReal (nodeProduct (epsilon w) w start ps) =
        ENNReal.ofReal (nodeProduct (epsilon w) w start ps *
          (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) * 1))
      rw [← ENNReal.ofReal_mul hn]
      congr 1
      ring
  exact main h.primes h rfl

theorem source_prime_weight_identity (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal * (1+epsilon w)^h.primes.length *
        (h.node.gap/start.gap)^2 * (weight start.side start.ratio / weight h.node.side h.node.ratio) := by
  rw [pathLaw_singleton_weight hs h, ENNReal.toReal_ofReal (nodeProduct_nonnegative (epsilon_pos w).le hs h.admissible)]
  have hweight := normalized_prime_prefix_weight_identity (epsilon_pos w).le hell hr hs h.admissible
  simpa only [nodeProduct, History.node, terminal_gap_eq, terminal_side_eq, terminal_ratio_eq] using hweight

theorem normalized_source_prime_weight (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (h : History w ell S start) :
    IsProbabilityMeasure (pathLaw w ell S start h.primes.length) ∧
      ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
        (pathLaw w ell S start h.primes.length {some h}).toReal * (1+epsilon w)^h.primes.length *
          (h.node.gap/start.gap)^2 * (weight start.side start.ratio / weight h.node.side h.node.ratio) := by
  exact ⟨pathLaw_isProbability hw hell hS0 hS hr hs hsS h.primes.length,
    source_prime_weight_identity (by linarith) hr hs h⟩

end NumberTheoryLean.PrimeChainProbabilities



namespace NumberTheoryLean.PrimeCompactVisits

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry

variable {w ell S : ℝ} {start : Node}

noncomputable def potential (K : ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => min h.node.gap K + 1

noncomputable def visit (K : ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => if h.node.gap ≤ K then 1 else 0

theorem visit_nonneg (K : ℝ) (z : ChainState w ell S start) : 0 ≤ visit K z := by
  cases z with
  | none => exact le_rfl
  | some h => simp only [visit]; split_ifs <;> norm_num

theorem potential_nonneg {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    0 ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    exact add_nonneg (le_min hg.le hK) zero_le_one

theorem potential_le {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    potential K z ≤ K+1 := by
  cases z with
  | none => change (0:ℝ) ≤ K+1; linarith
  | some h => exact add_le_add_left (min_le_right _ _) 1

theorem visit_le_potential {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    visit K z ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    simp only [visit,potential]
    split_ifs with hle
    · rw [min_eq_left hle]; linarith
    · exact add_nonneg (le_min hg.le hK) zero_le_one

theorem child_potential_drift {K : ℝ} (hell : 1 ≤ ell)
    (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    visit K (some h) + potential K (some (h.append p hp)) ≤ potential K (some h) := by
  classical
  have he : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
    (Finset.mem_filter.mp hp).2.1
  simp only [visit,potential,History.append_node,step]
  split_ifs with hle
  · rw [min_eq_left hle]
    have hm := min_le_left (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith
  · rw [min_eq_right (le_of_not_ge hle)]
    have hm := min_le_right (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hell hr hs in

theorem actual_row_drift_ae {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    ∀ᵐ y ∂chain w ell S start z, visit K z + potential K y ≤ potential K z := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (by trivial)).mpr (by simp [visit,potential])
  | some h =>
    have hdead : visit K (some h) + potential K (none : ChainState w ell S start) ≤ potential K (some h) := by
      simpa only [potential,add_zero] using visit_le_potential hK (by linarith : 0 ≤ ell) hr hs (some h)
    have hchild := child_potential_drift (K := K) hell h
    apply ae_iff.mpr
    simp [chain_some,completedLaw,liveLaw,hdead,hchild]

include hw hell hS0 hS hr hs hsS

theorem actual_row_drift {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    ENNReal.ofReal (visit K z) + (∫⁻ y, ENNReal.ofReal (potential K y) ∂chain w ell S start z) ≤
      ENNReal.ofReal (potential K z) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  have hp := actual_row_drift_ae hell hr hs hK z
  have hnon := potential_nonneg (w := w) (S := S) hK (by linarith : 0 ≤ ell) hr hs
  calc
    _ = ∫⁻ y, ENNReal.ofReal (visit K z) + ENNReal.ofReal (potential K y) ∂chain w ell S start z := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
    _ ≤ ∫⁻ _y, ENNReal.ofReal (potential K z) ∂chain w ell S start z := by
      apply lintegral_mono_ae
      filter_upwards [hp] with y hy
      rw [← ENNReal.ofReal_add (visit_nonneg K z) (hnon y)]
      exact ENNReal.ofReal_le_ofReal hy
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem finite_compact_potential {K : ℝ} (hK : 0 ≤ K) (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z, ENNReal.ofReal (visit K z) ∂pathLaw w ell S start n) +
      (∫⁻ z, ENNReal.ofReal (potential K z) ∂pathLaw w ell S start N) ≤
        ENNReal.ofReal (potential K (some (History.empty : History w ell S start))) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  have hV : Measurable (fun z : ChainState w ell S start => ENNReal.ofReal (potential K z)) := measurable_of_countable _
  have hv : Measurable (fun z : ChainState w ell S start => ENNReal.ofReal (visit K z)) := measurable_of_countable _
  induction N with
  | zero =>
    simp only [sum_range_zero,zero_add,pathLaw,pow_zero]
    change (∫⁻ z, ENNReal.ofReal (potential K z) ∂Measure.dirac (some History.empty)) ≤ _
    rw [lintegral_dirac' _ hV]
  | succ N ih =>
    have hnext : (∫⁻ z, ENNReal.ofReal (potential K z) ∂pathLaw w ell S start (N+1)) =
        ∫⁻ z, ∫⁻ y, ENNReal.ofReal (potential K y) ∂chain w ell S start z ∂pathLaw w ell S start N := by
      unfold pathLaw
      have hp : (chain w ell S start)^(N+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^N) := pow_succ' _ _
      rw [hp,Kernel.lintegral_comp _ _ _ hV]
    rw [sum_range_succ,hnext,add_assoc]
    apply le_trans (add_le_add_right ?_ _) ih
    rw [← lintegral_add_left hv]
    exact lintegral_mono (actual_row_drift hw hell hS0 hS hr hs hsS hK)

theorem finite_compact_visits {K : ℝ} (hK : 0 ≤ K) (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z, ENNReal.ofReal (visit K z) ∂pathLaw w ell S start n) ≤
      ENNReal.ofReal (K+1) := by
  exact (le_add_right le_rfl).trans ((finite_compact_potential hw hell hS0 hS hr hs hsS hK N).trans
    (ENNReal.ofReal_le_ofReal (potential_le hK _)))

end NumberTheoryLean.PrimeCompactVisits



namespace NumberTheoryLean.PrimeHistoryHorizon

open _root_.Set _root_.Finset
open _root_.Erdos970.Set _root_.Erdos970.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

theorem valid_ratio_lower {i : Side} {t : ℝ} (ht : Valid i t) : (19/20 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem prime_cost_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hs : Valid i s) (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    (ps.length : ℝ)/(S+1) ≤ pathCost (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => simp [primeRatios,pathCost]
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    have ht := valid_pos (child_valid hs hp)
    have htS : childRatio w r p ≤ S := (Finset.mem_filter.mp hp).2.2.2.2
    have hc : 1/(S+1) ≤ cost (childRatio w r p) :=
      (one_div_le_one_div_of_le (by linarith : 0 < childRatio w r p+1) (by linarith)).trans
        (cost_ge_inv_add_one ht)
    have hih := ih (child_valid hs hp) hrest
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_div, primeRatios, pathCost]
    linarith

theorem prime_gap_cost {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = r * Real.exp (-pathCost (primeRatios w r ps)) := by
  rw [primeFinalGap_eq hell hr hs hpath, finalGap_eq_cost hs (ratios_admissible hpath)]

theorem prime_final_gap_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hne : ps ≠ []) :
    (19/20 : ℝ)*ell < primeFinalGap w r ps := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    cases ps with
    | nil =>
      have hx : ell < primeExponent w p := (Finset.mem_filter.mp hp).2.1
      have hx0 : 0 < primeExponent w p := hell.trans hx
      have ht := valid_ratio_lower (child_valid hs hp)
      have heq : r-primeExponent w p = childRatio w r p * primeExponent w p := by
        unfold childRatio
        field_simp
      change (19/20 : ℝ)*ell < r-primeExponent w p
      calc
        _ < (19/20 : ℝ)*primeExponent w p := mul_lt_mul_of_pos_left hx (by norm_num)
        _ ≤ childRatio w r p * primeExponent w p := mul_le_mul_of_nonneg_right ht hx0.le
        _ = _ := heq.symm
    | cons q qs =>
      exact ih (child_gap_positive hell.le hr hs hp) (child_valid hs hp) hrest (by simp)

theorem prime_source_horizon {w ell S s r cap B : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hB : 0 < B) (hsize : r ≤ (23/10 : ℝ)*B) :
    ps.length < sourceHorizon S B := by
  by_cases hne : ps = []
  · subst ps
    unfold sourceHorizon
    simp
  · have hell0 : 0 < ell := by linarith
    have hgap := prime_final_gap_lower hell0 hr hs hpath hne
    have hl := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19/20) hell0) hgap
    rw [prime_gap_cost hell0.le hr hs hpath,
      Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hc := prime_cost_lower hs hpath
    have hlogR := Real.log_le_log hr hsize
    rw [Real.log_mul (by norm_num : (23/10 : ℝ) ≠ 0) hB.ne'] at hlogR
    have hlog23 : Real.log (23/10 : ℝ) ≤ 13/10 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23/10)
      norm_num at h
      exact h
    have hlog19 : (-1/19 : ℝ) ≤ Real.log (19/20 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19/20)
      norm_num at h
      linarith
    have hlogell : Real.log (19/20 : ℝ) ≤ Real.log ((19/20 : ℝ)*ell) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hn : (ps.length : ℝ)/(S+1) < Real.log B+2 := by linarith
    have hmul := (div_lt_iff₀ (by linarith : 0 < S+1)).mp hn
    have hceil := Nat.le_ceil ((S+1)*(Real.log B+2))
    have hreal : (ps.length : ℝ) < (sourceHorizon S B : ℝ) := by
      unfold sourceHorizon
      push_cast
      nlinarith
    exact_mod_cast hreal

theorem history_length_lt {w ell S B : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (h : History w ell S start) :
    h.primes.length < sourceHorizon S B :=
  prime_source_horizon hell hS hr hs h.admissible hB hsize

end NumberTheoryLean.PrimeHistoryHorizon



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeHistoryHorizon LowStateHorizon

variable {w ell S : ℝ} {start : Node}

def stage (n : ℕ) : ChainState w ell S start → Prop
  | none => True
  | some h => h.primes.length = n

theorem stage_measurable (n : ℕ) : MeasurableSet {z : ChainState w ell S start | stage n z} := trivial

theorem next_stage (n : ℕ) (z : ChainState w ell S start) (hz : stage n z) :
    ∀ᵐ y ∂chain w ell S start z, stage (n+1) y := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (stage_measurable (n+1))).mpr trivial
  | some h =>
    have hlen : h.primes.length = n := hz
    apply ae_iff.mpr
    simp [chain_some, completedLaw, liveLaw, stage, History.append_primes, hlen]

theorem pathLaw_stage (n : ℕ) : ∀ᵐ z ∂pathLaw w ell S start n, stage n z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (some (History.empty : History w ell S start)), stage 0 z
    exact (ae_dirac_iff (stage_measurable 0)).mpr rfl
  | succ n ih =>
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((chain w ell S start)^(n+1)) (some History.empty), stage (n+1) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (stage_measurable (n+1))
    filter_upwards [ih] with z hz
    exact next_stage n z hz

theorem pathLaw_eq_cemetery {B : ℝ} (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    pathLaw w ell S start n = Measure.dirac none := by
  let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
  have hnone : ∀ᵐ z ∂pathLaw w ell S start n, z = none := by
    filter_upwards [pathLaw_stage n] with z hz
    cases z with
    | none => rfl
    | some h =>
      have hlen := history_length_lt hell hS0 hr hs hB hsize h
      change h.primes.length = n at hz
      omega
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_dirac' _ hf]
  calc
    _ = ∫⁻ _z, f none ∂pathLaw w ell S start n := lintegral_congr_ae (hnone.mono (fun z hz => congrArg f hz))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end NumberTheoryLean.PrimeChainHorizon



namespace NumberTheoryLean.PrimeCorrectionFactor

open _root_.Filter _root_.Set
open _root_.Erdos970.Filter _root_.Erdos970.Set
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeHistoryHorizon PrimeKilledChain LowStateHorizon

noncomputable def correctionBudget (d w : ℝ) : ℝ :=
  Real.exp (5*d^3*(Real.log w)^3*epsilon w)-1

theorem correctionBudget_tendsto_zero (d : ℝ) : Tendsto (correctionBudget d) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => 5*d^3*x^6*Real.exp (-normalizationRate*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6 : ℝ) normalizationRate normalizationRate_pos).const_mul (5*d^3)
    simpa only [Real.rpow_ofNat, mul_assoc, mul_zero] using h
  have hi : Tendsto (fun w : ℝ => 5*d^3*(Real.log w)^3*epsilon w) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (ht.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with w hw
    have hp : (Real.sqrt (Real.log w))^6 = (Real.log w)^3 := by
      calc
        _ = ((Real.sqrt (Real.log w))^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hw]
    simp only [Function.comp_apply, epsilon, hp]
  have h := ((Real.continuous_exp.tendsto (0 : ℝ)).comp hi).sub_const 1
  change Tendsto (fun w : ℝ => Real.exp (5*d^3*(Real.log w)^3*epsilon w)-1) atTop (𝓝 0)
  simpa only [Function.comp_apply, Real.exp_zero, sub_self] using h

theorem correction_le_budget {d w B : ℝ} (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (n : ℕ)
    (hn : n ≤ sourceHorizon ((Real.log B)^2) B) :
    0 ≤ (1+epsilon w)^n-1 ∧ (1+epsilon w)^n-1 ≤ correctionBudget d w := by
  have hpow1 : 1 ≤ (1+epsilon w)^n := one_le_pow₀ (by linarith [epsilon_pos w])
  have hN := source_horizon_log_cube hB
  have hnR : (n : ℝ) ≤ (sourceHorizon ((Real.log B)^2) B : ℝ) := by exact_mod_cast hn
  have hcube : (Real.log B)^3 ≤ (d*Real.log w)^3 := pow_le_pow_left₀ (by linarith) hcomp 3
  have hnum : (n : ℝ) ≤ 5*d^3*(Real.log w)^3 := by nlinarith [hN,hnR]
  have hbase : 1+epsilon w ≤ Real.exp (epsilon w) := by
    simpa only [add_comm] using Real.add_one_le_exp (epsilon w)
  have hp : (1+epsilon w)^n ≤ (Real.exp (epsilon w))^n := pow_le_pow_left₀ (by linarith [epsilon_pos w]) hbase n
  rw [← Real.exp_nat_mul] at hp
  have he : Real.exp ((n : ℝ)*epsilon w) ≤ Real.exp (5*d^3*(Real.log w)^3*epsilon w) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnum (epsilon_pos w).le)
  exact ⟨sub_nonneg.mpr hpow1, sub_le_sub_right (hp.trans he) 1⟩

theorem history_correction {d w ell B : ℝ} {start : Node}
    (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) (hell : 1 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B)
    (h : History w ell ((Real.log B)^2) start) :
    0 ≤ (1+epsilon w)^h.primes.length-1 ∧
      (1+epsilon w)^h.primes.length-1 ≤ correctionBudget d w :=
  correction_le_budget hlogB hcomp h.primes.length
    (history_length_lt hell (sq_nonneg _) hr hs hB hsize h).le

end NumberTheoryLean.PrimeCorrectionFactor



namespace NumberTheoryLean.PrimeSideSupport

open _root_.Set _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon

def sideAfter (i : Side) : ℕ → Side
  | 0 => i
  | n+1 => (sideAfter i n).flip

theorem sideAfter_flip (i : Side) (n : ℕ) : sideAfter i.flip n = (sideAfter i n).flip := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sideAfter,ih]

theorem sideAfter_even (n : ℕ) : sideAfter .even (2*n) = .even := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,sideAfter,sideAfter,ih]
    rfl

theorem sideAfter_odd (n : ℕ) : sideAfter .even (2*n+1) = .odd := by
  rw [sideAfter,sideAfter_even]
  rfl

theorem terminal_side_after (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).side = sideAfter z.side ps.length := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih =>
    rw [terminal_cons,ih,List.length_cons,sideAfter]
    exact sideAfter_flip z.side ps.length

def regularLower : Side → ℝ | .even => 2 | .odd => 1
noncomputable def weakLower : Side → ℝ | .even => 2 | .odd => 98/100

def Regular (z : Node) : Prop := regularLower z.side ≤ z.ratio
def WeakRegular (z : Node) : Prop := weakLower z.side ≤ z.ratio

theorem regular_step {w ell S : ℝ} {z : Node} (hz : Regular z) {p : ℕ}
    (hp : p ∈ nodeChildren w ell S z) : Regular (step w z p) := by
  classical
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  cases hi : z.side with
  | even =>
    change regularLower z.side ≤ z.ratio at hz
    rw [hi,regularLower] at hz
    change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
    rw [hi,minRatio] at hlo
    change regularLower z.side.flip ≤ childRatio w z.gap p
    rw [hi,Side.flip,regularLower]
    linarith
  | odd =>
    change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
    rw [hi,minRatio] at hlo
    change regularLower z.side.flip ≤ childRatio w z.gap p
    rw [hi,Side.flip,regularLower]
    exact (le_max_left _ _).trans hlo

theorem two_step_regular {w ell S : ℝ} {z : Node} {p q : ℕ}
    (hp : p ∈ nodeChildren w ell S z) (hq : q ∈ nodeChildren w ell S (step w z p)) :
    Regular (step w (step w z p) q) := by
  classical
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  have hlo' := (Finset.mem_filter.mp hq).2.2.2.1
  change minRatio z.side.flip (childRatio w z.gap p) ≤ childRatio w (step w z p).gap q at hlo'
  change regularLower z.side.flip.flip ≤ childRatio w (step w z p).gap q
  cases hi : z.side with
  | even =>
    rw [Side.flip,Side.flip,regularLower]
    rw [hi,Side.flip,minRatio] at hlo'
    exact (le_max_left _ _).trans hlo'
  | odd =>
    rw [Side.flip,Side.flip,regularLower]
    change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
    rw [hi,minRatio] at hlo
    rw [hi,Side.flip,minRatio] at hlo'
    linarith [le_max_left (2:ℝ) (z.ratio-1)]

theorem terminal_regular_of_regular {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hz : Regular z) (hp : allowed w ell S z ps) : Regular (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (regular_step hz hchild) hpath

theorem terminal_regular {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hp : allowed w ell S z ps) (hlen : 2 ≤ ps.length) : Regular (terminal w z ps) := by
  cases ps with
  | nil => simp at hlen
  | cons p ps =>
    cases ps with
    | nil => simp at hlen
    | cons q qs =>
      rcases (allowed_cons w ell S z p (q::qs)).mp hp with ⟨hp,hrest⟩
      rcases (allowed_cons w ell S (step w z p) q qs).mp hrest with ⟨hq,hrest⟩
      change Regular (terminal w (step w (step w z p) q) qs)
      exact terminal_regular_of_regular (two_step_regular hp hq) hrest

theorem weak_step {w ell S : ℝ} {z : Node} (hz : Valid z.side z.ratio) {p : ℕ}
    (hp : p ∈ nodeChildren w ell S z) : WeakRegular (step w z p) := by
  classical
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
  change weakLower z.side.flip ≤ childRatio w z.gap p
  cases hi : z.side with
  | even =>
    rw [hi,Valid] at hz
    rw [hi,minRatio] at hlo
    rw [Side.flip,weakLower]
    linarith
  | odd =>
    rw [hi,minRatio] at hlo
    rw [Side.flip,weakLower]
    exact (le_max_left _ _).trans hlo

theorem terminal_weak {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hz : Valid z.side z.ratio) (hp : allowed w ell S z ps) (hne : ps ≠ []) :
    WeakRegular (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    cases ps with
    | nil => exact weak_step hz hchild
    | cons q qs => exact ih (child_valid hz hchild) hpath (by simp)

theorem pathLaw_regular {w ell S : ℝ} {start : Node} (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ p ∂pathLaw w ell S start n, match p with
      | none => True
      | some h => Regular h.node := by
  filter_upwards [pathLaw_stage (w:=w) (ell:=ell) (S:=S) (start:=start) n] with p hp
  cases p with
  | none => trivial
  | some h =>
    have heq : h.primes.length = n := hp
    exact terminal_regular h.admissible (by omega)

theorem pathLaw_weak {w ell S : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ p ∂pathLaw w ell S start n, match p with
      | none => True
      | some h => WeakRegular h.node := by
  filter_upwards [pathLaw_stage (w:=w) (ell:=ell) (S:=S) (start:=start) n] with p hp
  cases p with
  | none => trivial
  | some h =>
    have heq : h.primes.length = n := hp
    apply terminal_weak hs h.admissible
    intro he
    simp [he] at heq
    omega

theorem pathLaw_side {w ell S : ℝ} {start : Node} (hi : start.side = .even) (n : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start n, match p with
      | none => True
      | some h => h.node.side = sideAfter .even n := by
  filter_upwards [pathLaw_stage (w:=w) (ell:=ell) (S:=S) (start:=start) n] with p hp
  cases p with
  | none => trivial
  | some h =>
    have heq : h.primes.length = n := hp
    change (terminal w start h.primes).side = _
    rw [terminal_side_after,heq,hi]

end NumberTheoryLean.PrimeSideSupport



namespace NumberTheoryLean.PrimeGridGeometry

open _root_.Set _root_.Erdos970.Set
open FinitePathGeometry PrimeHistories PrimeSideSupport

noncomputable def width (m : ℕ) : ℝ := 1/(m:ℝ)
noncomputable def point (m j : ℕ) : ℝ := (j:ℝ)/(m:ℝ)

theorem width_nonneg (m : ℕ) : 0 ≤ width m := by unfold width; positivity

theorem width_pos {m : ℕ} (hm : 1 ≤ m) : 0 < width m := by
  apply one_div_pos.mpr
  exact_mod_cast (show 0 < m by omega)

theorem point_succ (m j : ℕ) : point m (j+1) = point m j+width m := by
  simp only [point,width,Nat.cast_add,Nat.cast_one,add_div]

theorem point_nonneg (m j : ℕ) : 0 ≤ point m j := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem threshold_le_point {m : ℕ} (hm : 1 ≤ m) (k j : ℕ) :
    (k:ℝ) ≤ point m j ↔ k*m ≤ j := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [point,le_div_iff₀ hm0]
  exact_mod_cast Iff.rfl

theorem index_from_upper {m j k : ℕ} {t : ℝ} (hm : 1 ≤ m)
    (hkt : (k:ℝ) ≤ t) (ht : t < point m (j+1)) : k*m ≤ j := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hdiv : (k:ℝ) < ((j+1:ℕ):ℝ)/(m:ℝ) := hkt.trans_lt ht
  have hmul := (lt_div_iff₀ hm0).mp hdiv
  have hn : k*m < j+1 := by exact_mod_cast hmul
  omega

theorem finite_grid_cover {m J : ℕ} {t : ℝ} (hm : 1 ≤ m) (ht : 0 ≤ t)
    (hJ : t < point m (J+1)) : ∃ j ≤ J, t ∈ Ico (point m j) (point m (j+1)) := by
  let j := ⌊t*(m:ℝ)⌋₊
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have htm : 0 ≤ t*(m:ℝ) := mul_nonneg ht hm0.le
  have hlo := Nat.floor_le htm
  have hhi := Nat.lt_floor_add_one (t*(m:ℝ))
  have hbound : (j:ℝ) < ((J+1:ℕ):ℝ) := by
    have h := (lt_div_iff₀ hm0).mp hJ
    exact hlo.trans_lt h
  have hj : j ≤ J := by
    have hnat : j < J+1 := by exact_mod_cast hbound
    omega
  refine ⟨j,hj,?_⟩
  constructor
  · exact (div_le_iff₀ hm0).mpr hlo
  · apply (lt_div_iff₀ hm0).mpr
    simpa only [Nat.cast_add,Nat.cast_one] using hhi

theorem incoming_grid_end {m : ℕ} (hmN : 1 ≤ m) (j : ℕ) :
    point m (j+m+2) = point m j+1+2*width m := by
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold point width
  push_cast
  field_simp

def lowerIndex (m : ℕ) : Side → ℕ | .even => 2*m | .odd => m

theorem regular_bin_domain {m j : ℕ} {z : Node} (hm : 1 ≤ m) (hz : Regular z)
    (hbin : z.ratio ∈ Ico (point m j) (point m (j+1))) :
    lowerIndex m z.side ≤ j ∧ Valid z.side (point m j) := by
  cases hi : z.side with
  | even =>
    change regularLower z.side ≤ z.ratio at hz
    rw [hi,regularLower] at hz
    have hj := index_from_upper hm (k:=2) hz hbin.2
    have ht : (2:ℝ) ≤ point m j := by simpa only [Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
    rw [lowerIndex,Valid]
    exact ⟨hj,by linarith⟩
  | odd =>
    change regularLower z.side ≤ z.ratio at hz
    rw [hi,regularLower] at hz
    have hj := index_from_upper hm (k:=1) (by simpa only [Nat.cast_one] using hz) hbin.2
    have ht : (1:ℝ) ≤ point m j := by simpa only [Nat.cast_one] using (threshold_le_point hm 1 j).mpr hj
    rw [lowerIndex,Valid]
    exact ⟨by simpa using hj,by linarith⟩

theorem weak_bin_domain {m j : ℕ} {z : Node} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (hz : WeakRegular z) (hbin : z.ratio ∈ Ico (point m j) (point m (j+1))) :
    Valid z.side (point m j) := by
  cases hi : z.side with
  | even =>
    change weakLower z.side ≤ z.ratio at hz
    rw [hi,weakLower] at hz
    have hj := index_from_upper hm (k:=2) hz hbin.2
    have ht : (2:ℝ) ≤ point m j := by simpa only [Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
    rw [Valid]
    linarith
  | odd =>
    change weakLower z.side ≤ z.ratio at hz
    rw [hi,weakLower] at hz
    have ht := hbin.2
    rw [point_succ] at ht
    rw [Valid]
    linarith

theorem child_bin_domain {w ell S : ℝ} {m j p : ℕ} {z : Node}
    (hm : 1 ≤ m) (hsmall : width m ≤ 1/100) (hz : Valid z.side z.ratio)
    (hp : p ∈ nodeChildren w ell S z)
    (hbin : (step w z p).ratio ∈ Ico (point m j) (point m (j+1))) :
    Valid z.side.flip (point m j) :=
  weak_bin_domain hm hsmall (weak_step hz hp) hbin

end NumberTheoryLean.PrimeGridGeometry


end Erdos970

end OAI
