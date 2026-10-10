import Mathlib
import OAI.Probability.IsingPerceptron.OrderedQuantile

namespace OAI

/-! Time Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedHamiltonian_count_succ {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (φ : A → Spin N → ℝ) (m : ℕ) (z : EnrichedFixedData n A) :
    enrichedHamiltonian n h u φ (enrichedCountJoin (m+1,z)) =
      fun s => enrichedHamiltonian n h u φ (enrichedCountJoin (m,z)) s+φ (z.1.1 m) s.1 := by
  funext s
  unfold enrichedHamiltonian enrichedCountJoin
  dsimp only
  rw [patternBase_prefix_succ]
  simp only [Pi.add_apply]
  ring

lemma enrichedFixed_pressure_increment {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (m : ℕ) :
    ∀ᵐ z ∂enrichedFixedLaw P n b,
      enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m+1,z))-
        enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m,z)) =
      cgf (fun s : Spin N × LabeledLeaf n => φ (z.1.1 m) s.1)
        (enrichedGibbsReference n h u ν φ (enrichedCountJoin (m,z))) 1/N := by
  filter_upwards [enrichedFixed_exp_ae hN n b hh h0 u hu ν P hK hφ m,
    enrichedFixed_exp_ae hN n b hh h0 u hu ν P hK hφ (m+1)] with z he he'
  rw [enrichedHamiltonian_count_succ] at he'
  have hc := cgf_fold (labeledSpinReference n ν z.1.2)
    (enrichedHamiltonian n h u φ (enrichedCountJoin (m,z)))
    (fun s : Spin N × LabeledLeaf n => φ (z.1.1 m) s.1) 1 he (by simpa using he')
  change cgf _ (enrichedGibbsReference n h u ν φ (enrichedCountJoin (m,z))) _ = _ at hc
  rw [hc]
  change (Real.log (referencePartition (labeledSpinReference n ν z.1.2)
    (enrichedHamiltonian n h u φ (enrichedCountJoin (m+1,z))))-N*h n/2)/N -
    (Real.log (referencePartition (labeledSpinReference n ν z.1.2)
    (enrichedHamiltonian n h u φ (enrichedCountJoin (m,z))))-N*h n/2)/N = _
  rw [enrichedHamiltonian_count_succ]
  simp only [one_mul]
  ring

lemma enrichedFixed_mean_step_bound {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (m : ℕ) :
    |(∫ z, enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m+1,z)) ∂enrichedFixedLaw P n b)-
      (∫ z, enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m,z)) ∂enrichedFixedLaw P n b)| ≤ K/N := by
  rw [← integral_sub (enrichedFixed_pressure_integrable hN n b hb hh h0 u hu ν P hm hK hφ (m+1))
    (enrichedFixed_pressure_integrable hN n b hb hh h0 u hu ν P hm hK hφ m),← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le_const (C := K/N) ?_).trans (by simp)
  filter_upwards [enrichedFixed_pressure_increment hN n b hh h0 u hu ν P hK hφ m] with z hz
  rw [hz,Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact abs_cgf_one_le _ (measurable_of_countable _) (fun s => hφ (z.1.1 m) s.1)

lemma enrichedMeanPressure_eq_poissonMean {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b h u ν φ =
      poissonMean (fun m => ∫ z, enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m,z))
        ∂enrichedFixedLaw P n b) r := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n)) u hu ν P hm hK hφ r
    (α := (r:ℝ)/N) (by rw [div_mul_cancel₀ _ hn])).1.integrable (by norm_num)
  have hp := enrichedCountJoin_preserving P r n b
  rw [poissonMean_eq_integral]
  unfold enrichedMeanPressure
  rw [← hp.hasLaw.integral_comp hi.aestronglyMeasurable,integral_prod _ ((hp.map_eq.symm ▸ hi).comp_measurable hp.measurable)]
  rfl

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def enrichedNextPatternCGF {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (m : ℕ) (z : EnrichedFixedData n A) : ℝ :=
  cgf (fun s : Spin N × LabeledLeaf n => φ (z.1.1 m) s.1)
    (enrichedGibbsReference n h u ν φ (enrichedCountJoin (m,z))) 1

lemma enrichedFixed_mean_increment {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (m : ℕ) :
    (∫ z, enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m+1,z)) ∂enrichedFixedLaw P n b)-
      (∫ z, enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m,z)) ∂enrichedFixedLaw P n b) =
      (∫ z, enrichedNextPatternCGF n h u ν φ m z ∂enrichedFixedLaw P n b)/N := by
  rw [← integral_sub (enrichedFixed_pressure_integrable hN n b hb hh h0 u hu ν P hm hK hφ (m+1))
    (enrichedFixed_pressure_integrable hN n b hb hh h0 u hu ν P hm hK hφ m),
    integral_congr_ae (enrichedFixed_pressure_increment hN n b hh h0 u hu ν P hK hφ m),integral_div]
  rfl

 

theorem enrichedMeanPressure_time_derivative {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => -enrichedMeanPressure P (Real.toNNReal (N*s)) n b h u ν φ)
      (-(∫ m, ∫ z, enrichedNextPatternCGF n h u ν φ m z ∂enrichedFixedLaw P n b
        ∂poissonMeasure (Real.toNNReal (N*t)))) t := by
  let a : ℕ → ℝ := fun m => ∫ z, enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m,z))
    ∂enrichedFixedLaw P n b
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hstep := enrichedFixed_mean_step_bound hN n b hb hh h0 u hu ν P hm hK hφ
  change ∀ m, |a (m+1)-a m| ≤ K/N at hstep
  have hd := ((poisson_count_derivative (div_nonneg hK hn.le) hstep ((N:ℝ)*t)).comp t
    ((hasDerivAt_id t).const_mul (N:ℝ))).neg
  simp only [mul_one] at hd
  have hdval : poissonMean (fun m => a (m+1)-a m) ((N:ℝ)*t)*(N:ℝ) =
      (∫ m, ∫ z, enrichedNextPatternCGF n h u ν φ m z ∂enrichedFixedLaw P n b
        ∂poissonMeasure (Real.toNNReal (N*t))) := by
    rw [← Real.coe_toNNReal ((N:ℝ)*t) (mul_nonneg hn.le ht.le),poissonMean_eq_integral]
    have he (m : ℕ) : a (m+1)-a m =
        (∫ z, enrichedNextPatternCGF n h u ν φ m z ∂enrichedFixedLaw P n b)/N :=
      enrichedFixed_mean_increment hN n b hb hh h0 u hu ν P hm hK hφ m
    simp_rw [he]
    rw [integral_div,div_mul_cancel₀ _ hn.ne']
    simp [max_eq_left (mul_nonneg hn.le ht.le)]
  rw [hdval] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  congr 1
  rw [enrichedMeanPressure_eq_poissonMean hN n b hb hh h0 u hu ν P hm hK hφ,
    Real.coe_toNNReal _ (mul_nonneg hn.le hs.le)]
  rfl

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma random_cylinder_cgf_amplitude_cost {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ 1)
    {d : ℝ} (hd : ∀ x, cylinderCross (A x) (A x) = d) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (a : ℝ) {v w : ℝ} (hv : |v| ≤ 2) (hw : |w| ≤ 2) :
    |(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A x) z.2) (ν z.1) (a*v)
        ∂P.prod gaussianCoordinates)-
      (∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A x) z.2) (ν z.1) (a*w)
        ∂P.prod gaussianCoordinates)| ≤ (4*a^2)*|v-w| := by
  let F := fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A x) z.2) (ν z.1) (a*t)
    ∂P.prod gaussianCoordinates
  let R := fun t => randomReplicaAverage P ν A (a*t)
    (fun σ : Fin 2 → X => cylinderCross (A (σ 1)) (A (σ 0)))
  have hR (t : ℝ) : |R t| ≤ 1 := randomReplicaAverage_abs_le hν A (a*t) _ zero_le_one
    (fun σ => by simpa using cylinderCross_bound A hA (σ 1) (σ 0))
  have hder (t : ℝ) : HasDerivAt F ((a*t*(d-R t))*a) t := by
    simpa only [F,R,mul_one,id_eq,Function.comp_def] using (hasDerivAt_random_cylinder_covariance hν A hA hd (a*t)).comp t
      ((hasDerivAt_id t).const_mul a)
  have hbound (t : ℝ) (ht : t ∈ Icc (-2:ℝ) 2) : |(a*t*(d-R t))*a| ≤ 4*a^2 := by
    have ht' : |t| ≤ 2 := abs_le.mpr ht
    have hd' : |d-R t| ≤ 2 := (abs_sub _ _).trans (by rw [abs_of_nonneg hd0]; linarith [hR t])
    rw [abs_mul,abs_mul,abs_mul]
    calc
      _ ≤ (|a| *2*2)* |a| := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left ht' (abs_nonneg a)) hd' (abs_nonneg _) (by positivity)) (abs_nonneg a)
      _ = _ := by nlinarith [sq_abs a]
  have he := (convex_Icc (-2:ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hder t).hasDerivWithinAt) (fun t ht => hbound t ht)
    (abs_le.mp hw) (abs_le.mp hv)
  simpa only [Real.norm_eq_abs] using he

lemma enriched_coordinate_lipschitz {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N) {v w : ℝ}
    (hv : |v| ≤ 2) (hw : |w| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    |enrichedMeanPressure P r n b h (Function.update u j v) ν φ-
      enrichedMeanPressure P r n b h (Function.update u j w) ν φ| ≤
        (4*(perturbationAmplitude N j)^2/N)*|v-w| := by
  have hdiag (x : Spin N × LabeledLeaf n) := monomialCoefficients_variance hN n (monomialIndex j).1 (monomialIndex j).2 x
  simp_rw [← cylinderCross_self] at hdiag
  have hc := random_cylinder_cgf_amplitude_cost (P := enrichedFrozenLaw P r n b j)
    (measurable_enrichedFrozenReference n h u j ν hm)
    (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2)
    (monomialCoefficients_variance_le hN n (monomialIndex j).1 (monomialIndex j).2)
    hdiag (monomialPath_nonneg n (monomialIndex j).2 n) (monomialPath_diag_le_one n (monomialIndex j).2)
    (perturbationAmplitude N j) hv hw
  change |(∫ z, enrichedCGF n h u j ν φ v z ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates)-
      (∫ z, enrichedCGF n h u j ν φ w z ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates)| ≤ _ at hc
  rw [(enrichedCGF_integral hN n b hb hh h0 u hu j hv ν P hm hK hφ r).2,
    (enrichedCGF_integral hN n b hb hh h0 u hu j hw ν P hm hK hφ r).2] at hc
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [← mul_sub,sub_sub_sub_cancel_right,abs_mul,abs_of_pos hn] at hc
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  nlinarith [hc]

 
lemma cube_coordinate_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (C : ι → ℝ)
    (hF : ∀ (u : ι → ℝ), (∀ j, |u j| ≤ 2) → ∀ (j : ι) (v w : ℝ),
      |v| ≤ 2 → |w| ≤ 2 → |F (Function.update u j v)-F (Function.update u j w)| ≤ C j*|v-w|)
    {u v : ι → ℝ} (hu : ∀ j, |u j| ≤ 2) (hv : ∀ j, |v j| ≤ 2) :
    |F u-F v| ≤ ∑ j, C j*|u j-v j| := by
  let mix := fun (s : Finset ι) j => if j ∈ s then u j else v j
  have hm (s : Finset ι) : ∀ j, |mix s j| ≤ 2 := by
    intro j; dsimp only [mix]; split_ifs; exact hu j; exact hv j
  have hs (s : Finset ι) : |F (mix s)-F v| ≤ ∑ j ∈ s, C j*|u j-v j| := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert j s hj ih =>
      have he : mix (insert j s) = Function.update (mix s) j (u j) := by
        ext k; by_cases hk : k=j <;> simp [mix,hk]
      have he' : Function.update (mix s) j (v j) = mix s := by
        apply Function.update_eq_self_iff.mpr
        simp [mix,hj]
      have hb := hF (mix s) (hm s) j (u j) (v j) (hu j) (hv j)
      rw [he'] at hb
      rw [he,Finset.sum_insert hj]
      exact (abs_sub_le (F (Function.update (mix s) j (u j))) (F (mix s)) (F v)).trans
        (add_le_add hb ih)
  simpa [mix] using hs Finset.univ

theorem enrichedMeanPressure_perturbation_lipschitz {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {u v : Fin N → ℝ} (hu : ∀ j, |u j| ≤ 2) (hv : ∀ j, |v j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    |enrichedMeanPressure P r n b h u ν φ-enrichedMeanPressure P r n b h v ν φ| ≤
      ∑ j : Fin N, (4*(perturbationAmplitude N j)^2/N)*|u j-v j| :=
  cube_coordinate_sum_bound (fun w => enrichedMeanPressure P r n b h w ν φ)
    (fun (j : Fin N) => 4*(perturbationAmplitude N j)^2/N) (fun w hw j _ _ hx hy =>
    enriched_coordinate_lipschitz hN n b hb hh h0 w hw j hx hy ν P hm hK hφ r) hu hv

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma poissonMean_lipschitz {a : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ n, |a (n+1)-a n| ≤ K) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |poissonMean a r-poissonMean a s| ≤ K*|r-s| := by
  have hd := fun t (_ : t ∈ Ici (0:ℝ)) => (poisson_count_derivative hK ha t).hasDerivWithinAt (s := Ici 0)
  have hb (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      ‖poissonMean (fun n => a (n+1)-a n) t‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact poissonMean_derivative_bound hK ha (⟨t,ht⟩ : ℝ≥0)
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (0:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (show s ∈ Ici 0 from hs) (show r ∈ Ici 0 from hr)

theorem enrichedMeanPressure_time_lipschitz {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r s : ℝ≥0) :
    |enrichedMeanPressure P r n b h u ν φ-enrichedMeanPressure P s n b h u ν φ| ≤
      (K/N)*|(r:ℝ)-s| := by
  rw [enrichedMeanPressure_eq_poissonMean hN n b hb hh h0 u hu ν P hm hK hφ,
    enrichedMeanPressure_eq_poissonMean hN n b hb hh h0 u hu ν P hm hK hφ]
  exact poissonMean_lipschitz (div_nonneg hK (Nat.cast_nonneg N))
    (enrichedFixed_mean_step_bound hN n b hb hh h0 u hu ν P hm hK hφ) r.coe_nonneg s.coe_nonneg

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev ContactParameter (n N : ℕ) := ℝ≥0 × (Fin (n+1) → ℝ) × (Fin N → ℝ)

def contactRegion (n N : ℕ) (rmax : ℝ≥0) (H : ℝ) : Set (ContactParameter n N) :=
  Icc (0, (fun _ => 0), (fun _ => 1)) (rmax, (fun _ => H), (fun _ => 2)) ∩
    {p | (∑ j, p.2.1 j) ≤ H}

lemma contactRegion_nonneg {n N : ℕ} {rmax : ℝ≥0} {H : ℝ} {p : ContactParameter n N}
    (hp : p ∈ contactRegion n N rmax H) :
    0 ≤ p.1 ∧ p.1 ≤ rmax ∧ (∀ j, 0 ≤ p.2.1 j) ∧ (∑ j, p.2.1 j) ≤ H ∧
      ∀ j, p.2.2 j ∈ Icc (1:ℝ) 2 := by
  exact ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.2,fun j => ⟨hp.1.1.2.2 j,hp.1.2.2.2 j⟩⟩

lemma contactRegion_mem {n N : ℕ} {rmax : ℝ≥0} {H : ℝ} {p : ContactParameter n N}
    (hr : p.1 ≤ rmax) (ha : ∀ j, 0 ≤ p.2.1 j) (hcap : (∑ j, p.2.1 j) ≤ H)
    (hu : ∀ j, p.2.2 j ∈ Icc (1:ℝ) 2) : p ∈ contactRegion n N rmax H := by
  refine ⟨⟨⟨bot_le,ha,fun j => (hu j).1⟩,hr,?_,fun j => (hu j).2⟩,hcap⟩
  intro j
  exact (Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ j)).trans hcap

lemma isCompact_contactRegion (n N : ℕ) (rmax : ℝ≥0) (H : ℝ) :
    IsCompact (contactRegion n N rmax H) :=
  isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)

lemma contactRegion_nonempty (n N : ℕ) (rmax : ℝ≥0) {H : ℝ} (hH : 0 ≤ H) :
    (contactRegion n N rmax H).Nonempty := by
  refine ⟨(0,fun _ => 0,fun _ => (3:ℝ)/2),contactRegion_mem bot_le (fun _ => le_rfl) ?_ ?_⟩
  · simpa using hH
  · intro j; norm_num

lemma enrichedMeanPressure_parameters_continuousOn {N : ℕ} (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) {s : Set (ContactParameter n N)}
    (hs : ∀ p ∈ s, (∀ j, 0 ≤ p.2.1 j) ∧ ∀ j, |p.2.2 j| ≤ 2) :
    ContinuousOn (fun p => enrichedMeanPressure P p.1 n b (finiteFieldPath p.2.1) p.2.2 ν φ) s := by
  let F := fun p : ContactParameter n N =>
    enrichedMeanPressure P p.1 n b (finiteFieldPath p.2.1) p.2.2 ν φ
  have hbnd (p q : s) : |F p-F q| ≤
      (K/N)*|(p.val.1:ℝ)-q.val.1| + (∑ j, |p.val.2.1 j-q.val.2.1 j|)/2 +
      ∑ j : Fin N, (4*(perturbationAmplitude N j)^2/N)*|p.val.2.2 j-q.val.2.2 j| := by
    have hp := hs p p.property
    have hq := hs q q.property
    have hr := enrichedMeanPressure_time_lipschitz hN n b hb (monotone_finiteFieldPath hp.1)
      (finiteFieldPath_nonneg hp.1 0) p.val.2.2 hp.2 ν P hm hK hφ p.val.1 q.val.1
    have ha := enrichedMeanPressure_field_lipschitz hN n b hb hp.1 hq.1 p.val.2.2 hp.2 ν P hm hK hφ q.val.1
    have hu := enrichedMeanPressure_perturbation_lipschitz hN n b hb (monotone_finiteFieldPath hq.1)
      (finiteFieldPath_nonneg hq.1 0) hp.2 hq.2 ν P hm hK hφ q.val.1
    have ht1 := abs_sub_le (F p)
      (enrichedMeanPressure P q.val.1 n b (finiteFieldPath p.val.2.1) p.val.2.2 ν φ)
      (enrichedMeanPressure P q.val.1 n b (finiteFieldPath q.val.2.1) p.val.2.2 ν φ)
    have ht2 := abs_sub_le (F p)
      (enrichedMeanPressure P q.val.1 n b (finiteFieldPath q.val.2.1) p.val.2.2 ν φ) (F q)
    dsimp only [F] at *
    linarith
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_continuousAt.mpr
  intro q
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let E := fun p : s =>
    (K/N)*|(p.val.1:ℝ)-q.val.1| + (∑ j, |p.val.2.1 j-q.val.2.1 j|)/2 +
      ∑ j : Fin N, (4*(perturbationAmplitude N j)^2/N)*|p.val.2.2 j-q.val.2.2 j|
  have hE : Continuous E := by fun_prop
  have hEq : E q = 0 := by simp [E]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs, F, Set.domRestrict_apply] using hbnd p q))
  simpa only [hEq] using (hE.continuousAt (x := q)).tendsto

 
def enrichedContactObjective {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (n : ℕ) (b : ℕ → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (c : Fin (n+1) → ℝ) (S v : ℝ) (p : ContactParameter n N) : ℝ :=
  -enrichedMeanPressure P p.1 n b (finiteFieldPath p.2.1) p.2.2 ν φ -
    (∑ i, c i*finiteFieldPath p.2.1 i)/2 + S + ((p.1:ℝ)/N)*v +
    ∑ j : Fin N, perturbationWeight j * (p.2.2 j-3/2)^2

lemma continuous_enrichedContactPenalty {N n : ℕ} (c : Fin (n+1) → ℝ) (S v : ℝ) :
    Continuous (fun p : ContactParameter n N => -(∑ i, c i*finiteFieldPath p.2.1 i)/2 +
      S + ((p.1:ℝ)/N)*v + ∑ j : Fin N, perturbationWeight j*(p.2.2 j-3/2)^2) := by
  have hf (i : Fin (n+1)) : Continuous (fun p : ContactParameter n N => finiteFieldPath p.2.1 i) := by
    unfold finiteFieldPath
    apply continuous_finsetSum
    intro j _
    split_ifs <;> fun_prop
  exact (((((continuous_finsetSum _ (fun i _ => continuous_const.mul (hf i))).neg).div_const 2).add
    continuous_const).add ((by fun_prop : Continuous (fun p : ContactParameter n N => (p.1:ℝ)/N)).mul continuous_const)).add
      (continuous_finsetSum _ (fun j _ => by fun_prop))

 

theorem enrichedContactObjective_exists_minimum {N : ℕ} (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (rmax : ℝ≥0) {H : ℝ} (hH : 0 ≤ H)
    (c : Fin (n+1) → ℝ) (S v : ℝ) :
    ∃ p ∈ contactRegion n N rmax H,
      IsMinOn (enrichedContactObjective P n b ν φ c S v) (contactRegion n N rmax H) p := by
  apply (isCompact_contactRegion n N rmax H).exists_isMinOn (contactRegion_nonempty n N rmax hH)
  have hc := enrichedMeanPressure_parameters_continuousOn hN n b hb ν P hm hK hφ
    (s := contactRegion n N rmax H) (fun p hp => by
      have h := contactRegion_nonneg hp
      exact ⟨h.2.2.1,fun j => abs_le.mpr ⟨by linarith [(h.2.2.2.2 j).1],(h.2.2.2.2 j).2⟩⟩)
  have he := hc.neg.add (continuous_enrichedContactPenalty c S v).continuousOn
  convert he using 1
  ext p
  simp only [enrichedContactObjective,sub_eq_add_neg,Pi.add_apply,Pi.neg_apply]
  ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma right_derivative_nonneg_of_min {F : ℝ → ℝ} {D : ℝ}
    (hD : HasDerivWithinAt F D (Ici 0) 0)
    (hmin : ∀ᶠ a in 𝓝[>] (0:ℝ), F 0 ≤ F a) : 0 ≤ D := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp
    (hD.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto ht
  filter_upwards [hmin,self_mem_nhdsWithin] with a ha ha'
  simpa only [slope_def_field,sub_zero] using div_nonneg (sub_nonneg.mpr ha) ha'.le

def enrichedFieldObjective {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (c : Fin (n+1) → ℝ) (h : ℕ → ℝ) : ℝ :=
  -enrichedMeanPressure P r n b h u ν φ - (∑ i, c i*h i)/2

 

theorem enriched_field_minimum_cone {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) (c : Fin (n+1) → ℝ)
    {H : ℝ} (hcap : h n < H)
    (hmin : ∀ g : ℕ → ℝ, Monotone g → 0 ≤ g 0 → g n ≤ H →
      enrichedFieldObjective P r n b u ν φ c h ≤ enrichedFieldObjective P r n b u ν φ c g) :
    (∑ i, c i*l i) ≤ enrichedReplicaAverage P r n b h u ν φ
      (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        spinOverlap (σ 1).1 (σ 0).1*l (labeledCommonDepth n (σ 1).2 (σ 0).2)) := by
  let R := enrichedReplicaAverage P r n b h u ν φ
      (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        spinOverlap (σ 1).1 (σ 0).1*l (labeledCommonDepth n (σ 1).2 (σ 0).2))
  have hd := enrichedMeanPressure_field_derivative hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r
  have hs : HasDerivAt (fun a : ℝ => ∑ i : Fin (n+1), c i*(h i+a*l i))
      (∑ i : Fin (n+1), c i*l i) 0 := by
    simpa only [one_mul, id_eq] using HasDerivAt.fun_sum
      (fun (i : Fin (n+1)) (_ : i ∈ Finset.univ) =>
        (((hasDerivAt_id (0:ℝ)).mul_const (l i)).const_add (h i)).const_mul (c i))
  have hD : HasDerivWithinAt (fun a => enrichedFieldObjective P r n b u ν φ c (fun i => h i+a*l i))
      (R/2-(∑ i, c i*l i)/2) (Ici 0) 0 := hd.sub (hs.div_const 2).hasDerivWithinAt
  have hfeas : ∀ᶠ a in 𝓝[>] (0:ℝ), h n+a*l n < H := by
    have hc : ContinuousAt (fun a : ℝ => h n+a*l n) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa using hcap))).filter_mono nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hD (by
    filter_upwards [hfeas,self_mem_nhdsWithin] with a ha ha'
    have hg : Monotone (fun i => h i+a*l i) := hh.add (hl.const_mul ha'.le)
    simpa only [zero_mul,add_zero] using hmin (fun i => h i+a*l i) hg
      (add_nonneg h0 (mul_nonneg ha'.le l0)) ha.le)
  change (∑ i, c i*l i) ≤ R
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteFieldPath_const_mul {n : ℕ} (a : Fin (n+1) → ℝ) (t : ℝ) :
    finiteFieldPath (fun i => t*a i) = fun i => t*finiteFieldPath a i := by
  ext i
  simp only [finiteFieldPath,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma enriched_contact_perturbation_minimum {N n : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (b : ℕ → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (c : Fin (n+1) → ℝ) (S v : ℝ) {rmax : ℝ≥0} {H : ℝ} {p : ContactParameter n N}
    (hp : p∈contactRegion n N rmax H)
    (hmin : IsMinOn (enrichedContactObjective P n b ν φ c S v) (contactRegion n N rmax H) p)
    (u : Fin N → ℝ) (hu : ∀ j, u j∈Icc (1:ℝ) 2) :
    enrichedPerturbationObjective P p.1 n b (finiteFieldPath p.2.1) ν φ p.2.2 ≤
      enrichedPerturbationObjective P p.1 n b (finiteFieldPath p.2.1) ν φ u := by
  have hp' := contactRegion_nonneg hp
  have hq : (p.1,p.2.1,u) ∈ contactRegion n N rmax H :=
    contactRegion_mem hp'.2.1 hp'.2.2.1 hp'.2.2.2.1 hu
  have H := hmin hq
  simp only [Set.mem_ofPred_eq, enrichedContactObjective,enrichedPerturbationObjective] at H ⊢
  linarith

lemma enriched_contact_time_minimum {N n : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (b : ℕ → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (c : Fin (n+1) → ℝ) (S v : ℝ) {rmax : ℝ≥0} {H : ℝ} {p : ContactParameter n N}
    (hp : p∈contactRegion n N rmax H)
    (hmin : IsMinOn (enrichedContactObjective P n b ν φ c S v) (contactRegion n N rmax H) p)
    (r : ℝ≥0) (hr : r≤rmax) :
    -enrichedMeanPressure P p.1 n b (finiteFieldPath p.2.1) p.2.2 ν φ+((p.1:ℝ)/N)*v ≤
      -enrichedMeanPressure P r n b (finiteFieldPath p.2.1) p.2.2 ν φ+((r:ℝ)/N)*v := by
  have hp' := contactRegion_nonneg hp
  have hq : (r,p.2.1,p.2.2) ∈ contactRegion n N rmax H :=
    contactRegion_mem hr hp'.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2
  have H := hmin hq
  simp only [Set.mem_ofPred_eq, enrichedContactObjective] at H
  linarith

 

theorem enriched_contact_cone {N : ℕ} (hN : 0<N) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → Spin N → ℝ} (hm : Measurable φ)
    {K : ℝ} (hK : 0≤K) (hφ : ∀ y x, |φ y x|≤K)
    (c : Fin (n+1) → ℝ) (S v : ℝ) {rmax : ℝ≥0} {H : ℝ} {p : ContactParameter n N}
    (hp : p∈contactRegion n N rmax H)
    (hmin : IsMinOn (enrichedContactObjective P n b ν φ c S v) (contactRegion n N rmax H) p)
    (hcap : (∑ i, p.2.1 i)<H) (d : Fin (n+1) → ℝ) (hd : ∀ i, 0≤d i) :
    (∑ i, c i*finiteFieldPath d i) ≤ enrichedReplicaAverage P p.1 n b (finiteFieldPath p.2.1) p.2.2 ν φ
      (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        spinOverlap (σ 1).1 (σ 0).1*finiteFieldPath d (labeledCommonDepth n (σ 1).2 (σ 0).2)) := by
  have hp' := contactRegion_nonneg hp
  have hu : ∀ j, |p.2.2 j|≤2 := fun j => abs_le.mpr ⟨by linarith [(hp'.2.2.2.2 j).1],(hp'.2.2.2.2 j).2⟩
  let h := finiteFieldPath p.2.1
  let l := finiteFieldPath d
  let R := enrichedReplicaAverage P p.1 n b h p.2.2 ν φ
    (fun σ : Fin 2 → Spin N × LabeledLeaf n => spinOverlap (σ 1).1 (σ 0).1*l (labeledCommonDepth n (σ 1).2 (σ 0).2))
  have hder := enrichedMeanPressure_field_derivative hN n b hb
    (monotone_finiteFieldPath hp'.2.2.1) (finiteFieldPath_nonneg hp'.2.2.1 0)
    (monotone_finiteFieldPath hd) (finiteFieldPath_nonneg hd 0) p.2.2 hu ν P hm hK hφ p.1
  have hs : HasDerivAt (fun t : ℝ => ∑ i : Fin (n+1), c i*(h i+t*l i)) (∑ i, c i*l i) 0 := by
    simpa only [one_mul,id_eq] using HasDerivAt.fun_sum (fun (i : Fin (n+1)) (_ : i∈Finset.univ) =>
      (((hasDerivAt_id (0:ℝ)).mul_const (l i)).const_add (h i)).const_mul (c i))
  have hD : HasDerivWithinAt (fun t => enrichedFieldObjective P p.1 n b p.2.2 ν φ c (fun i => h i+t*l i))
      (R/2-(∑ i, c i*l i)/2) (Ici 0) 0 := hder.sub (hs.div_const 2).hasDerivWithinAt
  have hfeas : ∀ᶠ t in 𝓝[>] (0:ℝ), (∑ i, p.2.1 i)+t*(∑ i, d i)<H := by
    have hc : ContinuousAt (fun t : ℝ => (∑ i, p.2.1 i)+t*(∑ i, d i)) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa using hcap))).filter_mono nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hD (by
    filter_upwards [hfeas,self_mem_nhdsWithin] with t ht ht'
    have hnew : (p.1,(fun i => p.2.1 i+t*d i),p.2.2)∈contactRegion n N rmax H :=
      contactRegion_mem hp'.2.1 (fun i => add_nonneg (hp'.2.2.1 i) (mul_nonneg ht'.le (hd i)))
        (by simpa only [Finset.sum_add_distrib,Finset.mul_sum] using ht.le) hp'.2.2.2.2
    have H := hmin hnew
    simp only [Set.mem_ofPred_eq, enrichedContactObjective,finiteFieldPath_add,finiteFieldPath_const_mul] at H
    simp only [enrichedFieldObjective,zero_mul,add_zero]
    dsimp only [h,l]
    linarith)
  change (∑ i, c i*l i) ≤ R
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def depthTail (n j : ℕ) (t : ℝ) : ℝ := if j=0 then 1 else treeTail n (j-1) t
lemma continuous_depthTail (n j : ℕ) : Continuous (depthTail n j) := by
  unfold depthTail
  split_ifs
  · exact continuous_const
  · exact continuous_treeTail n (j-1)
lemma depthTail_mem (n j : ℕ) (t : ℝ) : depthTail n j t∈Icc (0:ℝ) 1 := by
  unfold depthTail
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact treeTail_mem n (j-1) t
lemma depthTail_level (n j d : ℕ) : depthTail n j ((d:ℝ)/(n+1:ℕ)) = if j ≤ d then 1 else 0 := by
  by_cases hj : j=0
  · simp [depthTail,hj]
  · simp only [depthTail,hj,ite_false,treeTail_level,show j-1<d ↔ j ≤ d by omega]

lemma finiteFieldPath_single {n : ℕ} (j : Fin (n+1)) (i : ℕ) :
    finiteFieldPath (Pi.single j (1:ℝ)) i=if j.val ≤ i then 1 else 0 := by
  classical
  unfold finiteFieldPath
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

lemma enrichedArrayLaw_depthTail {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) (j : Fin (n+1)) :
    (∫ x, spinArray x 0 1*depthTail n j (treeArray x 0 1)
      ∂(enrichedArrayLaw P r n b h u ν hm : Measure JointArray)) =
      enrichedReplicaAverage P r n b h u ν φ (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        spinOverlap (σ 1).1 (σ 0).1*finiteFieldPath (Pi.single j (1:ℝ))
          (labeledCommonDepth n (σ 1).2 (σ 0).2)) := by
  rw [enrichedArrayLaw_integral P r n b h u ν hm
    (fun x => spinArray x 0 1*depthTail n j (treeArray x 0 1))
    ((by unfold spinArray; fun_prop : Continuous (fun x : JointArray => spinArray x 0 1)).mul
      ((continuous_depthTail n j).comp (by unfold treeArray; fun_prop))).measurable]
  let D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ := fun σ =>
    spinOverlap (σ 1).1 (σ 0).1*finiteFieldPath (Pi.single j (1:ℝ))
      (labeledCommonDepth n (σ 1).2 (σ 0).2)
  have hbD (σ) : |D σ| ≤ 1 := by
    dsimp only [D]
    rw [finiteFieldPath_single]
    split_ifs
    · simpa using abs_spinOverlap_le hN (σ 1).1 (σ 0).1
    · simp
  have he := enrichedReplicaLaw_integral hN n b hh h0 u hu ν P hm hK hφ r D hbD
    (fun i : Fin 2 => i.val) Fin.val_injective
  rw [← he]
  apply integral_congr_ae
  apply ae_of_all
  intro σ
  change spinOverlap (σ 0).1 (σ 1).1*depthTail n j (treeOverlap n (σ 0).2 (σ 1).2)=_
  rw [treeOverlap,depthTail_level]
  simp only [D,finiteFieldPath_single,Fin.val_zero,Fin.val_one]
  rw [spinOverlap_symm,labeledCommonDepth_symm]

end IsingPerceptron

end

end OAI
