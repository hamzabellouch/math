import Mathlib

namespace OAI

 

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace FourierLLogL

abbrev Torus := AddCircle (2 * Real.pi)

instance circlePeriod_pos : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

 
def circleMeasure : Measure Torus := AddCircle.haarAddCircle

 

def MemLLogL (f : Torus → ℂ) : Prop :=
  AEStronglyMeasurable f circleMeasure ∧
    Integrable (fun x ↦ ‖f x‖ * Real.log (2 + ‖f x‖)) circleMeasure

 

def symmetricPartialSum (f : Torus → ℂ) (N : ℕ) (x : Torus) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x

 

 

instance : IsProbabilityMeasure circleMeasure := by
  unfold circleMeasure
  infer_instance

@[simp] theorem circleMeasure_univ : circleMeasure Set.univ = 1 :=
  measure_univ

 
theorem fourier_of_real (k : ℤ) (x : ℝ) :
    fourier k (x : Torus) = Complex.exp (Complex.I * (k : ℂ) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

 
theorem fourierCoeff_eq_integral (f : Torus → ℂ) (k : ℤ) :
    fourierCoeff f k = ∫ x, f x * fourier (-k) x ∂circleMeasure := by
  simp only [fourierCoeff, circleMeasure, smul_eq_mul, mul_comm]

 

theorem fourierCoeff_eq_normalized_intervalIntegral (f : Torus → ℂ) (k : ℤ) :
    fourierCoeff f k = (1 / (2 * Real.pi) : ℝ) •
      ∫ x in (0 : ℝ)..(2 * Real.pi),
        f (x : Torus) * Complex.exp (-(Complex.I * (k : ℂ) * (x : ℂ))) := by
  rw [fourierCoeff_eq_intervalIntegral f k 0]
  simp only [zero_add, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [fourier_of_real]
  simp only [Int.cast_neg, mul_neg, mul_comm]

 
theorem orliczDensity_nonneg (z : ℂ) :
    0 ≤ ‖z‖ * Real.log (2 + ‖z‖) := by
  apply mul_nonneg (norm_nonneg _)
  apply Real.log_nonneg
  linarith [norm_nonneg z]

 
theorem MemLLogL.integrable {f : Torus → ℂ} (hf : MemLLogL f) :
    Integrable f circleMeasure := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (hf.2.div_const (Real.log 2)).mono' hf.1
  refine Filter.Eventually.of_forall fun x ↦ ?_
  apply (le_div_iff₀ hlog).2
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by norm_num) (le_add_of_nonneg_right (norm_nonneg _)))
    (norm_nonneg _)

 
theorem MemLLogL.congr_ae {f g : Torus → ℂ} (hf : MemLLogL f)
    (hfg : f =ᵐ[circleMeasure] g) : MemLLogL g := by
  refine ⟨hf.1.congr hfg, hf.2.congr ?_⟩
  filter_upwards [hfg] with x hx
  rw [hx]

 

theorem continuous_symmetricPartialSum (f : Torus → ℂ) (N : ℕ) :
    Continuous (symmetricPartialSum f N) := by
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (fourier k).continuous

theorem measurable_symmetricPartialSum (f : Torus → ℂ) (N : ℕ) :
    Measurable (symmetricPartialSum f N) :=
  (continuous_symmetricPartialSum f N).measurable

 
theorem symmetricPartialSum_congr_ae {f g : Torus → ℂ}
    (hfg : f =ᵐ[circleMeasure] g) (N : ℕ) (x : Torus) :
    symmetricPartialSum f N x = symmetricPartialSum g N x := by
  have hcoeff : fourierCoeff f = fourierCoeff g := fourierCoeff_congr_ae hfg
  simp only [symmetricPartialSum, hcoeff]

@[simp] theorem symmetricPartialSum_zero (N : ℕ) (x : Torus) :
    symmetricPartialSum (fun _ ↦ 0) N x = 0 := by
  simp [symmetricPartialSum, fourierCoeff]

 
@[simp] theorem symmetricPartialSum_cutoff_zero (f : Torus → ℂ) (x : Torus) :
    symmetricPartialSum f 0 x = fourierCoeff f 0 := by
  simp [symmetricPartialSum]

theorem symmetricPartialSum_add {f g : Torus → ℂ}
    (hf : Integrable f circleMeasure) (hg : Integrable g circleMeasure)
    (N : ℕ) (x : Torus) :
    symmetricPartialSum (f + g) N x =
      symmetricPartialSum f N x + symmetricPartialSum g N x := by
  simp only [symmetricPartialSum, fourierCoeff.add hf hg, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]

theorem symmetricPartialSum_const_mul (f : Torus → ℂ) (c : ℂ)
    (N : ℕ) (x : Torus) :
    symmetricPartialSum (fun y ↦ c * f y) N x = c * symmetricPartialSum f N x := by
  simp only [symmetricPartialSum, fourierCoeff.const_mul, Finset.mul_sum, mul_assoc]

 
theorem norm_fourierCoeff_le (f : Torus → ℂ) (k : ℤ) :
    ‖fourierCoeff f k‖ ≤ ∫ x, ‖f x‖ ∂circleMeasure := by
  calc
    ‖fourierCoeff f k‖ ≤ ∫ x, ‖fourier (-k) x * f x‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ ∂circleMeasure := by
      congr 1
      funext x
      simp [fourier_apply, Circle.norm_coe]

 

theorem norm_symmetricPartialSum_le (f : Torus → ℂ) (N : ℕ) (x : Torus) :
    ‖symmetricPartialSum f N x‖ ≤
      (2 * N + 1 : ℕ) * ∫ y, ‖f y‖ ∂circleMeasure := by
  calc
    ‖symmetricPartialSum f N x‖ ≤
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f k * fourier k x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ y, ‖f y‖ ∂circleMeasure := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using
        norm_fourierCoeff_le f k
    _ = (2 * N + 1 : ℕ) * ∫ y, ‖f y‖ ∂circleMeasure := by
      simp only [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
      congr 2
      omega

 

 

theorem exists_measurable_null_of_ae {p : Torus → Prop}
    (hp : ∀ᵐ x ∂circleMeasure, p x) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E, p x := by
  obtain ⟨E, hsub, hE, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨E, hE, hzero, ?_⟩
  intro x hx
  by_contra h
  exact hx (hsub h)

 

theorem ae_convergence_iff_exists_measurable_null (f : Torus → ℂ) :
    (∀ᵐ x ∂circleMeasure,
        Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x))) ↔
      ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧
        ∀ x ∉ E, Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) := by
  refine ⟨exists_measurable_null_of_ae, ?_⟩
  rintro ⟨E, _, hzero, hconv⟩
  have hE : ∀ᵐ x ∂circleMeasure, x ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hzero
  filter_upwards [hE] with x hx using hconv x hx

 

 

theorem tendsto_symmetricPartialSum_of_summable (f : C(Torus, ℂ))
    (hf : Summable (fourierCoeff f)) (x : Torus) :
    Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) := by
  have h := has_pointwise_sum_fourier_series_of_summable hf x
  exact h.comp (Finset.tendsto_Icc_neg (R := ℤ))

 

 
theorem fourierCoeff_tsum {F : ℕ → Torus → ℂ}
    (hF : ∀ j, Integrable (F j) circleMeasure)
    (hsum : Summable (fun j ↦ ∫ x, ‖F j x‖ ∂circleMeasure)) (k : ℤ) :
    fourierCoeff (fun x ↦ ∑' j, F j x) k = ∑' j, fourierCoeff (F j) k := by
  have hint : ∀ j, Integrable (fun x ↦ fourier (-k) x * F j x) circleMeasure :=
    fun j ↦ (hF j).fourier_smul (-k)
  have hs : Summable (fun j ↦ ∫ x, ‖fourier (-k) x * F j x‖ ∂circleMeasure) := by
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, one_mul] using hsum
  simpa only [fourierCoeff, circleMeasure, smul_eq_mul, tsum_mul_left] using
    (integral_tsum_of_summable_integral_norm hint hs).symm

 

theorem symmetricPartialSum_tsum {F : ℕ → Torus → ℂ}
    (hF : ∀ j, Integrable (F j) circleMeasure)
    (hsum : Summable (fun j ↦ ∫ x, ‖F j x‖ ∂circleMeasure)) (N : ℕ) (x : Torus) :
    symmetricPartialSum (fun y ↦ ∑' j, F j y) N x =
      ∑' j, symmetricPartialSum (F j) N x := by
  simp only [symmetricPartialSum, fourierCoeff_tsum hF hsum, ← tsum_mul_right]
  symm
  apply Summable.tsum_finsetSum
  intro k _
  exact (hsum.of_norm_bounded (fun j ↦ norm_fourierCoeff_le (F j) k)).mul_right _

 

theorem tendsto_symmetricPartialSum_tsum {F : ℕ → Torus → ℂ}
    (hF : ∀ j, Integrable (F j) circleMeasure)
    (hsum : Summable (fun j ↦ ∫ y, ‖F j y‖ ∂circleMeasure))
    (x : Torus) {b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ j N, ‖symmetricPartialSum (F j) N x‖ ≤ b j)
    (hlim : ∀ j, Tendsto (fun N : ℕ ↦ symmetricPartialSum (F j) N x)
      atTop (𝓝 (F j x))) :
    Tendsto (fun N : ℕ ↦ symmetricPartialSum (fun y ↦ ∑' j, F j y) N x)
      atTop (𝓝 (∑' j, F j x)) := by
  have h := tendsto_tsum_of_dominated_convergence hb hlim
    (Filter.Eventually.of_forall (fun N j ↦ hbound j N))
  simpa only [symmetricPartialSum_tsum hF hsum, tsum_apply] using h

 

 
theorem mass_logMinus_le {m a : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) :
    m * max 0 (-Real.log m) ≤ a * m + Real.exp (-a) := by
  rcases eq_or_lt_of_le hm with rfl | hm
  · simp [Real.exp_nonneg]
  by_cases hlog : 0 ≤ -Real.log m
  · rw [max_eq_right hlog]
    have h := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (-a)) hm)
    rw [Real.log_div (Real.exp_ne_zero _) hm.ne', Real.log_exp] at h
    have h' := mul_le_mul_of_nonneg_right h hm.le
    simp only [sub_mul, div_mul_cancel₀ _ hm.ne', one_mul] at h'
    nlinarith
  · rw [max_eq_left (le_of_not_ge hlog), mul_zero]
    positivity

 

theorem summable_mass_logMinus {m : ℕ → ℝ} (hm : ∀ j, 0 ≤ m j)
    (hweight : Summable (fun j ↦ (2 : ℝ) ^ j * m j)) :
    Summable (fun j ↦ m j * max 0 (-Real.log (m j))) := by
  have hexp : Summable (fun j : ℕ ↦ Real.exp (-((2 : ℝ) ^ j))) := by
    have hpow : ∀ j : ℕ, (j : ℝ) ≤ (2 : ℝ) ^ j := by
      intro j
      exact_mod_cast (Nat.lt_two_pow_self (n := j)).le
    simpa only [neg_one_mul] using
      Real.summable_exp_nat_mul_of_ge (c := -1) (by norm_num) hpow
  refine (hweight.add hexp).of_nonneg_of_le (fun j ↦ ?_) (fun j ↦ ?_)
  · exact mul_nonneg (hm j) (le_max_left _ _)
  · exact mass_logMinus_le (hm j) (by positivity)

 

theorem summable_layerCost {m : ℕ → ℝ} (hm : ∀ j, 0 ≤ m j)
    (hweight : Summable (fun j ↦ (2 : ℝ) ^ j * m j)) :
    Summable (fun j ↦ m j * ((2 : ℝ) ^ (j + 1) + max 0 (-Real.log (m j)))) := by
  apply ((hweight.mul_left 2).add (summable_mass_logMinus hm hweight)).congr
  intro j
  simp only [pow_succ]
  ring

 

 
def heightLayerSet (f : Torus → ℂ) (j : ℕ) : Set Torus :=
  {x | Real.exp ((2 : ℝ) ^ (j + 1)) ≤ ‖f x‖ ∧
    ‖f x‖ < Real.exp ((2 : ℝ) ^ (j + 2))}

 
def heightLayer (f : Torus → ℂ) (j : ℕ) : Torus → ℂ :=
  (heightLayerSet f j).indicator f

 
def heightLayerMass (f : Torus → ℂ) (j : ℕ) : ℝ :=
  ∫ x in heightLayerSet f j, ‖f x‖ ∂circleMeasure

theorem heightLayerSet_nullMeasurable {f : Torus → ℂ} (hf : MemLLogL f) (j : ℕ) :
    NullMeasurableSet (heightLayerSet f j) circleMeasure := by
  exact (nullMeasurableSet_le aemeasurable_const hf.1.norm.aemeasurable).inter
    (nullMeasurableSet_lt hf.1.norm.aemeasurable aemeasurable_const)

theorem heightLayerSet_pairwise_disjoint (f : Torus → ℂ) :
    Pairwise (fun i j ↦ Disjoint (heightLayerSet f i) (heightLayerSet f j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hmono : Monotone (fun n : ℕ ↦ Real.exp ((2 : ℝ) ^ n)) :=
    Real.exp_monotone.comp (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge ((hmono (by omega : i + 2 ≤ j + 1)).trans hxj.1)) hxi.2
  · exact (not_lt_of_ge ((hmono (by omega : j + 2 ≤ i + 1)).trans hxi.1)) hxj.2

theorem MemLLogL.heightLayer_integrable {f : Torus → ℂ} (hf : MemLLogL f) (j : ℕ) :
    Integrable (heightLayer f j) circleMeasure :=
  hf.integrable.indicator₀ (heightLayerSet_nullMeasurable hf j)

theorem heightLayerMass_nonneg (f : Torus → ℂ) (j : ℕ) :
    0 ≤ heightLayerMass f j :=
  integral_nonneg (fun x ↦ norm_nonneg (f x))

theorem heightLayerMass_eq_integral_norm {f : Torus → ℂ} (hf : MemLLogL f) (j : ℕ) :
    heightLayerMass f j = ∫ x, ‖heightLayer f j x‖ ∂circleMeasure := by
  rw [heightLayerMass, ← integral_indicator₀ (heightLayerSet_nullMeasurable hf j)]
  simp only [heightLayer, norm_indicator_eq_indicator_norm]

 

theorem MemLLogL.summable_weighted_heightLayerMass {f : Torus → ℂ} (hf : MemLLogL f) :
    Summable (fun j ↦ (2 : ℝ) ^ (j + 1) * heightLayerMass f j) := by
  have hD : Summable (fun j ↦ ∫ x in heightLayerSet f j,
      ‖f x‖ * Real.log (2 + ‖f x‖) ∂circleMeasure) :=
    (hasSum_integral_iUnion_ae (heightLayerSet_nullMeasurable hf)
      ((heightLayerSet_pairwise_disjoint f).mono (fun _ _ h ↦ h.aedisjoint))
      hf.2.integrableOn).summable
  refine hD.of_nonneg_of_le
    (fun j ↦ mul_nonneg (by positivity) (heightLayerMass_nonneg f j)) ?_
  intro j
  rw [heightLayerMass, ← integral_const_mul]
  apply integral_mono_ae (hf.integrable.norm.integrableOn.const_mul _) hf.2.integrableOn
  filter_upwards [ae_restrict_mem₀ (heightLayerSet_nullMeasurable hf j)] with x hx
  have hlog : (2 : ℝ) ^ (j + 1) ≤ Real.log (2 + ‖f x‖) := by
    calc
      (2 : ℝ) ^ (j + 1) = Real.log (Real.exp ((2 : ℝ) ^ (j + 1))) := (Real.log_exp _).symm
      _ ≤ Real.log (2 + ‖f x‖) :=
        Real.log_le_log (Real.exp_pos _) (hx.1.trans (by linarith))
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlog (norm_nonneg (f x))

 
theorem MemLLogL.summable_heightLayer_norm {f : Torus → ℂ} (hf : MemLLogL f) :
    Summable (fun j ↦ ∫ x, ‖heightLayer f j x‖ ∂circleMeasure) := by
  simp_rw [← heightLayerMass_eq_integral_norm hf]
  apply hf.summable_weighted_heightLayerMass.of_nonneg_of_le
    (heightLayerMass_nonneg f)
  intro j
  exact le_mul_of_one_le_left (heightLayerMass_nonneg f j)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

 

theorem MemLLogL.summable_heightLayerCost {f : Torus → ℂ} (hf : MemLLogL f) :
    Summable (fun j ↦ heightLayerMass f j *
      ((2 : ℝ) ^ (j + 2) + max 0 (-Real.log (heightLayerMass f j)))) := by
  have hw0 : Summable (fun j ↦ (2 : ℝ) ^ j * heightLayerMass f j) := by
    apply (hf.summable_weighted_heightLayerMass.mul_left (1 / 2 : ℝ)).congr
    intro j
    simp only [pow_succ]
    ring
  apply ((hf.summable_weighted_heightLayerMass.mul_left 2).add
    (summable_mass_logMinus (heightLayerMass_nonneg f) hw0)).congr
  intro j
  simp only [pow_succ]
  ring

 
def boundedPart (f : Torus → ℂ) : Torus → ℂ :=
  {x | ‖f x‖ < Real.exp 2}.indicator f

theorem MemLLogL.boundedPart_integrable {f : Torus → ℂ} (hf : MemLLogL f) :
    Integrable (boundedPart f) circleMeasure :=
  hf.integrable.indicator₀ (nullMeasurableSet_lt hf.1.norm.aemeasurable aemeasurable_const)

theorem norm_boundedPart_le (f : Torus → ℂ) (x : Torus) :
    ‖boundedPart f x‖ ≤ Real.exp 2 := by
  by_cases hx : ‖f x‖ < Real.exp 2
  · simpa [boundedPart, hx] using hx.le
  · simp [boundedPart, hx, Real.exp_nonneg]

theorem norm_heightLayer_le (f : Torus → ℂ) (j : ℕ) (x : Torus) :
    ‖heightLayer f j x‖ ≤ Real.exp ((2 : ℝ) ^ (j + 2)) := by
  by_cases hx : x ∈ heightLayerSet f j
  · simpa only [heightLayer, Set.indicator_of_mem hx] using hx.2.le
  · simp only [heightLayer, Set.indicator_of_notMem hx, norm_zero]
    exact Real.exp_nonneg _

 
theorem mem_boundedPart_or_heightLayerSet (f : Torus → ℂ) (x : Torus) :
    ‖f x‖ < Real.exp 2 ∨ ∃ j : ℕ, x ∈ heightLayerSet f j := by
  classical
  by_cases hlo : ‖f x‖ < Real.exp 2
  · exact Or.inl hlo
  right
  have hex : ∃ n : ℕ, ‖f x‖ < Real.exp ((2 : ℝ) ^ (n + 1)) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖f x‖
    refine ⟨n, ?_⟩
    have hp : (n + 1 : ℝ) < (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := n + 1))
    have he := Real.add_one_le_exp ((2 : ℝ) ^ (n + 1))
    linarith
  have hn : 0 < Nat.find hex := by
    by_contra hn
    have hn0 : Nat.find hex = 0 := by omega
    exact hlo (by simpa only [hn0, zero_add, pow_one] using Nat.find_spec hex)
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex))
  · have hidx : Nat.find hex - 1 + 2 = Nat.find hex + 1 := by omega
    simpa only [hidx] using Nat.find_spec hex

 

theorem boundedPart_add_tsum_heightLayer (f : Torus → ℂ) (x : Torus) :
    boundedPart f x + ∑' j, heightLayer f j x = f x := by
  classical
  by_cases hlo : ‖f x‖ < Real.exp 2
  · have hz : ∀ j, heightLayer f j x = 0 := by
      intro j
      have hnot : x ∉ heightLayerSet f j := by
        intro hx
        have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
          simpa only [pow_one] using
            (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone
              (by omega : 1 ≤ j + 1)
        exact (not_le_of_gt hlo) ((Real.exp_le_exp.mpr hp).trans hx.1)
      exact Set.indicator_of_notMem hnot f
    simp [boundedPart, hlo, hz]
  · obtain ⟨j, hj⟩ := (mem_boundedPart_or_heightLayerSet f x).resolve_left hlo
    have hs : (∑' k, heightLayer f k x) = heightLayer f j x := by
      apply tsum_eq_single j
      intro k hkj
      have hk : x ∉ heightLayerSet f k := by
        intro hk
        exact Set.disjoint_left.mp (heightLayerSet_pairwise_disjoint f hkj) hk hj
      exact Set.indicator_of_notMem hk f
    rw [hs]
    simp [boundedPart, hlo, heightLayer, hj]

 

theorem MemLLogL.symmetricPartialSum_heightDecomposition {f : Torus → ℂ}
    (hf : MemLLogL f) (N : ℕ) (x : Torus) :
    symmetricPartialSum f N x = symmetricPartialSum (boundedPart f) N x +
      ∑' j, symmetricPartialSum (heightLayer f j) N x := by
  have htail : (fun y ↦ ∑' j, heightLayer f j y) = f - boundedPart f := by
    funext y
    have h := boundedPart_add_tsum_heightLayer f y
    change (∑' j, heightLayer f j y) = f y - boundedPart f y
    exact eq_sub_of_add_eq' h
  have hint : Integrable (fun y ↦ ∑' j, heightLayer f j y) circleMeasure := by
    rw [htail]
    exact hf.integrable.sub hf.boundedPart_integrable
  have hdecomp : f = boundedPart f + (fun y ↦ ∑' j, heightLayer f j y) := by
    funext y
    exact (boundedPart_add_tsum_heightLayer f y).symm
  calc
    symmetricPartialSum f N x =
        symmetricPartialSum (boundedPart f + (fun y ↦ ∑' j, heightLayer f j y)) N x :=
      congrArg (fun g ↦ symmetricPartialSum g N x) hdecomp
    _ = symmetricPartialSum (boundedPart f) N x +
        symmetricPartialSum (fun y ↦ ∑' j, heightLayer f j y) N x :=
      symmetricPartialSum_add hf.boundedPart_integrable hint N x
    _ = symmetricPartialSum (boundedPart f) N x +
        ∑' j, symmetricPartialSum (heightLayer f j) N x := by
      rw [symmetricPartialSum_tsum hf.heightLayer_integrable hf.summable_heightLayer_norm]

end FourierLLogL

end

end OAI
