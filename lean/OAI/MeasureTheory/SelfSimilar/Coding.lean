import OAI.MeasureTheory.SelfSimilar.Bernoulli

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension
namespace Coding
open Filter Set
open scoped Topology

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

def shift (ω : ℕ → ι) (n : ℕ) : ι := ω (n+1)

def slope (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, S.ratio (ω j)

def term (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  slope S ω n * S.offset (ω n)

noncomputable def point (S : System ι) (ω : ℕ → ι) : ℝ := ∑' n, term S ω n

omit [Nonempty ι] in
theorem slope_zero (S : System ι) (ω : ℕ → ι) : slope S ω 0 = 1 := by simp [slope]

omit [Nonempty ι] in
theorem slope_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = slope S ω n * S.ratio (ω n) := by
  simp [slope, Finset.prod_range_succ]

omit [Nonempty ι] in
theorem slope_shift (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = S.ratio (ω 0) * slope S (shift ω) n := by
  simp only [slope, Finset.prod_range_succ', shift]
  ring

omit [Nonempty ι] in
theorem abs_slope_le (S : System ι) (ω : ℕ → ι) {c : ℝ}
    (hc : 0 ≤ c) (hr : ∀ i, |S.ratio i| ≤ c) (n : ℕ) :
    |slope S ω n| ≤ c^n := by
  induction n with
  | zero => simp [slope_zero]
  | succ n ih =>
    rw [slope_succ, abs_mul, pow_succ]
    exact mul_le_mul ih (hr _) (abs_nonneg _) (pow_nonneg hc _)

omit [Nonempty ι] in
theorem abs_term_le (S : System ι) (ω : ℕ → ι) {c T : ℝ}
    (hc : 0 ≤ c) (_hT : 0 ≤ T) (hr : ∀ i, |S.ratio i| ≤ c)
    (ht : ∀ i, |S.offset i| ≤ T) (n : ℕ) : |term S ω n| ≤ c^n*T := by
  rw [term, abs_mul]
  exact mul_le_mul (abs_slope_le S ω hc hr n) (ht _) (abs_nonneg _) (pow_nonneg hc n)

theorem term_summable (S : System ι) (ω : ℕ → ι) : Summable (term S ω) := by
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hc.le hc1).mul_right T)
  intro n
  simpa only [Real.norm_eq_abs] using abs_term_le S ω hc.le hT hr ht n

theorem point_shift (S : System ι) (ω : ℕ → ι) :
    point S ω = S.affine (ω 0) (point S (shift ω)) := by
  rw [point, (term_summable S ω).tsum_eq_zero_add]
  have he : (fun n => term S ω (n+1)) = fun n => S.ratio (ω 0)*term S (shift ω) n := by
    funext n
    simp only [term, slope_shift, shift]
    ring
  rw [he, tsum_mul_left]
  simp only [term, slope_zero, one_mul, System.affine, point]
  ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Nonempty ι] in
theorem slope_measurable (S : System ι) (n : ℕ) : Measurable (fun ω => slope S ω n) := by
  apply Finset.measurable_prod
  intro j hj
  exact (measurable_of_finite _).comp (measurable_pi_apply j)

omit [Nonempty ι] in
theorem term_measurable (S : System ι) (n : ℕ) : Measurable (fun ω => term S ω n) :=
  (slope_measurable S n).mul ((measurable_of_finite _).comp (measurable_pi_apply n))

theorem point_measurable (S : System ι) : Measurable (point S) := by
  apply measurable_of_tendsto_metrizable
    (fun n => Finset.measurable_sum (s := Finset.range n) (fun j _ => term_measurable S j))
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (term_summable S ω).hasSum.tendsto_sum_nat

noncomputable def symbolMeasure (S : System ι) : Measure ι :=
  ∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i

instance symbolMeasure_probability (S : System ι) : IsProbabilityMeasure (symbolMeasure S) where
  measure_univ := by
    simp only [symbolMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => S.weight_nonneg i), S.weight_sum]
    simp

noncomputable def addressMeasure (S : System ι) : Measure (ℕ → ι) :=
  Measure.infinitePi fun _ : ℕ => symbolMeasure S

instance addressMeasure_probability (S : System ι) : IsProbabilityMeasure (addressMeasure S) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => symbolMeasure S))

noncomputable def law (S : System ι) : Measure ℝ := (addressMeasure S).map (point S)

instance law_probability (S : System ι) : IsProbabilityMeasure (law S) :=
  (Measure.isProbabilityMeasure_map_iff (point_measurable S).aemeasurable).2 inferInstance

theorem head_tail_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S (shift ω))) =
      (symbolMeasure S).prod (law S) := by
  have h := congrArg (Measure.map (Prod.map id (point S)))
    (Bernoulli.head_tail_law (symbolMeasure S))
  rw [Measure.map_map (measurable_id.prodMap (point_measurable S))
      ((measurable_pi_apply 0).prodMk Bernoulli.shift_measurable)] at h
  rw [← Measure.map_prod_map _ _ measurable_id (point_measurable S), Measure.map_id] at h
  exact h

theorem law_selfSimilar (S : System ι) : S.SelfSimilar (law S) := by
  classical
  let f : ι × ℝ → ℝ := fun z => S.affine z.1 z.2
  have hf : Measurable f := by
    exact ((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd |>.add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp Bernoulli.shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = point S :=
    funext fun ω => (point_shift S ω).symm
  rw [he] at hh
  change law S = _ at hh
  change law S = _
  conv_lhs => rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.prod_smul_left, Measure.map_smul _ hf.aemeasurable, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

end Coding
end EntropyRateDimension

end

end OAI
