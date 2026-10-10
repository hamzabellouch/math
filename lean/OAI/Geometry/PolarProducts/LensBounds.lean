import OAI.Geometry.PolarProducts.TipEstimates

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem exists_inner_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (t v : ℝ),
      (v : ℂ)+(t : ℂ)*I ∈ D → 0 ≤ v → rho t v ≤ a →
      (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
        C*(k : ℝ)*a^(2*k-2) := by
  let Cset := F '' Metric.closedBall (0 : ℂ) a
  have hCD : Cset ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ a := by simpa using hw
    simpa using hw'.trans_lt ha1
  have hCc : IsCompact Cset := (isCompact_closedBall (0 : ℂ) a).image_of_continuousOn
    (continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall ha1.le))
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (analyticOnNhd_g.deriv.continuousOn.mono hCD)
  obtain ⟨B, hB0, hB⟩ := isBounded_D.exists_pos_norm_le
  let M := max N 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨B*M^2, mul_nonneg hB0.le (sq_nonneg _), ?_⟩
  intro k t v hz hv hra
  have hvB : v ≤ B := by
    have hh := (abs_re_le_norm ((v : ℂ)+(t : ℂ)*I)).trans (hB _ hz)
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self, add_zero, abs_of_nonneg hv] using hh
  have hpi : IntervalIntegrable (fun h : ℝ => a^(2*k-2)*M^2) volume 0 v := intervalIntegrable_const
  have hii := integrable_density hz k
  have hcmp : ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤ v*(a^(2*k-2)*M^2) := by
    have hh : ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
        ∫ h in 0..v, a^(2*k-2)*M^2 := by
      apply intervalIntegral.integral_mono_on hv hii hpi
      intro h hh
      have hhz := horizontal_segment_mem hz hv hh
      have hr : rho t h ≤ a := ((horizontal_radius_strictMono hz hv).monotoneOn hh
        (right_mem_Icc.mpr hv) hh.2).trans hra
      have hc : (h : ℂ)+(t : ℂ)*I ∈ Cset :=
        ⟨g _, by simpa [rho] using hr, F_g hhz⟩
      have hn : ‖deriv g ((h : ℂ)+(t : ℂ)*I)‖ ≤ M := (hN _ hc).trans (le_max_left _ _)
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hr _) (pow_le_pow_left₀ (norm_nonneg _) hn _)
        (sq_nonneg _) (pow_nonneg ha0 _)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  calc
    _ ≤ (k : ℝ)*(v*(a^(2*k-2)*M^2)) := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg k)
    _ ≤ (k : ℝ)*(B*(a^(2*k-2)*M^2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hvB (mul_nonneg (pow_nonneg ha0 _) (sq_nonneg _))) (Nat.cast_nonneg k)
    _ = _ := by ring

theorem exists_uniform_error_bound {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (t v : ℝ),
      (v : ℂ)+(t : ℂ)*I ∈ D → 0 ≤ v →
      (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
      Real.pi/4*(rho t v)^(2*k) + C*(k : ℝ)*a^(2*k-2) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨C, hC, hinner⟩ := exists_inner_bound ha0 ha1
  refine ⟨C, hC, ?_⟩
  intro k hk t v hz hv
  have hE : 0 ≤ Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by positivity
  have hCterm : 0 ≤ C*(k : ℝ)*a^(2*k-2) := by positivity
  have hR : 0 ≤ Real.pi/4*(rho t v)^(2*k) := by
    exact mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
  by_cases hr : rho t v ≤ a
  · exact (hinner k t v hz hv hr).trans (by linarith)
  by_cases hl : a ≤ rho t 0
  · have hh := outer_integral_bound hk hz (le_refl 0) hv ha hl
    have hn : 0 ≤ Real.pi/4*(rho t 0)^(2*k) :=
      mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
    nlinarith
  have haI : a ∈ Icc (rho t 0) (rho t v) := ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩
  obtain ⟨u, hu, heu⟩ := intermediate_value_Icc hv (continuousOn_rho hz hv) haI
  have huD := horizontal_segment_mem hz hv hu
  have hleft := hinner k t u huD hu.1 heu.le
  have hright := outer_integral_bound hk hz hu.1 hu.2 ha heu.ge
  have hIuv : IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume u v := by
    exact (integrable_density hz k).mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le hv]) right_mem_uIcc)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (integrable_density huD k) hIuv
  have hn : 0 ≤ Real.pi/4*(rho t u)^(2*k) :=
    mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
  rw [← hadd]
  nlinarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem J_div_order {k : ℕ} (hk : 1 ≤ k) {v t : ℝ} (hv : 0 ≤ v) :
    |J k v t|/(k : ℝ) = (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [abs_of_nonneg (J_nonneg hv k), J]
  field_simp

theorem rho_neg {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) : rho t (-v) = rho t v := by
  have he : -(starRingEnd ℂ) ((v : ℂ)+(t : ℂ)*I) = ((-v : ℝ) : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  rw [rho, rho, ← he, g_neg_conj hz]
  simp

def excess (k : ℕ) (z : ℂ) : ℝ := |J k z.re z.im|/(k : ℝ) - Real.pi/4*‖g z‖^(2*k)

def epsilon (k : ℕ) : ℝ := max 0 (sSup (excess k '' D))

theorem epsilon_nonneg (k : ℕ) : 0 ≤ epsilon k := le_max_left _ _

theorem exists_excess_bound {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ D,
      excess k z ≤ C*(k : ℝ)*a^(2*k-2) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_error_bound ha ha1
  refine ⟨C, hC, ?_⟩
  intro k hk z hz
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa only [re_add_im] using hz
  have hpos (v t : ℝ) (hv : 0 ≤ v) (hh : (v : ℂ)+(t : ℂ)*I ∈ D) :
      |J k v t|/(k : ℝ) - Real.pi/4*(rho t v)^(2*k) ≤
        C*(k : ℝ)*a^(2*k-2) + Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
    rw [J_div_order hk hv]
    linarith [hb k hk t v hh hv]
  by_cases hv : 0 ≤ z.re
  · simpa only [excess, rho, re_add_im] using hpos z.re z.im hv hz'
  · have hnz : ((-z.re : ℝ) : ℂ)+(z.im : ℂ)*I ∈ D := by
      convert neg_conj_mem_D hz using 1
      apply Complex.ext <;> simp
    have hh := hpos (-z.re) z.im (by linarith) hnz
    rw [J_neg hz', abs_neg, rho_neg hz'] at hh
    simpa only [excess, rho, re_add_im] using hh

theorem bddAbove_excess {k : ℕ} (hk : 1 ≤ k) : BddAbove (excess k '' D) := by
  obtain ⟨C, _, hC⟩ := exists_excess_bound (a := 3/4) (by norm_num) (by norm_num)
  refine ⟨C*(k : ℝ)*(3/4)^(2*k-2) + Real.pi^3/Real.sqrt (tailSlope (3/4))*(1+Real.pi/Real.exp 1), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC k hk z hz

theorem excess_le_epsilon {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ D) : excess k z ≤ epsilon k :=
  (le_csSup (bddAbove_excess hk) (mem_image_of_mem _ hz)).trans (le_max_right _ _)

theorem epsilon_le_of_excess_le {k : ℕ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ z ∈ D, excess k z ≤ B) :
    epsilon k ≤ B := by
  apply max_le hB
  apply csSup_le ⟨excess k 0, mem_image_of_mem _ zero_mem_D⟩
  rintro _ ⟨z, hz, rfl⟩
  exact h z hz

theorem tendsto_inner_error {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (C : ℝ) :
    Tendsto (fun k : ℕ => C*(k : ℝ)*a^(2*k-2)) atTop (𝓝 0) := by
  have hq : |a^2| < 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq).const_mul (C/a^2)
  simp only [pow_one, mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hp : a^(2*k-2)*a^2 = (a^2)^k := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ 2*k), pow_mul]
  have ha2 : a^2 ≠ 0 := pow_ne_zero _ ha.ne'
  apply mul_right_cancel₀ ha2
  calc
    ((C/a^2)*((k : ℝ)*(a^2)^k))*a^2 = C*(k : ℝ)*(a^2)^k := by field_simp
    _ = C*(k : ℝ)*(a^(2*k-2)*a^2) := by rw [hp]
    _ = C*(k : ℝ)*a^(2*k-2)*a^2 := by ring

theorem exists_small_tail (e : ℝ) (he : 0 < e) :
    ∃ a ∈ Ioo (1/2 : ℝ) 1,
      Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) < e := by
  let H := Real.pi^3*(1+Real.pi/Real.exp 1)
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨a, ha, hL⟩ := exists_tail_cutoff ((H/e)^2)
  have ha0 : 0 < a := by linarith [ha.1]
  have hs : 0 < Real.sqrt (tailSlope a) := Real.sqrt_pos.2 (tailSlope_pos ha0 ha.2)
  have hq : H/e < Real.sqrt (tailSlope a) := by
    rw [← Real.sqrt_sq (div_nonneg hH.le he.le)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hL
  refine ⟨a, ha, ?_⟩
  have hh : H < e * Real.sqrt (tailSlope a) := by
    have := (div_lt_iff₀ he).mp hq
    nlinarith
  have hh' := (div_lt_iff₀ hs).mpr hh
  convert hh' using 1
  first | rfl | (dsimp only [H]; ring)

theorem tendsto_epsilon : Tendsto epsilon atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun k => hc.trans_le (epsilon_nonneg k))
  · intro e he
    obtain ⟨a, ha, htail⟩ := exists_small_tail (e/2) (by linarith)
    obtain ⟨C, hC, hbound⟩ := exists_excess_bound ha.1.le ha.2
    have ha0 : 0 < a := by linarith [ha.1]
    have ht := (tendsto_inner_error ha0 ha.2 C).eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < e/2))
    filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with k hinner hk
    have hE := epsilon_le_of_excess_le (k := k)
      (B := C*(k : ℝ)*a^(2*k-2)+Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1))
      (by positivity) (hbound k hk)
    linarith

theorem uniform_slice {k : ℕ} (hk : 1 ≤ k) {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    |J k v t|/(k : ℝ) ≤ Real.pi/4*‖g ((v : ℂ)+(t : ℂ)*I)‖^(2*k)+epsilon k := by
  have hh := excess_le_epsilon hk hz
  have hre : ((v : ℂ)+(t : ℂ)*I).re = v := by simp
  have him : ((v : ℂ)+(t : ℂ)*I).im = t := by simp
  simp only [excess, hre, him] at hh
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI
