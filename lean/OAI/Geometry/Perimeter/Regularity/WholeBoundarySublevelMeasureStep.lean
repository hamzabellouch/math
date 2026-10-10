import OAI.Geometry.Perimeter.Regularity.TendstoLintegralNormOfL2

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
namespace RPISingularHarnack
open RPI RPI.Boundary Classical

theorem wholeBoundary_sublevel_measure_step {n : ℕ} (hn : 2 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hSob : WholeBoundarySobolev E h G) (hSuper : WholeBoundarySupersolution E G)
    (hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1)
    {p : ℝ} (hp : 1 < p) (hpk : (((n - 1 : ℕ) : ℝ) - 1) * p < (n - 1 : ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s r l k : ℝ, 0 < s → s < r → r ≤ 2 → 0 < l → l < k →
      (boundaryArea E).real (Metric.ball 0 s ∩ {x | h x < l}) ≤
        C * (k / ((r-s) * (k-l))) ^ p *
          ((boundaryArea E).real (Metric.ball 0 r ∩ {x | h x < k})) ^ p := by
  classical
  have hp0 : 0 ≤ p := (lt_trans zero_lt_one hp).le
  have hn1 : 1 < n := by omega
  obtain ⟨L, hL, hcut⟩ := exists_interior_cutoff_constant
  obtain ⟨C, hC, hsob⟩ := wholeBoundary_sublevel_sobolev hn hmin hSob hh01 (by norm_num : (0 : ℝ) < 3) hp hpk
  refine ⟨(C.toReal + 1) * (10 * L) ^ p, by positivity, ?_⟩
  intro s r l k hs hsr hr2 hl hlk
  have hk : 0 < k := hl.trans hlk
  have hd : 0 < (k-l)/2 := by linarith
  have hN : 0 < L / (r-s) := div_pos hL (sub_pos.mpr hsr)
  obtain ⟨η, hη, hcη, hsη, hη01, hηone, hηD⟩ := hcut n E s r hs hsr
  let μ := (boundaryArea E).restrict (Metric.ball 0 3)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn1 hmin 0 (by norm_num : (0 : ℝ) < 3)⟩
  let A := Metric.ball (0 : Euc n) s ∩ {x | h x < l}
  let B := Metric.ball (0 : Euc n) r ∩ {x | h x < k}
  have hm := (hSob 3 (by norm_num)).1.aestronglyMeasurable.aemeasurable
  have hAm : NullMeasurableSet A μ := measurableSet_ball.nullMeasurableSet.inter
    (nullMeasurableSet_lt hm aemeasurable_const)
  have hBm : NullMeasurableSet B μ := measurableSet_ball.nullMeasurableSet.inter
    (nullMeasurableSet_lt hm aemeasurable_const)
  have hAeq : μ A = boundaryArea E A := by
    change (boundaryArea E).restrict (Metric.ball 0 3) A = _
    rw [Measure.restrict_apply₀ hAm, inter_eq_left.mpr]
    exact fun x hx ↦ Metric.ball_subset_ball (by linarith : s ≤ 3) hx.1
  have hBeq : μ B = boundaryArea E B := by
    change (boundaryArea E).restrict (Metric.ball 0 3) B = _
    rw [Measure.restrict_apply₀ hBm, inter_eq_left.mpr]
    exact fun x hx ↦ Metric.ball_subset_ball (by linarith : r ≤ 3) hx.1
  have hAtop : boundaryArea E A ≠ ⊤ := hAeq ▸ measure_ne_top μ A
  have hBtop : boundaryArea E B ≠ ⊤ := hBeq ▸ measure_ne_top μ B
  have hlo : ENNReal.ofReal ((k-l)/2) ^ p * boundaryArea E A ≤
      ∫⁻ x, ENNReal.ofReal (η x ^ 2 * sublevelTest ((k-l)/2) k (h x)) ^ p ∂μ := by
    rw [← hAeq]
    calc
      _ = ∫⁻ x, A.indicator (fun _ ↦ ENNReal.ofReal ((k-l)/2) ^ p) x ∂μ := by
        rw [lintegral_indicator₀ hAm, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := lintegral_mono fun x ↦ by
        by_cases hx : x ∈ A
        · rw [indicator_of_mem hx, hηone x hx.1, one_pow, one_mul]
          apply ENNReal.rpow_le_rpow _ hp0
          apply ENNReal.ofReal_le_ofReal
          have H := sub_parameter_le_smoothPositive (s := k - h x) hd
          change k - h x - (k-l)/2 ≤ sublevelTest ((k-l)/2) k (h x) at H
          have hxl : h x < l := hx.2
          linarith
        · rw [indicator_of_notMem hx]
          exact bot_le
  have hsR := hsη.trans (Metric.ball_subset_ball (by linarith : r ≤ 3))
  have hl1 := wholeBoundary_sublevel_L1 hn1 hmin hSob hSuper hh01
    (by norm_num : (0 : ℝ) < 3) (by linarith : r ≤ 3) hd hk hN hη hcη hsη hη01 hηD
  have hso := hsob η hη hcη hsR ((k-l)/2) k hd hk.le
  have H : ENNReal.ofReal ((k-l)/2) ^ p * boundaryArea E A ≤
      C * (ENNReal.ofReal (5 * k * (L/(r-s))) * boundaryArea E B) ^ p := by
    exact hlo.trans (hso.trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hl1 hp0) (show (0 : ℝ≥0∞) ≤ C from bot_le)))
  have hRt : C * (ENNReal.ofReal (5 * k * (L/(r-s))) * boundaryArea E B) ^ p ≠ ⊤ :=
    ENNReal.mul_ne_top hC (ENNReal.rpow_ne_top_of_nonneg hp0
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop))
  have Hr := ENNReal.toReal_mono hRt H
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hd.le, ENNReal.toReal_ofReal (show 0 ≤ 5 * k * (L/(r-s)) by positivity)] at Hr
  exact (RPIIteration.sublevel_step_division hd (by positivity) Hr).trans
    (RPIIteration.sublevel_step_factor ENNReal.toReal_nonneg hL hk hlk hsr ENNReal.toReal_nonneg)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPIIteration

lemma exists_small_power {p A e : ℝ} (hp : 1 < p) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ A * d ^ p ≤ e * d := by
  have hq : 0 < p - 1 := sub_pos.mpr hp
  have ht : Tendsto (fun d : ℝ ↦ A * d ^ (p - 1)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow (ne_of_gt hq), mul_zero] using
      tendsto_const_nhds.mul ((Real.continuous_rpow_const hq.le).tendsto 0)
  have hb : ∀ᶠ d : ℝ in 𝓝[>] 0, A * d ^ (p - 1) < e :=
    (ht.eventually (gt_mem_nhds he)).filter_mono nhdsWithin_le_nhds
  have h01 : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < 1 :=
    Filter.Eventually.and (show ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d from self_mem_nhdsWithin)
      ((gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  obtain ⟨d, ⟨hd, hd1⟩, hAd⟩ := (h01.and hb).exists
  refine ⟨d, hd, hd1, ?_⟩
  have heq : d ^ p = d ^ (p - 1) * d := by
    calc
      d ^ p = d ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hd, Real.rpow_one]
  rw [heq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hAd.le hd.le

theorem superlinear_iteration {p A B : ℝ} (hp : 1 < p) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ d : ℝ, 0 < d ∧ ∀ u : ℕ → ℝ, (∀ j, 0 ≤ u j) → u 0 ≤ d →
      (∀ j, u (j + 1) ≤ A * B ^ j * (u j) ^ p) →
      Tendsto u atTop (𝓝 0) := by
  obtain ⟨t, ht, ht1, hBt⟩ := exists_small_power (A := B) hp (by norm_num : (0 : ℝ) < 1)
  simp only [one_mul] at hBt
  obtain ⟨d, hd, _, hAd⟩ := exists_small_power (A := A) hp ht
  refine ⟨d, hd, ?_⟩
  intro u hu hu0 hstep
  have hbound : ∀ j, u j ≤ d * t ^ j := by
    intro j
    induction j with
    | zero => simpa using hu0
    | succ j ih =>
      calc
        u (j + 1) ≤ A * B ^ j * (u j) ^ p := hstep j
        _ ≤ A * B ^ j * (d * t ^ j) ^ p := by gcongr; exact hu j
        _ = (A * d ^ p) * (B * t ^ p) ^ j := by
          rw [Real.mul_rpow hd.le (pow_nonneg ht.le _), ← Real.rpow_pow_comm ht.le, mul_pow]
          ring
        _ ≤ (t * d) * t ^ j := by
          apply mul_le_mul hAd (pow_le_pow_left₀ (mul_nonneg hB (Real.rpow_nonneg ht.le _)) hBt j)
            (pow_nonneg (mul_nonneg hB (Real.rpow_nonneg ht.le _)) _) (by positivity)
        _ = d * t ^ (j + 1) := by rw [pow_succ]; ring
  have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one ht.le ht1
  have hlim : Tendsto (fun j : ℕ ↦ d * t ^ j) atTop (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hgeo
  exact squeeze_zero hu hbound hlim

end RPIIteration

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPIIteration

lemma exists_small_positive_sublevel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (h : X → ℝ) (hm : AEMeasurable h μ)
    (hp : ∀ᵐ x ∂μ, 0 < h x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ μ.real {x | h x < k} < δ := by
  let q : ℕ → ℝ := fun j ↦ (1 / 2 : ℝ) ^ j
  let A : ℕ → Set X := fun j ↦ {x | h x < q j}
  have hq : Tendsto q atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hAm (j : ℕ) : NullMeasurableSet (A j) μ := nullMeasurableSet_lt hm aemeasurable_const
  have hAa : Antitone A := by
    intro i j hij x hx
    change h x < q i
    change h x < q j at hx
    exact hx.trans_le (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)
  have hzero : μ (⋂ j, A j) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hp] with x hx
    intro hxA
    have hle : h x ≤ 0 := ge_of_tendsto hq (Eventually.of_forall fun j ↦ (show h x < q j from (mem_iInter.mp hxA) j).le)
    exact (not_le_of_gt hx) hle
  have ht := tendsto_measure_iInter_atTop hAm hAa ⟨0, measure_ne_top μ _⟩
  rw [hzero] at ht
  have hreal : Tendsto (fun j ↦ μ.real (A j)) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨j, hj⟩ := (hreal.eventually (gt_mem_nhds hδ)).exists
  exact ⟨q j, pow_pos (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num), hj⟩

end RPIIteration

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPIIteration

def radius (j : ℕ) : ℝ := 1 + (1 / 2 : ℝ) ^ j
def level (a : ℝ) (j : ℕ) : ℝ := a / 2 * radius j

lemma radius_bounds (j : ℕ) : 1 < radius j ∧ radius j ≤ 2 := by
  have h0 : 0 < (1/2 : ℝ)^j := pow_pos (by norm_num) _
  have h1 : (1/2 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> dsimp [radius] <;> linarith

lemma radius_succ_lt (j : ℕ) : radius (j + 1) < radius j := by
  dsimp [radius]
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1/2) j]

lemma level_bounds {a : ℝ} (ha : 0 < a) (j : ℕ) :
    0 < level a j ∧ a/2 < level a j ∧ level a j ≤ a := by
  have hr := radius_bounds j
  have hr0 : 0 < radius j := lt_trans zero_lt_one hr.1
  dsimp [level]
  constructor
  · positivity
  constructor
  · nlinarith [hr.1]
  · nlinarith [hr.2]

lemma level_succ_lt {a : ℝ} (ha : 0 < a) (j : ℕ) : level a (j + 1) < level a j := by
  exact mul_lt_mul_of_pos_left (radius_succ_lt j) (by positivity)

lemma level_zero (a : ℝ) : level a 0 = a := by simp [level, radius]; ring

lemma quotient_bound {a : ℝ} (ha : 0 < a) (j : ℕ) :
    level a j / ((radius j - radius (j+1)) * (level a j - level a (j+1))) ≤ 8 * (4 : ℝ)^j := by
  have hden : 0 < (radius j - radius (j+1)) * (level a j - level a (j+1)) :=
    mul_pos (sub_pos.mpr (radius_succ_lt j)) (sub_pos.mpr (level_succ_lt ha j))
  rw [div_le_iff₀ hden]
  have heq : (radius j - radius (j+1)) * (level a j - level a (j+1)) = a/8 * ((1/2 : ℝ)^j)^2 := by
    simp only [radius, level, pow_succ]
    ring
  have hpow : ((1/2 : ℝ)^j)^2 = ((1/2 : ℝ)^2)^j := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have h4 : (4 : ℝ)^j * ((1/2 : ℝ)^j)^2 = 1 := by
    rw [hpow, ← mul_pow]
    norm_num
  rw [heq]
  calc
    _ ≤ a := (level_bounds ha j).2.2
    _ = 8 * (4 : ℝ)^j * (a/8 * ((1/2 : ℝ)^j)^2) := by
      calc
        _ = a * ((4 : ℝ)^j * ((1/2 : ℝ)^j)^2) := by rw [h4, mul_one]
        _ = _ := by ring

lemma power_step {a C p : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hp : 0 ≤ p)
    {U V : ℝ} (hU : 0 ≤ U) (j : ℕ)
    (hstep : V ≤ C * (level a j / ((radius j - radius (j+1)) * (level a j - level a (j+1)))) ^ p * U ^ p) :
    V ≤ (C * (8 : ℝ)^p) * ((4 : ℝ)^p)^j * U ^ p := by
  have hpos : 0 ≤ level a j / ((radius j - radius (j+1)) * (level a j - level a (j+1))) := by
    exact div_nonneg (level_bounds ha j).1.le
      (mul_nonneg (sub_nonneg.mpr (radius_succ_lt j).le) (sub_nonneg.mpr (level_succ_lt ha j).le))
  calc
    _ ≤ C * (level a j / ((radius j - radius (j+1)) * (level a j - level a (j+1)))) ^ p * U ^ p := hstep
    _ ≤ C * (8 * (4 : ℝ)^j)^p * U ^ p := by
      gcongr
      exact quotient_bound ha j
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 4)]
      ring

end RPIIteration

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem no_positive_bounded_supersolution_with_zero_vertex_inf
    {n : ℕ} (hn : 8 ≤ n) (E : Set (Euc n))
    (hmin : IsLocallyPerimeterMinimizing E) :
    IsCone E → (0 : Euc n) ∈ perimeterSupport E → ∀ (h : Euc n → ℝ) (G : Euc n → Euc n),
    WholeBoundarySobolev E h G → WholeBoundarySupersolution E G →
    (∀ᵐ x ∂boundaryArea E, 0 < h x ∧ h x ≤ 1) → ZeroEssentialInfAtVertex E h → False := by
  intro _ _ h G hSobolev hSuper hpositive hinf
  classical
  have hn2 : 2 < n := by omega
  have hn1 : 1 < n := by omega
  let m : ℝ := (n-1 : ℕ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < n-1 by omega)
  let p : ℝ := 1 + 1/m
  have hp : 1 < p := by dsimp [p]; linarith [one_div_pos.mpr hm]
  have hpk : (((n-1 : ℕ) : ℝ)-1) * p < (n-1 : ℕ) := by
    have hcan : m * (1/m) = 1 := mul_one_div_cancel (ne_of_gt hm)
    have hinv : 0 < 1/m := one_div_pos.mpr hm
    change (m-1) * (1+1/m) < m
    nlinarith
  have hh01 : ∀ᵐ x ∂boundaryArea E, 0 ≤ h x ∧ h x ≤ 1 :=
    hpositive.mono fun _ hx ↦ ⟨hx.1.le, hx.2⟩
  obtain ⟨C, hC, hstep⟩ := wholeBoundary_sublevel_measure_step hn2 hmin hSobolev hSuper hh01 hp hpk
  obtain ⟨δ, hδ, hiter⟩ := RPIIteration.superlinear_iteration (p := p)
    (A := C * (8 : ℝ)^p) (B := (4 : ℝ)^p) hp (by positivity) (by positivity)
  let μ := (boundaryArea E).restrict (Metric.ball 0 2)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn1 hmin 0 (by norm_num : (0 : ℝ) < 2)⟩
  have hmμ : AEMeasurable h μ := (hSobolev 2 (by norm_num)).1.aestronglyMeasurable.aemeasurable
  have hpμ : ∀ᵐ x ∂μ, 0 < h x := ae_restrict_of_ae (hpositive.mono fun _ hx ↦ hx.1)
  obtain ⟨a, ha, ha1, hsmall⟩ := RPIIteration.exists_small_positive_sublevel μ h hmμ hpμ hδ
  let u : ℕ → ℝ := fun j ↦ (boundaryArea E).real
    (Metric.ball 0 (RPIIteration.radius j) ∩ {x | h x < RPIIteration.level a j})
  have hu : ∀ j, 0 ≤ u j := fun _ ↦ measureReal_nonneg
  have hu0 : u 0 ≤ δ := by
    have hmA : NullMeasurableSet {x | h x < a} μ := nullMeasurableSet_lt hmμ aemeasurable_const
    have heq : u 0 = μ.real {x | h x < a} := by
      dsimp [u, Measure.real]
      rw [RPIIteration.level_zero]
      norm_num only [RPIIteration.radius, pow_zero] 
      change (boundaryArea E (Metric.ball 0 2 ∩ {x | h x < a})).toReal = _
      rw [Measure.restrict_apply₀ hmA, inter_comm]
    rw [heq]
    exact hsmall.le
  have hrec (j : ℕ) : u (j+1) ≤ (C * (8 : ℝ)^p) * ((4 : ℝ)^p)^j * (u j)^p := by
    apply RPIIteration.power_step ha hC.le (lt_trans zero_lt_one hp).le (hu j) j
    exact hstep (RPIIteration.radius (j+1)) (RPIIteration.radius j)
      (RPIIteration.level a (j+1)) (RPIIteration.level a j)
      (lt_trans zero_lt_one (RPIIteration.radius_bounds (j+1)).1)
      (RPIIteration.radius_succ_lt j) (RPIIteration.radius_bounds j).2
      (RPIIteration.level_bounds ha (j+1)).1 (RPIIteration.level_succ_lt ha j)
  have hlim := hiter u hu hu0 hrec
  let A := Metric.ball (0 : Euc n) 1 ∩ {x | h x < a/2}
  have hApos : 0 < boundaryArea E A := hinf 1 (by norm_num) (a/2) (by positivity)
  have hAtop : boundaryArea E A ≠ ⊤ := ne_top_of_le_ne_top
    (ne_of_lt (minimizing_boundaryArea_ball_lt_top hn1 hmin 0 (by norm_num : (0 : ℝ) < 1)))
    (measure_mono inter_subset_left)
  have hAr : 0 < (boundaryArea E).real A := ENNReal.toReal_pos hApos.ne' hAtop
  have hlower (j : ℕ) : (boundaryArea E).real A ≤ u j := by
    apply ENNReal.toReal_mono
    · apply ne_top_of_le_ne_top
        (ne_of_lt (minimizing_boundaryArea_ball_lt_top hn1 hmin 0
          (lt_trans zero_lt_one (RPIIteration.radius_bounds j).1)))
      exact measure_mono inter_subset_left
    · apply measure_mono
      intro x hx
      exact ⟨Metric.ball_subset_ball (RPIIteration.radius_bounds j).1.le hx.1,
        hx.2.trans (RPIIteration.level_bounds ha j).2.1⟩
  have hzero : (boundaryArea E).real A ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hlower)
  exact (not_le_of_gt hAr) hzero

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem minimizing_boundaryArea_ball_pos {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {x : Euc n} (hx : x ∈ perimeterSupport E) {r : ℝ} (hr : 0 < r) :
    0 < boundaryArea E (Metric.ball x r) := by
  obtain ⟨C, D, hC0, hCt, hD0, hDt, hc⟩ := minimizing_perimeter_boundaryArea_comparison hn
  have hh := Measure.le_iff'.mp (hc E hmin).1 (Metric.ball x r)
  rw [perimeterMeasure_open E Metric.isOpen_ball, Measure.smul_apply, smul_eq_mul] at hh
  by_contra h
  have hz : boundaryArea E (Metric.ball x r) = 0 := le_antisymm (le_of_not_gt h) bot_le
  rw [hz, mul_zero] at hh
  exact (not_le_of_gt (hx r hr)) hh

theorem regular_ball_nonempty {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hvertex : (0 : Euc n) ∈ perimeterSupport E) {r : ℝ} (hr : 0 < r) :
    ((perimeterSupport E \ Z) ∩ Metric.ball 0 r).Nonempty := by
  have hp := minimizing_boundaryArea_ball_pos (by omega : 1 < n) hmin hvertex hr
  have hzs := boundaryArea_zero_of_singular_dim hn E Z hZd
  by_contra he
  have hsub : Metric.ball (0 : Euc n) r ∩ perimeterSupport E ⊆ Z := by
    intro x hx
    by_contra hxz
    exact he ⟨x, ⟨⟨hx.2, hxz⟩, hx.1⟩⟩
  have hb : boundaryArea E (Metric.ball 0 r) =
      boundaryArea E (Metric.ball 0 r ∩ perimeterSupport E) := by
    simp only [boundaryArea, Measure.restrict_apply measurableSet_ball,
      Measure.restrict_apply (measurableSet_ball.inter (isClosed_perimeterSupport E).measurableSet),
      inter_assoc, inter_self]
  have hh := measure_mono (μ := boundaryArea E) hsub
  rw [← hb, hzs] at hh
  exact (not_le_of_gt hp) hh

theorem zeroEssentialInf_of_median_small_infimum {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hvertex : (0 : Euc n) ∈ perimeterSupport E)
    {W : Euc n → ℝ} {D : Euc n → Euc n}
    (htrace : ∀ x ∈ perimeterSupport E \ Z, HasC1TraceJetAt (perimeterSupport E) W D x)
    (hmedian : ∀ r : ℝ, 0 < r → r ≤ 1 →
      sInf (W '' ((perimeterSupport E \ Z) ∩ Metric.ball 0 r)) ≤ 3 * r) :
    ZeroEssentialInfAtVertex E (fun x ↦ min (W x) 1) := by
  classical
  intro R hR ε hε
  obtain ⟨r, hr, hrR, hrε, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r < R ∧ 3 * r < ε ∧ r ≤ 1 := by
    refine ⟨min (min (R/2) (ε/6)) (1/2), by positivity, ?_, ?_, ?_⟩
    · have := (min_le_left (min (R/2) (ε/6)) (1/2)).trans (min_le_left (R/2) (ε/6))
      linarith
    · have := (min_le_left (min (R/2) (ε/6)) (1/2)).trans (min_le_right (R/2) (ε/6))
      linarith
    · exact (min_le_right _ _).trans (by norm_num)
  obtain ⟨w, hw, hwε⟩ := exists_lt_of_csInf_lt
    ((regular_ball_nonempty hn hmin hZd hvertex hr).image W) ((hmedian r hr hr1).trans_lt hrε)
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨U, hU, hxU, f, hf, he, hD⟩ := htrace x hx.1
  have hfx : f x < ε := by rw [he ⟨hx.1.1, hxU⟩]; exact hwε
  have hm : U ∩ Metric.ball (0 : Euc n) R ∩ {y | f y < ε} ∈ 𝓝 x :=
    inter_mem (inter_mem (hU.mem_nhds hxU)
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hrR.le hx.2)))
      (((hf.contDiffAt (hU.mem_nhds hxU)).continuousAt).eventually (gt_mem_nhds hfx))
  obtain ⟨s, hs, hsm⟩ := Metric.mem_nhds_iff.mp hm
  have hsarea := minimizing_boundaryArea_ball_pos (by omega : 1 < n) hmin hx.1.1 hs
  have hsub : Metric.ball x s ∩ perimeterSupport E ⊆
      Metric.ball (0 : Euc n) R ∩ {y | min (W y) 1 < ε} := by
    intro y hy
    have hh := hsm hy.1
    refine ⟨hh.1.2, ?_⟩
    change min (W y) 1 < ε
    apply lt_of_le_of_lt (min_le_left _ _)
    rw [← he ⟨hy.2, hh.1.1⟩]
    exact hh.2
  have heq : boundaryArea E (Metric.ball x s ∩ perimeterSupport E) =
      boundaryArea E (Metric.ball x s) := by
    simp only [boundaryArea, Measure.restrict_apply measurableSet_ball,
      Measure.restrict_apply (measurableSet_ball.inter (isClosed_perimeterSupport E).measurableSet),
      inter_assoc, inter_self]
  exact hsarea.trans_le (heq ▸ measure_mono (μ := boundaryArea E) hsub)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem no_regular_positive_supersolution_with_median_bound
    {n : ℕ} (hn : 8 ≤ n) {E Z : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hcone : IsCone E)
    (hvertex : (0 : Euc n) ∈ perimeterSupport E)
    (hZ : IsClosed Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ perimeterSupport E \ Z, ∃ U : Set (Euc n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Euc n → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ perimeterSupport E ↔ f y = 0) ∧
        (∀ y ∈ U, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)))
    {W : Euc n → ℝ} {D : Euc n → Euc n}
    (htrace : ∀ x ∈ perimeterSupport E \ Z, HasC1TraceJetAt (perimeterSupport E) W D x)
    (hpositive : ∀ x ∈ perimeterSupport E \ Z, 0 < W x)
    (hsup : ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient (perimeterSupport E) φ x)
        ∂surfaceMeasure (perimeterSupport E))
    (hmedian : ∀ r : ℝ, 0 < r → r ≤ 1 →
      sInf (W '' ((perimeterSupport E \ Z) ∩ Metric.ball 0 r)) ≤ 3 * r) : False := by
  obtain ⟨hSob, hSuper⟩ :=
    c1_min_wholeBoundarySobolev_and_supersolution_of_minimizing_regular_geometry
      hn hmin hZ hZd hreg htrace (fun x hx ↦ (hpositive x hx).le) hsup
  have hinf := zeroEssentialInf_of_median_small_infimum hn hmin hZd hvertex htrace hmedian
  have hs : ∀ᵐ x ∂boundaryArea E, x ∈ perimeterSupport E :=
    ae_restrict_mem (isClosed_perimeterSupport E).measurableSet
  have hz : ∀ᵐ x ∂boundaryArea E, x ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      boundaryArea_zero_of_singular_dim hn E Z hZd
  have hp : ∀ᵐ x ∂boundaryArea E, 0 < min (W x) 1 ∧ min (W x) 1 ≤ 1 := by
    filter_upwards [hs, hz] with x hx hxz
    exact ⟨lt_min (hpositive x ⟨hx, hxz⟩) zero_lt_one, min_le_right _ _⟩
  exact no_positive_bounded_supersolution_with_zero_vertex_inf hn E hmin hcone hvertex
    (fun x ↦ min (W x) 1) (truncatedGradient W D) hSob hSuper hp hinf

end RPISingularHarnack

end

end OAI
