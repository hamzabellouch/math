import Mathlib
import OAI.Analysis.PathSelection.ContourDivision

namespace OAI

/-! Fixed-contour preparation polynomials, division and stable root counts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Metric Polynomial

namespace PathSelection.Preparation

lemma eqOn_closedBall_of_codiscrete {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall 0 r)) (hg : ContinuousOn g (closedBall 0 r))
    (heq : f =ᶠ[codiscreteWithin (closedBall 0 r)] g) :
    EqOn f g (closedBall 0 r) := by
  have hi : EqOn f g (ball 0 r) := by
    intro z hz
    have hznear : closedBall (0 : ℂ) r ∈ 𝓝 z :=
      mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
    have hle : 𝓝[≠] z ≤ codiscreteWithin (closedBall (0 : ℂ) r) := by
      rw [codiscreteWithin]
      exact le_iSup_of_le z (le_iSup_of_le (ball_subset_closedBall hz) (by
        rw [sdiff_eq, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hznear)]))
    have he := heq.filter_mono hle
    have hfc := (hf z (ball_subset_closedBall hz)).continuousAt hznear
    have hgc := (hg z (ball_subset_closedBall hz)).continuousAt hznear
    exact tendsto_nhds_unique (hfc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  exact hi.of_subset_closure hf hg ball_subset_closedBall (by rw [closure_ball _ hr.ne'])

 

lemma nonnegative_factor_polynomial (d : ℂ → ℤ) (hd : d.HasFiniteSupport)
    (hnonneg : ∀ z, 0 ≤ d z) :
    ∃ P : ℂ[X], P.Monic ∧
      (∀ z, P.eval z = (∏ᶠ w : ℂ, (fun t : ℂ => t-w) ^ d w) z) ∧
      (∀ z, P.eval z = 0 → z ∈ Function.support d) := by
  classical
  let s := hd.toFinset
  let P : ℂ[X] := ∏ w ∈ s, (X - C w) ^ (d w).toNat
  have hP : P.Monic := monic_prod_of_monic s _ (fun w _ => (monic_X_sub_C w).pow _)
  have heq (z : ℂ) : P.eval z = (∏ᶠ w : ℂ, (fun t : ℂ => t-w) ^ d w) z := by
    rw [Function.FactorizedRational.finprod_eq_fun hd]
    dsimp only
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · simp only [P, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      apply Finset.prod_congr rfl
      intro w _
      conv_rhs => rw [← Int.toNat_of_nonneg (hnonneg w), zpow_natCast]
    · intro w hw
      apply hd.mem_toFinset.mpr
      by_contra hn
      have : d w = 0 := by simpa using hn
      simp [Function.mem_mulSupport, this] at hw
  refine ⟨P, hP, heq, ?_⟩
  intro z hz
  by_contra hn
  have hprod : P.eval z ≠ 0 := by
    simp only [P, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro hzw
    apply hn
    rw [hzw]
    exact hd.mem_toFinset.mp hw
  exact hprod hz

 

theorem exists_preparation_on_disc {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ P : ℂ[X], P.Monic ∧
      (∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r) ∧
      ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (closedBall 0 r) ∧
        (∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0) ∧
        EqOn f (fun z => P.eval z * u z) (closedBall 0 r) := by
  have hz : (r : ℂ) ∈ sphere (0 : ℂ) r := by
    simp [abs_of_pos hr]
  have hzc := sphere_subset_closedBall hz
  have horder : ∀ z ∈ closedBall (0 : ℂ) r, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz'
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (isConnected_closedBall hr.le).isPreconnected hzc hz'
    rw [(hf _ hzc).meromorphicOrderAt_eq, (hf _ hzc).analyticOrderAt_eq_zero.mpr (hnz _ hz)]
    simp
  let d := MeromorphicOn.divisor f (closedBall (0 : ℂ) r)
  have hd : (d : ℂ → ℤ).HasFiniteSupport := d.finiteSupport (isCompact_closedBall _ _)
  have hdpos : ∀ z, 0 ≤ d z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  obtain ⟨P, hP, hPeq, hroot⟩ := nonnegative_factor_polynomial d hd hdpos
  obtain ⟨u, hu, hunz, heq⟩ := hf.meromorphicOn.extract_zeros_poles
    (fun z => horder z z.property) hd
  refine ⟨P, hP, ?_, u, hu, fun z hz => hunz ⟨z, hz⟩, ?_⟩
  · intro z hz
    have hs := hroot z hz
    have hzc := d.supportWithinDomain hs
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hzc) with hlt | he
    · exact mem_ball_zero_iff.mpr hlt
    have hzsp : z ∈ sphere (0 : ℂ) r := mem_sphere_zero_iff_norm.mpr he
    have hd0 : d z = 0 := by
      dsimp [d]
      rw [hf.meromorphicOn.divisor_apply hzc, (hf z hzc).meromorphicOrderAt_eq,
        (hf z hzc).analyticOrderAt_eq_zero.mpr (hnz z hzsp)]
      simp
    exact False.elim (hs hd0)
  · apply eqOn_closedBall_of_codiscrete hr hf.continuousOn
      (P.continuous.continuousOn.mul hu.continuousOn)
    filter_upwards [heq] with z hz
    change f z = P.eval z * u z
    rw [hPeq]
    simpa only [d, Pi.smul_apply', smul_eq_mul] using hz

 
def divisionKernel (P : ℂ[X]) (w : ℂ) : ℂ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    ∑ k ∈ Finset.range n, C (P.coeff n * w ^ (n - 1 - k)) * X ^ k

lemma divisionKernel_eval (P : ℂ[X]) (w y : ℂ) :
    (divisionKernel P w).eval y * (w-y) = P.eval w - P.eval y := by
  simp only [divisionKernel, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_mul]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hk (n : ℕ) :
      (∑ k ∈ Finset.range n, w ^ (n - 1 - k) * y ^ k) * (w-y) = w^n-y^n := by
    calc
      _ = (∑ k ∈ Finset.range n, y ^ k * w ^ (n-1-k)) * (w-y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      _ = (∑ k ∈ Finset.range n, w ^ k * y ^ (n-1-k)) * (w-y) := by
        rw [geom_sum₂_comm y w n]
      _ = _ := geom_sum₂_mul w y n
  simp_rw [mul_assoc, hk, mul_sub]
  rw [Finset.sum_sub_distrib, eval_eq_sum_range, eval_eq_sum_range]

lemma divisionKernel_degree (P : ℂ[X]) (w : ℂ) :
    (divisionKernel P w).degree < P.natDegree := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp only [divisionKernel, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hnd : n ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hne : k ≠ m := by omega
  simp [hne.symm]

lemma divisionKernel_continuous (P : ℂ[X]) (y : ℂ) :
    Continuous (fun w => (divisionKernel P w).eval y) := by
  simp only [divisionKernel, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  fun_prop

open scoped Real
open Complex

 

theorem fixed_circle_division {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0)
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    G y = P.eval y * ((2 * π * I)⁻¹ *
      ∮ w in C(0, r), G w / (P.eval w * (w-y))) +
      (2 * π * I)⁻¹ * ∮ w in C(0, r),
        G w / P.eval w * (divisionKernel P w).eval y := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg y) (mem_ball_zero_iff.mp hy)
  have hwy : ∀ w ∈ sphere (0 : ℂ) r, w-y ≠ 0 := by
    intro w hw
    apply sub_ne_zero.mpr
    intro he
    subst w
    exact (ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hw)
  have hc₁ : ContinuousOn (fun w => G w / (P.eval w * (w-y))) (sphere 0 r) :=
    (hG.continuousOn.mono sphere_subset_closedBall).div
      (P.continuous.continuousOn.mul (continuousOn_id.sub continuousOn_const))
      (fun w hw => mul_ne_zero (hP w hw) (hwy w hw))
  have hc₂ : ContinuousOn (fun w => G w / P.eval w * (divisionKernel P w).eval y)
      (sphere 0 r) :=
    ((hG.continuousOn.mono sphere_subset_closedBall).div P.continuous.continuousOn hP).mul
      (divisionKernel_continuous P y).continuousOn
  have hi : (∮ w in C(0, r), G w / (w-y)) =
      P.eval y * (∮ w in C(0, r), G w / (P.eval w * (w-y))) +
        ∮ w in C(0, r), G w / P.eval w * (divisionKernel P w).eval y := by
    have hci₁ : CircleIntegrable (fun w => P.eval y * (G w / (P.eval w * (w-y)))) 0 r :=
      (continuousOn_const.mul hc₁).circleIntegrable hr.le
    rw [← circleIntegral.integral_const_mul,
      ← circleIntegral.integral_add hci₁ (hc₂.circleIntegrable hr.le)]
    apply circleIntegral.integral_congr hr.le
    intro w hw
    have hk := divisionKernel_eval P w y
    field_simp [hP w hw, hwy w hw]
    linear_combination -G w * hk
  have hc := circleIntegral_div_sub_of_differentiable_on_off_countable
    Set.countable_empty hy hG.continuousOn
    (fun z hz => (hG z (ball_subset_closedBall hz.1)).differentiableAt)
  rw [hc] at hi
  have htwo : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  apply (mul_left_cancel₀ htwo)
  rw [mul_add]
  field_simp
  simpa only [div_mul_eq_mul_div] using hi

 
def divisionRemainder (G : ℂ → ℂ) (P : ℂ[X]) (r : ℝ) : ℂ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    ∑ k ∈ Finset.range n,
      C ((2 * π * I)⁻¹ * ∮ w in C(0,r),
        G w / P.eval w * (P.coeff n * w ^ (n-1-k))) * X ^ k

lemma divisionRemainder_degree (G : ℂ → ℂ) (P : ℂ[X]) (r : ℝ) :
    (divisionRemainder G P r).degree < P.natDegree := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp only [divisionRemainder, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hnd : n ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hne : m ≠ k := by omega
  simp [hne]

lemma divisionRemainder_eval {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ} (hr : 0 ≤ r)
    (hG : ContinuousOn G (sphere 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0) (y : ℂ) :
    (divisionRemainder G P r).eval y =
      (2 * π * I)⁻¹ * ∮ w in C(0,r), G w / P.eval w * (divisionKernel P w).eval y := by
  have hcont (n k : ℕ) : ContinuousOn
      (fun w => G w / P.eval w * (P.coeff n * w ^ (n-1-k)) * y ^ k) (sphere 0 r) :=
    (((hG.div P.continuous.continuousOn hP).mul
      (continuousOn_const.mul (continuousOn_id.pow _))).mul continuousOn_const)
  simp only [divisionRemainder, divisionKernel, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  simp_rw [Finset.mul_sum]
  rw [circleIntegral.integral_fun_sum (fun n _ =>
    (continuousOn_finsetSum _ (fun k _ => by simpa only [mul_assoc] using hcont n k)).circleIntegrable hr)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [circleIntegral.integral_fun_sum (fun k _ =>
    (by simpa only [mul_assoc] using (hcont n k).circleIntegrable hr))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (fun w => G w / P.eval w * (P.coeff n * w ^ (n-1-k) * y^k)) =
      (fun w => (G w / P.eval w * (P.coeff n * w ^ (n-1-k))) • y^k) by
        funext w; simp only [smul_eq_mul, mul_assoc], circleIntegral.integral_smul_const]
  simp only [smul_eq_mul, mul_assoc]

def divisionQuotient (G : ℂ → ℂ) (P : ℂ[X]) (r : ℝ) (y : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ w in C(0,r), G w / (P.eval w * (w-y))

lemma divisionQuotient_analyticOnNhd {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (sphere 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0) :
    AnalyticOnNhd ℂ (divisionQuotient G P r) (ball 0 r) := by
  have hi := (hG.div P.continuous.continuousOn hP).circleIntegrable hr.le
  have ha := (hasFPowerSeriesOn_cauchy_integral (R := ⟨r, hr.le⟩) hi hr).analyticOnNhd
  convert! ha using 1
  · funext y
    simp only [divisionQuotient, smul_eq_mul, Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
    congr 1
    apply congrArg (fun f : ℂ → ℂ => ∮ w in C(0,r), f w)
    funext w
    ring
  · exact (Metric.eball_coe (x := (0 : ℂ)) (ε := ⟨r, hr.le⟩)).symm

 

theorem fixed_disc_division {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0) :
    AnalyticOnNhd ℂ (divisionQuotient G P r) (ball 0 r) ∧
    (divisionRemainder G P r).degree < P.natDegree ∧
    EqOn G (fun y => P.eval y * divisionQuotient G P r y +
      (divisionRemainder G P r).eval y) (ball 0 r) := by
  refine ⟨divisionQuotient_analyticOnNhd hr (hG.continuousOn.mono sphere_subset_closedBall) hP,
    divisionRemainder_degree G P r, ?_⟩
  intro y hy
  dsimp only
  rw [divisionRemainder_eval hr.le (hG.continuousOn.mono sphere_subset_closedBall) hP]
  exact fixed_circle_division hG hP hy

 

lemma eqOn_deriv_closedBall {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (heq : EqOn f g (closedBall 0 r)) : EqOn (deriv f) (deriv g) (closedBall 0 r) := by
  have hi := (heq.mono ball_subset_closedBall).deriv isOpen_ball
  exact hi.of_subset_closure hf.deriv.continuousOn hg.deriv.continuousOn
    ball_subset_closedBall (by rw [closure_ball _ hr.ne'])

lemma circleIntegral_root_sum {r : ℝ} (hr : 0 < r) (l : ℕ) (a : Multiset ℂ)
    (ha : ∀ w ∈ a, w ∈ ball (0 : ℂ) r) :
    CircleIntegrable (fun z => (a.map (fun w => z^l / (z-w))).sum) 0 r ∧
    (∮ z in C(0,r), (a.map (fun w => z^l / (z-w))).sum) =
      (2 * π * I) * (a.map (fun w => w^l)).sum := by
  induction a using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a s ih =>
    have hai : a ∈ ball (0 : ℂ) r := ha a (by simp)
    obtain ⟨hsi, hseq⟩ := ih (fun w hw => ha w (by simp [hw]))
    have hane (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z-a ≠ 0 := by
      apply sub_ne_zero.mpr
      rintro rfl
      exact (ne_of_lt (mem_ball_zero_iff.mp hai)) (mem_sphere_zero_iff_norm.mp hz)
    have hai' : CircleIntegrable (fun z => z^l / (z-a)) 0 r :=
      ((continuousOn_id.pow l).div (continuousOn_id.sub continuousOn_const) hane).circleIntegrable hr.le
    have haeq : (∮ z in C(0,r), z^l / (z-a)) = (2 * π * I) * a^l :=
      circleIntegral_div_sub_of_differentiable_on_off_countable Set.countable_empty hai
        ((continuous_pow l).continuousOn) (fun z _ => by fun_prop)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact ⟨hai'.add hsi, by rw [circleIntegral.integral_add hai' hsi, haeq, hseq, mul_add]⟩

 
theorem polynomial_power_sum_contour {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hP : P ≠ 0) (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r) (l : ℕ) :
    (2 * π * I)⁻¹ * (∮ z in C(0,r), z^l * P.derivative.eval z / P.eval z) =
      (P.roots.map (fun w => w^l)).sum := by
  have ha : ∀ w ∈ P.roots, w ∈ ball (0 : ℂ) r := fun w hw =>
    hroot w ((mem_roots hP).mp hw)
  have hi := (circleIntegral_root_sum hr l P.roots ha).2
  have he : (∮ z in C(0,r), z^l * P.derivative.eval z / P.eval z) =
      ∮ z in C(0,r), (P.roots.map (fun w => z^l / (z-w))).sum := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hnz : P.eval z ≠ 0 := by
      intro he
      exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
    dsimp only
    rw [mul_div_assoc, (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hnz,
      ← Multiset.sum_map_mul_left]
    simp only [mul_one_div]
  rw [he, hi, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero, I_ne_zero]

 

theorem preparation_power_sum_contour {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hP : P.Monic)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r)
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hunz : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (closedBall 0 r)) (l : ℕ) :
    (2 * π * I)⁻¹ * (∮ z in C(0,r), z^l * deriv f z / f z) =
      (P.roots.map (fun w => w^l)).sum := by
  have hPa : AnalyticOnNhd ℂ (fun z => P.eval z) (closedBall 0 r) :=
    fun z _ => AnalyticOnNhd.eval_polynomial P z (mem_univ z)
  have hdeq := eqOn_deriv_closedBall hr hf (hPa.mul hu) heq
  have hPn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : P.eval z ≠ 0 := by
    intro he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
  have hunit : AnalyticOnNhd ℂ (fun z => z^l * deriv u z / u z) (closedBall 0 r) :=
    ((analyticOnNhd_id.pow l).mul hu.deriv).div hu hunz
  have hzero : (∮ z in C(0,r), z^l * deriv u z / u z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      hunit.continuousOn (fun z hz => (hunit z (ball_subset_closedBall hz.1)).differentiableAt)
  have hpoly : CircleIntegrable (fun z => z^l * P.derivative.eval z / P.eval z) 0 r :=
    (((continuousOn_id.pow l).mul P.derivative.continuous.continuousOn).div
      P.continuous.continuousOn hPn).circleIntegrable hr.le
  have hi : (∮ z in C(0,r), z^l * deriv f z / f z) =
      (∮ z in C(0,r), z^l * P.derivative.eval z / P.eval z) +
      ∮ z in C(0,r), z^l * deriv u z / u z := by
    rw [← circleIntegral.integral_add hpoly
      ((hunit.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le)]
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hzc := sphere_subset_closedBall hz
    dsimp only
    rw [heq hzc, hdeq hzc, deriv_fun_mul (P.differentiableAt) (hu z hzc).differentiableAt,
      (P.hasDerivAt z).deriv]
    field_simp [hPn z hz, hunz z hzc]
  rw [hi, hzero, add_zero]
  exact polynomial_power_sum_contour hr hP.ne_zero hroot l

 

def newtonEsymm (powerSum : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 1 else (n : ℂ)⁻¹ * (-1)^(n+1) *
    ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun a => a.1 < n),
      if h : a.1 < n then (-1)^a.1 * newtonEsymm powerSum a.1 * powerSum a.2 else 0
termination_by n
decreasing_by assumption

lemma multiset_newton_identity (a : Multiset ℂ) (n : ℕ) :
    (n : ℂ) * a.esymm n = (-1)^(n+1) *
        ∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1 < n),
          (-1)^t.1 * a.esymm t.1 * (a.map (fun w => w^t.2)).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun w : a => (w : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum a ℂ n)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  rw [← Finset.sum_map_val (Finset.univ : Finset a)]
  exact (congrArg Multiset.sum (Multiset.map_univ a (fun w => w^t.2))).symm

lemma newtonEsymm_eq (a : Multiset ℂ) (n : ℕ) :
    newtonEsymm (fun k => (a.map (fun w => w^k)).sum) n = a.esymm n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [newtonEsymm]
    split_ifs with hn
    · subst n
      simp [Multiset.esymm]
    · have hsum : (∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1 < n),
          if h : t.1 < n then (-1 : ℂ)^t.1 * newtonEsymm (fun k => (a.map (fun w => w^k)).sum) t.1 *
            (a.map (fun w => w^t.2)).sum else 0) =
        ∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1 < n),
          (-1 : ℂ)^t.1 * a.esymm t.1 * (a.map (fun w => w^t.2)).sum := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [dite_eq_left (Finset.mem_filter.mp ht).2, ih t.1 (Finset.mem_filter.mp ht).2]
      rw [hsum, mul_assoc, ← multiset_newton_identity]
      exact inv_mul_cancel_left₀ (by exact_mod_cast hn) _

 

def contourPowerSum (f : ℂ → ℂ) (r : ℝ) (l : ℕ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(0,r), z^l * deriv f z / f z

 
def preparationPolynomial (f : ℂ → ℂ) (r : ℝ) (d : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d+1),
    C ((-1)^(d-k) * newtonEsymm (contourPowerSum f r) (d-k)) * X^k

lemma polynomial_newton_formula (P : ℂ[X]) (hP : P.Monic) :
    (∑ k ∈ Finset.range (P.natDegree+1),
      C ((-1)^(P.natDegree-k) *
        newtonEsymm (fun l => (P.roots.map (fun w => w^l)).sum) (P.natDegree-k)) * X^k) = P := by
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [newtonEsymm_eq,
    coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits P) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
    hP.leadingCoeff, one_mul]

lemma preparationPolynomial_eq {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hP : P.Monic)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r)
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hunz : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (closedBall 0 r)) :
    preparationPolynomial f r P.natDegree = P := by
  have hs : contourPowerSum f r = fun l => (P.roots.map (fun w => w^l)).sum :=
    funext (preparation_power_sum_contour hr hf hP hroot hu hunz heq)
  simpa only [preparationPolynomial, hs] using polynomial_newton_formula P hP

lemma divisionQuotient_eq_unit {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hPn : ∀ z ∈ sphere (0 : ℂ) r, P.eval z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (sphere 0 r)) :
    EqOn (divisionQuotient f P r) u (ball 0 r) := by
  intro y hy
  have hr : 0 < r := (mem_ball_zero_iff.mp hy).trans_le' (norm_nonneg y)
  have hi : (∮ z in C(0,r), f z / (P.eval z * (z-y))) =
      ∮ z in C(0,r), u z / (z-y) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    rw [heq hz]
    exact mul_div_mul_left (u z) (z-y) (hPn z hz)
  have hc := circleIntegral_div_sub_of_differentiable_on_off_countable
    Set.countable_empty hy hu.continuousOn
      (fun z hz => (hu z (ball_subset_closedBall hz.1)).differentiableAt)
  rw [divisionQuotient, hi, hc, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero, I_ne_zero]

 

theorem fixed_contour_preparation {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ d : ℕ, let W := preparationPolynomial f r d
      W.Monic ∧ W.natDegree = d ∧
      (∀ z : ℂ, W.eval z = 0 → z ∈ ball 0 r) ∧
      AnalyticOnNhd ℂ (divisionQuotient f W r) (ball 0 r) ∧
      (∀ z ∈ ball (0 : ℂ) r, divisionQuotient f W r z ≠ 0) ∧
      EqOn f (fun z => W.eval z * divisionQuotient f W r z) (ball 0 r) := by
  obtain ⟨P, hP, hroot, u, hu, hunz, heq⟩ := exists_preparation_on_disc hr hf hnz
  refine ⟨P.natDegree, ?_⟩
  dsimp only
  rw [preparationPolynomial_eq hr hf hP hroot hu hunz heq]
  have hPn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : P.eval z ≠ 0 := by
    intro he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
  have hquot := divisionQuotient_eq_unit hu hPn (heq.mono sphere_subset_closedBall)
  refine ⟨hP, rfl, hroot,
    divisionQuotient_analyticOnNhd hr (hf.continuousOn.mono sphere_subset_closedBall) hPn, ?_, ?_⟩
  · intro z hz
    rw [hquot hz]
    exact hunz z (ball_subset_closedBall hz)
  · intro z hz
    simp only [heq (ball_subset_closedBall hz), hquot hz]

lemma preparation_zero_count {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hP : P.Monic)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r)
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hunz : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (closedBall 0 r)) :
    contourPowerSum f r 0 = (P.natDegree : ℂ) := by
  have h := preparation_power_sum_contour hr hf hP hroot hu hunz heq 0
  simpa [contourPowerSum, ← (IsAlgClosed.splits P).natDegree_eq_card_roots] using h

lemma contour_zero_count_nat {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    contourPowerSum f r 0 ∈ Set.range (fun n : ℕ => (n : ℂ)) := by
  obtain ⟨P, hP, hroot, u, hu, hunz, heq⟩ := exists_preparation_on_disc hr hf hnz
  exact ⟨P.natDegree, (preparation_zero_count hr hf hP hroot hu hunz heq).symm⟩

lemma continuousOn_circleIntegral {E : Type*} [NormedAddCommGroup E]
    {A : Set E} {F : E → ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hA : IsCompact A) (hF : ContinuousOn (Function.uncurry F) (A ×ˢ sphere 0 r)) :
    ContinuousOn (fun a => ∮ z in C(0,r), F a z) A := by
  have hu := (hA.prod (isCompact_sphere (0 : ℂ) r)).uniformContinuousOn_of_continuous hF
  intro a ha
  apply TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn hr
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hb, hz⟩)
  · exact hu.tendstoUniformlyOn ha

 

theorem contour_zero_count_constant {E : Type*} [NormedAddCommGroup E]
    {A : Set E} {F : E → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hA : IsCompact A) (hcA : IsPreconnected A)
    (hf : ∀ a ∈ A, AnalyticOnNhd ℂ (F a) (closedBall 0 r))
    (hnz : ∀ a ∈ A, ∀ z ∈ sphere (0 : ℂ) r, F a z ≠ 0)
    (hF : ContinuousOn (Function.uncurry F) (A ×ˢ sphere 0 r))
    (hdF : ContinuousOn (fun p : E × ℂ => deriv (F p.1) p.2) (A ×ˢ sphere 0 r))
    {a b : E} (ha : a ∈ A) (hb : b ∈ A) :
    contourPowerSum (F a) r 0 = contourPowerSum (F b) r 0 := by
  have hi : ContinuousOn (fun a => contourPowerSum (F a) r 0) A := by
    have h := continuousOn_circleIntegral (F := fun a z => deriv (F a) z / F a z) hr.le hA
      (hdF.div hF (fun p hp => hnz p.1 hp.1 p.2 hp.2))
    simpa only [contourPowerSum, pow_zero, one_mul] using h.const_mul ((2 * π * I)⁻¹)
  have hc : (Set.range (fun n : ℕ => (n : ℂ))).Countable := countable_range _
  have hsub : (fun a => contourPowerSum (F a) r 0) '' A ⊆
      Set.range (fun n : ℕ => (n : ℂ)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact contour_zero_count_nat hr (hf a ha) (hnz a ha)
  exact hc.isTotallyDisconnected _ hsub (hcA.image _ hi)
    (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

 

theorem contour_zero_count_eq_of_norm_sub_lt {f g : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (hsmall : ∀ z ∈ sphere (0 : ℂ) r, ‖g z - f z‖ < ‖f z‖) :
    contourPowerSum f r 0 = contourPowerSum g r 0 := by
  let F : ℝ → ℂ → ℂ := fun t z => f z + (t : ℂ) * (g z - f z)
  have hfa (t : ℝ) : AnalyticOnNhd ℂ (F t) (closedBall 0 r) :=
    hf.add (analyticOnNhd_const.mul (hg.sub hf))
  have hnz (t : ℝ) (ht : t ∈ Icc 0 1) (z : ℂ) (hz : z ∈ sphere 0 r) : F t z ≠ 0 := by
    have hn : ‖(t : ℂ) * (g z - f z)‖ < ‖f z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (hsmall z hz)
    intro he
    have he' : f z = -((t : ℂ) * (g z - f z)) := eq_neg_of_add_eq_zero_left he
    have he'' := congrArg norm he'
    rw [norm_neg] at he''
    exact (ne_of_lt hn) he''.symm
  have hs : ∀ p ∈ (Icc (0 : ℝ) 1) ×ˢ sphere (0 : ℂ) r, p.2 ∈ closedBall (0 : ℂ) r :=
    fun _ hp => sphere_subset_closedBall hp.2
  have hfc : ContinuousOn (fun p : ℝ × ℂ => f p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hf.continuousOn.comp continuous_snd.continuousOn hs
  have hgc : ContinuousOn (fun p : ℝ × ℂ => g p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hg.continuousOn.comp continuous_snd.continuousOn hs
  have hdfc : ContinuousOn (fun p : ℝ × ℂ => deriv f p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hf.deriv.continuousOn.comp continuous_snd.continuousOn hs
  have hdgc : ContinuousOn (fun p : ℝ × ℂ => deriv g p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hg.deriv.continuousOn.comp continuous_snd.continuousOn hs
  have htc : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ)) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn
  have hFc : ContinuousOn (Function.uncurry F) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hfc.add (htc.mul (hgc.sub hfc))
  have hdFc : ContinuousOn (fun p : ℝ × ℂ => deriv (F p.1) p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) := by
    apply (hdfc.add (htc.mul (hdgc.sub hdfc))).congr
    intro p hp
    have hfd := (hf p.2 (hs p hp)).differentiableAt
    have hgd := (hg p.2 (hs p hp)).differentiableAt
    dsimp only [F]
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.add_def] using
      (hfd.hasDerivAt.add ((hgd.hasDerivAt.sub hfd.hasDerivAt).const_mul (p.1 : ℂ))).deriv
  have h := contour_zero_count_constant hr isCompact_Icc isPreconnected_Icc
    (fun t _ => hfa t) hnz hFc hdFc (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simpa [F] using h

 

theorem fixed_contour_preparation_of_count {f : ℂ → ℂ} {r : ℝ} {d : ℕ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0)
    (hcount : contourPowerSum f r 0 = (d : ℂ)) :
    let W := preparationPolynomial f r d
    W.Monic ∧ W.natDegree = d ∧
      (∀ z : ℂ, W.eval z = 0 → z ∈ ball 0 r) ∧
      AnalyticOnNhd ℂ (divisionQuotient f W r) (ball 0 r) ∧
      (∀ z ∈ ball (0 : ℂ) r, divisionQuotient f W r z ≠ 0) ∧
      EqOn f (fun z => W.eval z * divisionQuotient f W r z) (ball 0 r) := by
  obtain ⟨P, hP, hroot, u, hu, hunz, heq⟩ := exists_preparation_on_disc hr hf hnz
  have hd : P.natDegree = d := by
    exact_mod_cast (preparation_zero_count hr hf hP hroot hu hunz heq).symm.trans hcount
  dsimp only
  rw [← hd, preparationPolynomial_eq hr hf hP hroot hu hunz heq]
  have hPn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : P.eval z ≠ 0 := by
    intro he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
  have hquot := divisionQuotient_eq_unit hu hPn (heq.mono sphere_subset_closedBall)
  refine ⟨hP, rfl, hroot,
    divisionQuotient_analyticOnNhd hr (hf.continuousOn.mono sphere_subset_closedBall) hPn, ?_, ?_⟩
  · intro z hz
    rw [hquot hz]
    exact hunz z (ball_subset_closedBall hz)
  · intro z hz
    simp only [heq (ball_subset_closedBall hz), hquot hz]

end PathSelection.Preparation
end

end OAI
