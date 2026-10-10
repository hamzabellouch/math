import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFreeStep

namespace OAI

/-! # Strong continuity of the moving-scale free propagator

Continuity is joint in the positive starting scale, forward time, and input.
No operator-norm continuity of Schrödinger evolution is asserted.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

abbrev ExpandingFreeParameters := {L : ℝ // 1 ≤ L} × NNReal

noncomputable def expandingFreeFamily (a b k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (p : ExpandingFreeParameters) : FourierL2 →L[ℂ] FourierL2 :=
  expandingFreeStep a b k p.1.1 p.2 ha hk p.1.2 p.2.2

theorem expandingFreeFamily_apply_coordinate (a b k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (p : ExpandingFreeParameters) (f : FourierL2) (n : frequencyLattice) :
    expandingFreeFamily a b k ha hk p f n =
      expandingFreeAmplitude a b p.2 *
        (expandingScaleRatio a k p.1.1 (expandingRadius p.1.1 p.2) n : ℂ) *
          schrodingerMultiplier (expandingFreeTime p.1.1 p.2) n * f n := by
  unfold expandingFreeFamily
  change expandingFreeAmplitude a b p.2 *
      ((expandingScaleRatio a k p.1.1 (expandingRadius p.1.1 p.2) n : ℂ) *
        (schrodingerMultiplier (expandingFreeTime p.1.1 p.2) n * f n)) = _
  ring

private theorem continuous_weight_on_positive (a k : ℝ) (n : frequencyLattice) :
    Continuous (fun L : {L : ℝ // 0 < L} => expandingSobolevWeight a k L.1 n) := by
  have hlow : Continuous (fun L : {L : ℝ // 0 < L} => L.1 ^ (2 * a)) :=
    continuous_subtype_val.rpow_const (fun L => Or.inl L.2.ne')
  have hhigh : Continuous (fun L : {L : ℝ // 0 < L} => L.1 ^ (12 - 2 * k)) :=
    continuous_subtype_val.rpow_const (fun L => Or.inl L.2.ne')
  unfold expandingSobolevWeight expandingSobolevWeightSq
  exact continuous_const.mul (Real.continuous_sqrt.comp
    ((hlow.mul continuous_const).add (hhigh.mul continuous_const)))

private theorem continuous_family_coordinate (a b k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (f : FourierL2) (n : frequencyLattice) :
    Continuous (fun p : ExpandingFreeParameters => expandingFreeFamily a b k ha hk p f n) := by
  have hL : Continuous (fun p : ExpandingFreeParameters => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hs : Continuous (fun p : ExpandingFreeParameters => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hR : Continuous (fun p : ExpandingFreeParameters => expandingRadius p.1.1 p.2) := by
    unfold expandingRadius
    exact hL.mul (Real.continuous_exp.comp (hs.div_const 2))
  have hLp (p : ExpandingFreeParameters) : 0 < p.1.1 := lt_of_lt_of_le zero_lt_one p.1.2
  have hRp (p : ExpandingFreeParameters) : 0 < expandingRadius p.1.1 p.2 :=
    mul_pos (hLp p) (Real.exp_pos _)
  have hwL : Continuous (fun p : ExpandingFreeParameters => expandingSobolevWeight a k p.1.1 n) :=
    (continuous_weight_on_positive a k n).comp (hL.subtype_mk hLp)
  have hwR : Continuous (fun p : ExpandingFreeParameters =>
      expandingSobolevWeight a k (expandingRadius p.1.1 p.2) n) :=
    (continuous_weight_on_positive a k n).comp (hR.subtype_mk hRp)
  have hratio : Continuous (fun p : ExpandingFreeParameters =>
      expandingScaleRatio a k p.1.1 (expandingRadius p.1.1 p.2) n) :=
    hwR.div hwL (fun p => (expandingSobolevWeight_pos a k p.1.1 p.1.2 n).ne')
  have hamp : Continuous (fun p : ExpandingFreeParameters => expandingFreeAmplitude a b p.2) := by
    unfold expandingFreeAmplitude
    fun_prop
  have htime : Continuous (fun p : ExpandingFreeParameters => expandingFreeTime p.1.1 p.2) := by
    unfold expandingFreeTime
    exact (hL.rpow_const (fun p => Or.inl (hLp p).ne')).mul
      (continuous_const.sub (Real.continuous_exp.comp hs.neg))
  simp only [expandingFreeFamily_apply_coordinate]
  exact (((hamp.mul (Complex.continuous_ofReal.comp hratio)).mul
    ((continuous_schrodingerMultiplier n).comp htime)).mul continuous_const)

private theorem family_coordinate_bound (a b k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (p : ExpandingFreeParameters) (f : FourierL2) (n : frequencyLattice)
    (T : ℝ) (hsT : (p.2 : ℝ) ≤ T) :
    ‖expandingFreeFamily a b k ha hk p f n‖ ≤ Real.exp (a * T / 2) * ‖f n‖ := by
  have hratio := expandingScaleRatio_le a k p.1.1 (expandingRadius p.1.1 p.2)
    ha hk p.1.2 (expandingRadius_ge p.1.1 p.2 p.1.2 p.2.2) n
  have hR : expandingRadius p.1.1 p.2 / p.1.1 = Real.exp ((p.2 : ℝ) / 2) := by
    unfold expandingRadius
    field_simp [(lt_of_lt_of_le zero_lt_one p.1.2).ne']
  rw [hR, ← Real.exp_mul] at hratio
  have hamp : Real.exp (-a * (p.2 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [p.2.2])
  rw [expandingFreeFamily_apply_coordinate, norm_mul, norm_mul, norm_mul,
    expandingFreeAmplitude_norm, schrodingerMultiplier_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (expandingScaleRatio_nonneg a k p.1.1
      (expandingRadius p.1.1 p.2) p.1.2 (expandingRadius_ge _ _ p.1.2 p.2.2) n)]
  calc
    _ ≤ 1 * Real.exp ((p.2 : ℝ) / 2 * a) * ‖f n‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hamp hratio (expandingScaleRatio_nonneg a k p.1.1
          (expandingRadius p.1.1 p.2) p.1.2 (expandingRadius_ge _ _ p.1.2 p.2.2) n)
          (by norm_num)) (norm_nonneg _)
    _ ≤ Real.exp (a * T / 2) * ‖f n‖ := by
      simp only [one_mul]
      gcongr
      nlinarith

/-- Each fixed input has a strongly continuous free orbit, jointly in scale and time. -/
theorem continuous_expandingFreeFamily (a b k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (f : FourierL2) :
    Continuous (fun p : ExpandingFreeParameters => expandingFreeFamily a b k ha hk p f) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let K := Real.exp (a * ((p₀.2 : ℝ) + 1) / 2)
  have hK : 0 < K := Real.exp_pos _
  have hnear : ∀ᶠ p : ExpandingFreeParameters in 𝓝 p₀, (p.2 : ℝ) < (p₀.2 : ℝ) + 1 :=
    ((continuous_subtype_val.comp continuous_snd).continuousAt.tendsto).eventually
      (eventually_lt_nhds (by change (p₀.2 : ℝ) < (p₀.2 : ℝ) + 1; linarith))
  have hdom : Summable (fun n : frequencyLattice => 4 * K ^ 2 * ‖f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mul_left (4 * K ^ 2)
  have hb : ∀ᶠ p : ExpandingFreeParameters in 𝓝 p₀, ∀ n,
      ‖expandingFreeFamily a b k ha hk p f n - expandingFreeFamily a b k ha hk p₀ f n‖ ^ 2 ≤
        4 * K ^ 2 * ‖f n‖ ^ 2 := by
    filter_upwards [hnear] with p hp n
    have hpB := family_coordinate_bound a b k ha hk p f n ((p₀.2 : ℝ) + 1) hp.le
    have hqB := family_coordinate_bound a b k ha hk p₀ f n ((p₀.2 : ℝ) + 1) (by linarith)
    have hdiff := norm_sub_le (expandingFreeFamily a b k ha hk p f n)
      (expandingFreeFamily a b k ha hk p₀ f n)
    change ‖expandingFreeFamily a b k ha hk p f n‖ ≤ K * ‖f n‖ at hpB
    change ‖expandingFreeFamily a b k ha hk p₀ f n‖ ≤ K * ‖f n‖ at hqB
    have hdiff' : ‖expandingFreeFamily a b k ha hk p f n -
        expandingFreeFamily a b k ha hk p₀ f n‖ ≤ 2 * K * ‖f n‖ := by linarith
    calc
      _ ≤ (2 * K * ‖f n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdiff' 2
      _ = _ := by ring
  have hlim := tendsto_tsum_of_dominated_convergence hdom
    (f := fun p n => ‖expandingFreeFamily a b k ha hk p f n -
      expandingFreeFamily a b k ha hk p₀ f n‖ ^ 2) (g := fun _ => (0 : ℝ)) (𝓕 := 𝓝 p₀)
    (by
      intro n
      have hc : Continuous (fun p : ExpandingFreeParameters =>
          ‖expandingFreeFamily a b k ha hk p f n -
            expandingFreeFamily a b k ha hk p₀ f n‖ ^ 2) :=
        (((continuous_family_coordinate a b k ha hk f n).sub continuous_const).norm.pow 2)
      simpa using (hc.continuousAt (x := p₀)).tendsto)
    (by
      filter_upwards [hb] with p hp n
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hp n)
  have hsq : Tendsto (fun p => ‖expandingFreeFamily a b k ha hk p f -
      expandingFreeFamily a b k ha hk p₀ f‖ ^ 2) (𝓝 p₀) (𝓝 0) := by
    have heq (p : ExpandingFreeParameters) := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (expandingFreeFamily a b k ha hk p f - expandingFreeFamily a b k ha hk p₀ f)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] at heq
    simpa only [heq, tsum_zero] using hlim
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn' : Tendsto (fun p => ‖expandingFreeFamily a b k ha hk p f -
      expandingFreeFamily a b k ha hk p₀ f‖) (𝓝 p₀) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

/-- Strong continuity for varying inputs, without an operator-norm assertion. -/
theorem continuous_expandingFreeFamily_uncurry (a b k : ℝ) (ha : 0 < a) (hk : 8 < k) :
    Continuous (fun p : ExpandingFreeParameters × FourierL2 =>
      expandingFreeFamily a b k ha hk p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu : ∀ᶠ q : ExpandingFreeParameters × FourierL2 in 𝓝 p, dist q.2 p.2 < ε / 2 :=
    continuous_snd.continuousAt.tendsto.eventually (Metric.ball_mem_nhds p.2 (by linarith))
  have hs : ∀ᶠ q : ExpandingFreeParameters × FourierL2 in 𝓝 p,
      dist (expandingFreeFamily a b k ha hk q.1 p.2)
        (expandingFreeFamily a b k ha hk p.1 p.2) < ε / 2 :=
    (((continuous_expandingFreeFamily a b k ha hk p.2).comp continuous_fst).continuousAt.tendsto).eventually
      (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [hu, hs] with q hqu hqs
  have hcontract : ‖expandingFreeFamily a b k ha hk q.1 (q.2 - p.2)‖ ≤ ‖q.2 - p.2‖ := by
    have he := expandingFreeStep_norm_bound a b k q.1.1.1 q.1.2 ha hk q.1.1.2 q.1.2.2 (q.2 - p.2)
    exact he.trans (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [q.1.2.2])))
  calc
    _ ≤ dist (expandingFreeFamily a b k ha hk q.1 q.2)
        (expandingFreeFamily a b k ha hk q.1 p.2) +
      dist (expandingFreeFamily a b k ha hk q.1 p.2)
        (expandingFreeFamily a b k ha hk p.1 p.2) := dist_triangle _ _ _
    _ ≤ dist q.2 p.2 + dist (expandingFreeFamily a b k ha hk q.1 p.2)
        (expandingFreeFamily a b k ha hk p.1 p.2) := by
      apply add_le_add_left
      simpa only [dist_eq_norm, ← map_sub] using hcontract
    _ < ε := by linarith

end DefocusingNLS

end OAI
