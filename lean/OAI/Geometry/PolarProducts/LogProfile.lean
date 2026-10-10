import OAI.Geometry.PolarProducts.HolomorphicBalls

namespace OAI

universe u50 u51

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

namespace SmoothLogProfile
noncomputable section

variable (b l u : ℝ)

def cutoff (t : ℝ) : ℝ := Real.smoothTransition ((t - l) / (u - l))

def slope (t : ℝ) : ℝ := b + cutoff l u t * (Real.exp t - b)

def profile (t : ℝ) : ℝ := Real.exp u + ∫ s in u..t, slope b l u s

theorem cutoff_smooth : ContDiff ℝ ∞ (cutoff l u) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem slope_smooth : ContDiff ℝ ∞ (slope b l u) :=
  contDiff_const.add ((cutoff_smooth l u).mul (Real.contDiff_exp.sub contDiff_const))

theorem cutoff_mem (t : ℝ) : cutoff l u t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_zero (hlu : l < u) {t : ℝ} (ht : t ≤ l) : cutoff l u t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu.le)

theorem cutoff_one (hlu : l < u) {t : ℝ} (ht : u ≤ t) : cutoff l u t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hlu)).mpr (by linarith)

theorem cutoff_monotone (hlu : l < u) : Monotone (cutoff l u) := by
  intro x y hxy
  exact Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hxy l) (sub_nonneg.mpr hlu.le))

theorem slope_left (hlu : l < u) {t : ℝ} (ht : t ≤ l) : slope b l u t = b := by
  simp [slope, cutoff_zero l u hlu ht]

theorem slope_right (hlu : l < u) {t : ℝ} (ht : u ≤ t) : slope b l u t = Real.exp t := by
  simp [slope, cutoff_one l u hlu ht]

theorem slope_pos (hb : 0 < b) (t : ℝ) : 0 < slope b l u t := by
  have hc := cutoff_mem l u t
  have he := Real.exp_pos t
  by_cases h : cutoff l u t = 1
  · simpa [slope, h] using he
  have hp : 0 < (1 - cutoff l u t) * b := mul_pos (sub_pos.mpr (lt_of_le_of_ne hc.2 h)) hb
  have hq : 0 ≤ cutoff l u t * Real.exp t := mul_nonneg hc.1 he.le
  unfold slope
  nlinarith

theorem slope_monotone (hlu : l < u) (hbl : b ≤ Real.exp l) : Monotone (slope b l u) := by
  intro x y hxy
  by_cases hyl : y ≤ l
  · rw [slope_left b l u hlu (hxy.trans hyl), slope_left b l u hlu hyl]
  have hly : l ≤ y := (not_le.mp hyl).le
  have hey : b ≤ Real.exp y := hbl.trans (Real.exp_le_exp.mpr hly)
  by_cases hxl : x ≤ l
  · rw [slope_left b l u hlu hxl]
    exact le_add_of_nonneg_right (mul_nonneg (cutoff_mem l u y).1 (sub_nonneg.mpr hey))
  have hlx : l ≤ x := (not_le.mp hxl).le
  have hex : b ≤ Real.exp x := hbl.trans (Real.exp_le_exp.mpr hlx)
  unfold slope
  apply add_le_add le_rfl
  exact mul_le_mul (cutoff_monotone l u hlu hxy)
    (sub_le_sub_right (Real.exp_le_exp.mpr hxy) b) (sub_nonneg.mpr hex) (cutoff_mem l u y).1

theorem hasDerivAt_profile (t : ℝ) : HasDerivAt (profile b l u) (slope b l u t) t := by
  have hd : HasDerivAt (fun t => ∫ s in u..t, slope b l u s) (slope b l u t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (slope_smooth b l u).continuous.intervalIntegrable _ _
    · exact (slope_smooth b l u).continuous.stronglyMeasurableAtFilter _ _
    · exact (slope_smooth b l u).continuous.continuousAt
  exact hd.const_add _

@[simp] theorem deriv_profile : deriv (profile b l u) = slope b l u :=
  funext (fun t => (hasDerivAt_profile b l u t).deriv)

theorem profile_smooth : ContDiff ℝ ∞ (profile b l u) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (hasDerivAt_profile b l u t).differentiableAt,
    deriv_profile b l u ▸ slope_smooth b l u⟩

theorem deriv_profile_pos (hb : 0 < b) (t : ℝ) : 0 < deriv (profile b l u) t := by
  rw [deriv_profile]
  exact slope_pos b l u hb t

theorem second_deriv_profile_nonneg (hlu : l < u) (hbl : b ≤ Real.exp l) (t : ℝ) :
    0 ≤ deriv (deriv (profile b l u)) t := by
  rw [deriv_profile]
  exact (slope_monotone b l u hlu hbl).deriv_nonneg

theorem profile_sub (s t : ℝ) :
    profile b l u t - profile b l u s = ∫ x in s..t, slope b l u x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((slope_smooth b l u).continuous.intervalIntegrable (μ := volume) u s)
    ((slope_smooth b l u).continuous.intervalIntegrable s t)
  unfold profile
  linarith

theorem profile_right (hlu : l < u) {t : ℝ} (ht : u ≤ t) :
    profile b l u t = Real.exp t := by
  have he : (∫ s in u..t, slope b l u s) = Real.exp t - Real.exp u := by
    calc
      _ = ∫ s in u..t, Real.exp s := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact slope_right b l u hlu (le_trans (by simp [ht]) hs.1)
      _ = Real.exp t - Real.exp u := by simp
  simp [profile, he]

theorem profile_left (hlu : l < u) {t : ℝ} (ht : t ≤ l) :
    profile b l u t = b * t + (profile b l u l - b * l) := by
  have he : (∫ s in t..l, slope b l u s) = (l - t) * b := by
    calc
      _ = ∫ s in t..l, b := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact slope_left b l u hlu (le_trans hs.2 (by simp [ht]))
      _ = (l - t) * b := by simp
  have hdiff := profile_sub b l u t l
  rw [he] at hdiff
  nlinarith

end
end SmoothLogProfile

namespace ComplexPotential

open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u50} {F : Type u51} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem exists_ball_from_holomorphic_zero {Ω : Set E} (hΩ : IsOpen Ω) (hΩ0 : (0 : E) ∈ Ω)
    {f : E → F} (hf : AnalyticOnNhd ℂ f Ω)
    (hfzero : ∀ x ∈ Ω, f x = 0 ↔ x = 0)
    {k : ℕ} (hk : 1 ≤ k) (ho : f =O[𝓝 (0 : E)] (fun x : E => ‖x‖^k))
    (hcompact : ∀ s : ℝ, 0 < s → s < 1 → IsCompact {x | x ∈ Ω ∧ ‖f x‖^2 ≤ s})
    {a : ℝ} (ha : 0 < a) (hak : a < (k : ℝ)) :
    let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ∃ Q : E ≃ₜ E, ContDiff ℝ ∞ (Q : E → E) ∧ ContDiff ℝ ∞ (Q.symm : E → E) ∧
      (∀ x : E, ‖x‖^2 < a → Q x ∈ Ω ∧ ‖f (Q x)‖^2 < 1) ∧
      ∀ x : E, ‖x‖^2 < a → ∀ v w : E,
        ddc (complexStructure E) (fun y => ‖y‖^2 + ‖f y‖^2) (Q x)
          (fderiv ℝ (Q : E → E) x v) (fderiv ℝ (Q : E → E) x w) =
            standardTensor (complexStructure E) v w := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  let τ : E → ℝ := fun x => ‖f x‖^2
  let U : Set E := {x | x ∈ Ω ∧ τ x < 1}
  have hτsmooth (x : E) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ τ x :=
    (contDiff_norm_sq ℝ).contDiffAt.comp x ((hf x hx).contDiffAt.restrict_scalars ℝ)
  have hτcont : ContinuousOn τ Ω := fun x hx => (hτsmooth x hx).continuousAt.continuousWithinAt
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact inter_mem (hΩ.mem_nhds hx.1)
      ((hτsmooth x hx.1).continuousAt.eventually_lt continuousAt_const hx.2)
  have hf0 : f 0 = 0 := (hfzero 0 hΩ0).mpr rfl
  have hτ0 : τ 0 = 0 := by simp [τ, hf0]
  have hU0 : (0 : E) ∈ U := ⟨hΩ0, by rw [hτ0]; norm_num⟩
  have hτpsh (x : E) (hx : x ∈ U) : IsPSHAt (complexStructure E) τ x := by
    have hn : IsPSHAt (complexStructure F) (fun z : F => ‖z‖^2) (f x) := by
      refine ⟨(contDiff_norm_sq ℝ).contDiffAt, fun v => ?_⟩
      rw [ddc_norm_sq _ (complexStructure_skew), standardTensor_complex_line _ complexStructure_norm]
      exact sq_nonneg _
    apply hn.holomorphic_comp ((hf x hx.1).contDiffAt.restrict_scalars ℝ)
    filter_upwards [hΩ.mem_nhds hx.1] with y hy
    exact (hf y hy).differentiableAt
  have hpos (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) : 0 < τ x := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (fun hh => hx0 ((hfzero x hx.1).mp hh)))
  have hlogpsh (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) :
      IsPSHAt (complexStructure E) (Real.log ∘ τ) x := by
    have hn := isPSHAt_logNormSq (complexStructure F) complexStructure_skew
      complexStructure_norm complexStructure_sq (δ := 0) le_rfl
        (show 0 < ‖f x‖^2 + 0 by simpa [τ] using hpos x hx hx0)
    have hh := hn.holomorphic_comp ((hf x hx.1).contDiffAt.restrict_scalars ℝ) (by
      filter_upwards [hΩ.mem_nhds hx.1] with y hy
      exact (hf y hy).differentiableAt)
    simpa only [logNormSq, add_zero, Function.comp_def, τ] using hh
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  obtain ⟨b, hab, hb1⟩ := exists_between ((div_lt_one hkpos).mpr hak)
  have hb : 0 < b := (div_pos ha hkpos).trans hab
  obtain ⟨l, hbl, hl0⟩ := exists_between (Real.log_neg hb hb1)
  obtain ⟨u, hlu, hu0⟩ := exists_between hl0
  have hble : b ≤ Real.exp l := by
    exact ((Real.log_le_iff_le_exp hb).mp hbl.le)
  let H : E → ℝ := SmoothLogProfile.profile b l u ∘ Real.log ∘ τ
  have hH (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) : IsPSHAt (complexStructure E) H x := by
    exact (hlogpsh x hx hx0).scalar_comp _ complexStructure_sq
      (SmoothLogProfile.profile_smooth b l u).contDiffAt
      (SmoothLogProfile.deriv_profile_pos b l u hb _).le
      (SmoothLogProfile.second_deriv_profile_nonneg b l u hlu hble _)
  have htail (x : E) (hx : x ∈ U) (ht : Real.exp u ≤ τ x) : H x = τ x := by
    have htpos : 0 < τ x := (Real.exp_pos u).trans_le ht
    have hlog : u ≤ Real.log (τ x) := by
      simpa using Real.log_le_log (Real.exp_pos u) ht
    change SmoothLogProfile.profile b l u (Real.log (τ x)) = τ x
    rw [SmoothLogProfile.profile_right b l u hlu hlog, Real.exp_log htpos]
  obtain ⟨C, hC, hCb⟩ := ho.exists_pos
  have hev : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖^k ∧ τ x < Real.exp l := by
    filter_upwards [hCb.bound,
      (hτsmooth 0 hΩ0).continuousAt.eventually_lt continuousAt_const
        (show τ 0 < Real.exp l by rw [hτ0]; exact Real.exp_pos l)] with x hx ht
    exact ⟨by simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hx, ht⟩
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hev
  let ρ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  let C₁ := b * (2 * Real.log C) + (SmoothLogProfile.profile b l u l - b * l)
  have hpole (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) (hnorm : ‖x‖ ≤ ρ) :
      H x ≤ (b * k) * Real.log (‖x‖^2) + C₁ := by
    have hdist : dist x 0 < ε := by rw [dist_zero_right]; exact hnorm.trans_lt (half_lt_self hε)
    obtain ⟨hbound, hsmall⟩ := hεprop hdist
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfxp : 0 < ‖f x‖ := norm_pos_iff.mpr (fun hh => hx0 ((hfzero x hx.1).mp hh))
    have hlogl : Real.log (τ x) ≤ l := (Real.log_le_iff_le_exp (hpos x hx hx0)).mpr hsmall.le
    change SmoothLogProfile.profile b l u (Real.log (τ x)) ≤ _
    rw [SmoothLogProfile.profile_left b l u hlu hlogl]
    have hlg := Real.log_le_log hfxp hbound
    rw [Real.log_mul hC.ne' (pow_pos hxp k).ne', Real.log_pow] at hlg
    have hmul := mul_le_mul_of_nonneg_left hlg hb.le
    dsimp [τ, C₁]
    rw [Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  apply exists_ball_from_logarithmic_pole (complexStructure E) complexStructure_skew
    complexStructure_norm complexStructure_sq hU hU0 hτpsh hτ0 hH
  · intro s hs hs1
    have he : {x | x ∈ U ∧ τ x ≤ s} = {x | x ∈ Ω ∧ ‖f x‖^2 ≤ s} := by
      ext x
      constructor
      · exact fun hx => ⟨hx.1.1, hx.2⟩
      · exact fun hx => ⟨⟨hx.1, hx.2.trans_lt hs1⟩, hx.2⟩
    rw [he]
    exact hcompact s hs hs1
  · exact Real.exp_lt_one_iff.mpr hu0
  · exact hρ
  · exact htail
  · exact hpole
  · exact ha
  · exact (div_lt_iff₀ hkpos).mp hab

end
end ComplexPotential

end LowerBoundInline

end OAI
