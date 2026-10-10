import OAI.Analysis.IrrationalRotation.Model.ScalarMultiplier
import OAI.Analysis.IrrationalRotation.Analysis.FieldsNorm
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem multiplier_coe (g : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    multiplier g f =ᵐ[μ] fun x => g x • f x := by
  exact (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).coeFn_holder g f

theorem norm_multiplier_le (g : Lp ℂ ∞ μ) :
    ‖(multiplier g : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  apply (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).norm_holder_apply_apply_le g f
    |>.trans
  have h : ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  calc
    ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ * ‖g‖ * ‖f‖
        ≤ 1 * ‖g‖ * ‖f‖ := by gcongr
    _ = ‖g‖ * ‖f‖ := by ring

variable [IsFiniteMeasure μ]

theorem multiplier_indicator_coe (s : Set X) (hs : MeasurableSet s)
    (f : Lp E 2 μ) :
    multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f =ᵐ[μ]
      s.indicator f := by
  filter_upwards [multiplier_coe (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f,
    indicatorConstLp_coeFn (p := ∞) (μ := μ) (hs := hs)
      (hμs := measure_ne_top μ s) (c := (1 : ℂ))] with x hx hi
  rw [hx, hi]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

theorem multiplier_const (c : ℂ) :
    (multiplier (Lp.const ∞ μ c) : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
      c • (1 : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [multiplier_coe (Lp.const ∞ μ c) f,
    Lp.coeFn_const ∞ μ c, Lp.coeFn_smul c f] with x hx hc hs
  simpa only [smul_apply, one_apply_eq_self] using
    hx.trans (by rw [hc]; exact hs.symm)

theorem multiplier_indicator_const (s : Set X) (hs : MeasurableSet s) (c : E) :
    multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) (Lp.const 2 μ c) =
      indicatorConstLp 2 hs (measure_ne_top μ s) c := by
  apply Lp.ext
  filter_upwards [multiplier_indicator_coe s hs (Lp.const 2 μ c),
    Lp.coeFn_const 2 μ c,
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs)
      (hμs := measure_ne_top μ s) (c := c)] with x hx hc hi
  rw [hx, hi]
  by_cases hxs : x ∈ s
  · simpa only [Set.indicator_of_mem hxs, Function.const_apply] using hc
  · simp only [Set.indicator_of_notMem hxs]

omit [IsFiniteMeasure μ] in

theorem norm_sq_eq_integral (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ), L2.inner_def]
  simp only [RCLike.re_to_real, real_inner_self_eq_norm_sq]

theorem norm_indicator_one_sq (s : Set X) (hs : MeasurableSet s) :
    ‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)‖ ^ 2 = μ.real s := by
  rw [norm_sq_eq_integral]
  calc
    (∫ x, ‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ) x‖ ^ 2 ∂μ) =
        ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs)
        (hμs := measure_ne_top μ s) (c := (1 : ℂ))] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]
    _ = μ.real s := by rw [integral_indicator hs]; simp

theorem norm_multiplier_indicator_sq (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    ‖multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f‖ ^ 2 =
      ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [multiplier_indicator_coe s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

theorem ae_norm_apply_const_one_le
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hB : ∀ g : Lp ℂ ∞ μ, Commute B (multiplier g)) :
    ∀ᵐ x ∂μ, ‖B (Lp.const 2 μ (1 : ℂ)) x‖ ≤ ‖B‖ := by
  apply Fields.ae_norm_le_of_local_square_integral (norm_nonneg B)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
  intro s hs
  have hcomm := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ =>
    A (Lp.const 2 μ (1 : ℂ)))
    (hB (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))).eq
  have hid : B (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) =
      multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))
        (B (Lp.const 2 μ (1 : ℂ))) := by
    simpa only [mul_apply_eq_comp, multiplier_indicator_const] using hcomm
  rw [← norm_multiplier_indicator_sq s hs, ← hid]
  calc
    ‖B (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))‖ ^ 2 ≤
        (‖B‖ * ‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)‖) ^ 2 := by
      gcongr
      exact B.le_opNorm _
    _ = ‖B‖ ^ 2 * μ.real s := by rw [mul_pow, norm_indicator_one_sq]

theorem apply_const_eq_smul (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : ℂ) :
    B (Lp.const 2 μ c) = c • B (Lp.const 2 μ (1 : ℂ)) := by
  have hc : Lp.const 2 μ c = c • Lp.const 2 μ (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one, Lp.constₗ_apply] using
      (Lp.constₗ 2 μ ℂ).map_smul c (1 : ℂ)
  rw [hc, map_smul]

theorem exists_multiplier_of_commutes
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hB : ∀ g : Lp ℂ ∞ μ, Commute B (multiplier g)) :
    ∃ g : Lp ℂ ∞ μ, ‖g‖ ≤ ‖B‖ ∧ B = multiplier g := by
  let b : Lp ℂ 2 μ := B (Lp.const 2 μ (1 : ℂ))
  have hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ ‖B‖ := ae_norm_apply_const_one_le B hB
  have hbtop : MemLp (fun x => b x) ∞ μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable b) ‖B‖ hb
  let g : Lp ℂ ∞ μ := hbtop.toLp (fun x => b x)
  have hg : g =ᵐ[μ] b := hbtop.coeFn_toLp
  refine ⟨g, ?_, ?_⟩
  · have hgbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖B‖ := by
      filter_upwards [hg, hb] with x hx hbound
      rw [hx]
      exact hbound
    simpa using Lp.norm_le_of_ae_bound (norm_nonneg B) hgbound
  · have hind : ∀ (c : ℂ) (s : Set X) (hs : MeasurableSet s),
        B (indicatorConstLp 2 hs (measure_ne_top μ s) c) =
          multiplier g (indicatorConstLp 2 hs (measure_ne_top μ s) c) := by
      intro c s hs
      have hcomm := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ =>
        A (Lp.const 2 μ c))
        (hB (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))).eq
      have hid : B (indicatorConstLp 2 hs (measure_ne_top μ s) c) =
          multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) (c • b) := by
        calc
          B (indicatorConstLp 2 hs (measure_ne_top μ s) c) =
              multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))
                (B (Lp.const 2 μ c)) := by
            simpa only [mul_apply_eq_comp, multiplier_indicator_const] using hcomm
          _ = _ := congrArg _ (apply_const_eq_smul B c)
      rw [hid]
      apply Lp.ext
      filter_upwards [multiplier_indicator_coe s hs (c • b), Lp.coeFn_smul c b,
        multiplier_coe g (indicatorConstLp 2 hs (measure_ne_top μ s) c),
        indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs)
          (hμs := measure_ne_top μ s) (c := c), hg] with x hx hsx hmult hi hgb
      rw [hx, hmult, hi, hgb]
      by_cases hxs : x ∈ s
      · simp only [Set.indicator_of_mem hxs, hsx, Pi.smul_apply, smul_eq_mul, mul_comm]
      · simp only [Set.indicator_of_notMem hxs, smul_zero]
    apply ContinuousLinearMap.ext
    apply Lp.induction (by simp) (fun f => B f = multiplier g f)
    · intro c s hs hμs
      simpa only [Lp.simpleFunc.coe_indicatorConst] using hind c s hs
    · intro f₁ f₂ hf₁ hf₂ hd h₁ h₂
      simp only [map_add, h₁, h₂]
    · exact isClosed_eq B.continuous (multiplier g).continuous

omit [IsFiniteMeasure μ] in

theorem multiplier_commute (g h : Lp ℂ ∞ μ) :
    Commute (multiplier g : Lp E 2 μ →L[ℂ] Lp E 2 μ) (multiplier h) := by
  show multiplier g * multiplier h = multiplier h * multiplier g
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [multiplier_coe g (multiplier h f), multiplier_coe h f,
    multiplier_coe h (multiplier g f), multiplier_coe g f] with x hgh hh hhg hg
  simp only [mul_apply_eq_comp, hgh, hh, hhg, hg, smul_smul, mul_comm]

theorem multiplier_injective :
    Function.Injective (multiplier (μ := μ) (E := ℂ)) := by
  intro g h hgh
  have haction := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ =>
    A (Lp.const 2 μ (1 : ℂ))) hgh
  apply Lp.ext
  filter_upwards [multiplier_coe g (Lp.const 2 μ (1 : ℂ)),
    multiplier_coe h (Lp.const 2 μ (1 : ℂ)), Lp.coeFn_const 2 μ (1 : ℂ)] with x hg hh hc
  rw [haction] at hg
  simpa only [hc, Function.const_apply, smul_eq_mul, mul_one] using hg.symm.trans hh

theorem norm_scalar_multiplier (g : Lp ℂ ∞ μ) :
    ‖(multiplier g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ = ‖g‖ := by
  apply le_antisymm (norm_multiplier_le g)
  obtain ⟨h, hh, haction⟩ := exists_multiplier_of_commutes (multiplier g)
    (multiplier_commute g)
  have hgh := multiplier_injective haction
  simpa only [hgh] using hh

end Invariant233.L2Multiplication

end OAI
