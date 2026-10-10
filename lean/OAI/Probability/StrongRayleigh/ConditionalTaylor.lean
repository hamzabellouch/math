import OAI.Probability.StrongRayleigh.CharacteristicTaylor

namespace OAI

universe u_1

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Problem336AdditiveD139
namespace CharacteristicTaylor

theorem abs_exp_neg_sub_one_add_le {s : ℝ} (hs : 0 ≤ s) :
    |Real.exp (-s) - 1 + s| ≤ s ^ 2 := by
  by_cases hs1 : s ≤ 1
  · simpa [Real.norm_eq_abs, abs_of_nonneg hs] using
      (Real.norm_exp_sub_one_sub_id_le (x := -s) (by simpa [Real.norm_eq_abs, abs_of_nonneg hs] using hs1))
  · have h1 : 1 ≤ s := le_of_lt (lt_of_not_ge hs1)
    have he0 := Real.exp_pos (-s)
    have he1 : Real.exp (-s) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
    rw [abs_of_nonneg (by linarith)]
    nlinarith

section Conditional

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {X : Ω → ℝ}

lemma integrable_exp_I_mul (hX : Integrable X μ) :
    Integrable (fun ω => Complex.exp (Complex.I * (X ω : ℂ))) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · have hc : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by fun_prop
    exact hc.comp_aestronglyMeasurable hX.aestronglyMeasurable
  · filter_upwards with ω
    simp

theorem condExp_quadratic_remainder_le (hm : m ≤ mΩ)
    (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (X a : ℂ)) | m] ω - 1 -
          Complex.I * (μ[X | m] ω : ℂ) +
          (μ[fun a => (X a) ^ 2 | m] ω : ℂ) / 2‖ ≤
        μ[fun a => |X a| ^ 3 | m] ω / 6 := by
  let e : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω : ℂ))
  let c : Ω → ℂ := fun ω => (X ω : ℂ)
  let q : Ω → ℂ := fun ω => ((X ω) ^ 2 : ℝ)
  let R : Ω → ℂ := e - (fun _ => 1) - Complex.I • c + (1 / 2 : ℂ) • q
  have he : Integrable e μ := integrable_exp_I_mul hX
  have hc : Integrable c μ := hX.ofReal
  have hq : Integrable q μ := hX2.ofReal
  have hR : Integrable R μ := ((he.sub (integrable_const 1)).sub (hc.smul Complex.I)).add
      (hq.smul (1 / 2 : ℂ))
  have hbound : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 / 6 : ℝ) * |X ω| ^ 3 := by
    filter_upwards with ω
    simpa [R, e, c, q, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_pow, div_eq_mul_inv, mul_comm] using norm_exp_I_mul_sub_quadratic (X ω)
  have hmono := condExp_mono hR.norm (hX3.const_mul (1 / 6)) hbound (m := m)
  have hscale := condExp_smul (1 / 6 : ℝ) (fun ω => |X ω| ^ 3) m (μ := μ)
  have hcE := Complex.ofRealCLM.comp_condExp_comm hX (m := m)
  have hqE := Complex.ofRealCLM.comp_condExp_comm hX2 (m := m)
  have hR1 := condExp_sub he (integrable_const (1 : ℂ)) m
  have hR2 := condExp_sub (he.sub (integrable_const (1 : ℂ))) (hc.smul Complex.I) m
  have hR3 := condExp_add ((he.sub (integrable_const (1 : ℂ))).sub (hc.smul Complex.I))
      (hq.smul (1 / 2 : ℂ)) m
  have hi := condExp_smul Complex.I c m (μ := μ)
  have hh := condExp_smul (1 / 2 : ℂ) q m (μ := μ)
  filter_upwards [norm_condExp_le (μ := μ) (m := m) R, hmono, hscale,
    hcE, hqE, hR1, hR2, hR3, hi, hh] with ω hn hb hs hcω hqω h1 h2 h3 hiω hhω
  have hce : μ[c | m] ω = (μ[X | m] ω : ℂ) := by
    simpa [c, Function.comp_def] using hcω.symm
  have hqe : μ[q | m] ω = (μ[fun a => X a ^ 2 | m] ω : ℂ) := by
    simpa [q, Function.comp_def] using hqω.symm
  have hRe : μ[R | m] ω = μ[e | m] ω - 1 - Complex.I * (μ[X | m] ω : ℂ) +
      (μ[fun a => X a ^ 2 | m] ω : ℂ) / 2 := by
    change μ[e - (fun _ => 1) - Complex.I • c + (1 / 2 : ℂ) • q | m] ω = _
    rw [h3]
    simp only [Pi.add_apply]
    rw [h2]
    simp only [Pi.sub_apply]
    rw [h1, hiω, hhω]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm,
      hce, hqe]
    ring
  rw [hRe] at hn
  have hb' : μ[fun a => ‖R a‖ | m] ω ≤ μ[fun a => |X a| ^ 3 | m] ω / 6 := by
    calc
      _ ≤ μ[fun a => (1 / 6 : ℝ) * |X a| ^ 3 | m] ω := hb
      _ = _ := by
        change μ[(1 / 6 : ℝ) • (fun a => |X a| ^ 3) | m] ω = _
        rw [hs]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
  exact hn.trans hb'

theorem conditional_characteristic_bound (hm : m ≤ mΩ)
    (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ)
    (hmean : μ[X | m] =ᵐ[μ] fun _ => 0) {v : ℝ} (hv : 0 ≤ v) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (X a : ℂ)) | m] ω -
          (Real.exp (-v / 2) : ℂ)‖ ≤
        μ[fun a => |X a| ^ 3 | m] ω / 6 +
          |μ[fun a => (X a) ^ 2 | m] ω - v| / 2 + v ^ 2 / 4 := by
  have hg : ‖(1 : ℂ) - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ)‖ ≤ v ^ 2 / 4 := by
    have hg0 := abs_exp_neg_sub_one_add_le (s := v / 2) (by positivity)
    have heq : (1 : ℂ) - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ) =
        ((-(Real.exp (-(v / 2)) - 1 + v / 2) : ℝ) : ℂ) := by
      push_cast
      rw [neg_div]
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    convert hg0 using 1; ring
  filter_upwards [condExp_quadratic_remainder_le hm hX hX2 hX3, hmean] with ω hr hmω
  rw [hmω] at hr
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at hr
  let a : ℂ := μ[fun a => Complex.exp (Complex.I * (X a : ℂ)) | m] ω
  let q : ℝ := μ[fun a => (X a) ^ 2 | m] ω
  change ‖a - (Real.exp (-v / 2) : ℂ)‖ ≤ _
  calc
    _ = ‖(a - 1 + (q : ℂ) / 2) + ((v - q : ℝ) : ℂ) / 2 +
        (1 - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ))‖ := by
          congr 1
          push_cast
          ring
    _ ≤ ‖a - 1 + (q : ℂ) / 2‖ + ‖((v - q : ℝ) : ℂ) / 2‖ +
        ‖1 - (v : ℂ) / 2 - (Real.exp (-v / 2) : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ μ[fun a => |X a| ^ 3 | m] ω / 6 + |q - v| / 2 + v ^ 2 / 4 := by
      have hnorm : ‖((v - q : ℝ) : ℂ) / 2‖ = |q - v| / 2 := by
        simp only [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      rw [hnorm]
      exact add_le_add (add_le_add hr le_rfl) hg

end Conditional
end CharacteristicTaylor
end Problem336AdditiveD139

end

end OAI
