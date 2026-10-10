import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace OAI

universe uAlpha uIota

open Filter
open scoped Topology

namespace Problem326

/-- A positive gap between limiting exponents makes the ratio of powers
 tend to zero, even when the numerator's exponent varies. -/
theorem tendsto_rpow_ratio_zero {α : Type uAlpha} {l : Filter α}
    {h p : α → ℝ} {p₀ q : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ n in l, 0 < h n)
    (hp : Tendsto p l (𝓝 p₀)) (hgap : q < p₀) :
    Tendsto (fun n => h n ^ p n / h n ^ q) l (𝓝 0) := by
  have hlim := hh.rpow (hp.sub_const q) (Or.inr (sub_pos.mpr hgap))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hgap))] at hlim
  apply hlim.congr'
  filter_upwards [hhpos] with n hn
  exact Real.rpow_sub hn (p n) q

/-- A negative limiting exponent gap makes the same ratio diverge. -/
theorem tendsto_rpow_ratio_atTop {α : Type uAlpha} {l : Filter α}
    {h p : α → ℝ} {p₀ q : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ n in l, 0 < h n)
    (hp : Tendsto p l (𝓝 p₀)) (hgap : p₀ < q) :
    Tendsto (fun n => h n ^ p n / h n ^ q) l atTop := by
  have hlim := hh.rpow (tendsto_const_nhds.sub hp)
    (Or.inr (sub_pos.mpr hgap))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hgap))] at hlim
  have hpos : ∀ᶠ n in l, 0 < h n ^ (q - p n) := by
    filter_upwards [hhpos] with n hn
    exact Real.rpow_pos_of_pos hn _
  have hinv := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hpos⟩)
  apply hinv.congr'
  filter_upwards [hhpos] with n hn
  simp only [Function.comp_apply, Real.rpow_sub hn, inv_div]

/-- Little-o form of the varying-exponent comparison. -/
theorem varying_rpow_isLittleO {α : Type uAlpha} {l : Filter α}
    {h p : α → ℝ} {p₀ q : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ n in l, 0 < h n)
    (hp : Tendsto p l (𝓝 p₀)) (hgap : q < p₀) :
    (fun n => h n ^ p n) =o[l] (fun n => h n ^ q) := by
  apply Asymptotics.isLittleO_of_tendsto' _
    (tendsto_rpow_ratio_zero hh hhpos hp hgap)
  filter_upwards [hhpos] with n hn
  intro hz
  exact False.elim ((ne_of_gt (Real.rpow_pos_of_pos hn q)) hz)

/-- Fixed distinct powers are asymptotically separated at zero from the right. -/
theorem rpow_isLittleO_at_zero {p q : ℝ} (hpq : q < p) :
    (fun h : ℝ => h ^ p) =o[𝓝[>] 0] (fun h => h ^ q) :=
  varying_rpow_isLittleO nhdsWithin_le_nhds
    self_mem_nhdsWithin tendsto_const_nhds hpq

/-- The exponents corresponding to any fixed initial state tend to zero. -/
theorem tendsto_log_ratio_zero (x : ℝ) :
    Tendsto (fun h : ℝ => Real.log x / Real.log h) (𝓝[>] 0) (𝓝 0) :=
  Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log x)

/-- One small parameter simultaneously controls every fixed initial exponent
 and a prescribed rate-separation inequality. -/
theorem exists_small_parameter_of_constants {ι : Type uIota} [Finite ι] (x : ι → ℝ)
    {H h₀ B : ℝ} (hH : 0 < H) (hh₀ : 0 < h₀) (hB : 0 < B) (A : ℝ) :
    ∃ h : ℝ, 0 < h ∧ h < h₀ ∧ h < 1 ∧
      (∀ i, |Real.log (x i) / Real.log h| < H) ∧ h ^ H * A < B := by
  have hbase : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlogs : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ i, |Real.log (x i) / Real.log h| < H := by
    apply eventually_all.mpr
    intro i
    have hi := (tendsto_log_ratio_zero (x i)).abs
    simp only [abs_zero] at hi
    exact hi.eventually_lt_const hH
  have hpowers : ∀ᶠ h : ℝ in 𝓝[>] 0, h ^ H * A < B := by
    have hl := (hbase.rpow_const_nhds_zero hH).mul_const A
    simp only [zero_mul] at hl
    exact hl.eventually_lt_const hB
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < h₀ :=
    hbase.eventually_lt_const hh₀
  have hone : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    hbase.eventually_lt_const zero_lt_one
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  exact (hpositive.and (hsmall.and (hone.and (hlogs.and hpowers)))).exists

end Problem326

end OAI
