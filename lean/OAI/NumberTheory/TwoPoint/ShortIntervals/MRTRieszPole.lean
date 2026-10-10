import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszMangoldt
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszBounds
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaPole

namespace OAI

/-! The actual shifted Riesz integrand has exactly the zeta pole, with
residue equal to the Riesz kernel at the shifted pole. -/

namespace TwoPointCorrelations

open Complex Filter Asymptotics
open scoped Topology

lemma mrt_riesz_integrand_simple_pole {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (mrtZetaRieszIntegrand x u - (fun s =>
      mrtRieszKernel x (1 - (u : ℂ) * Complex.I) / (s - (1 - (u : ℂ) * Complex.I))))
      =O[𝓝[≠] (1 - (u : ℂ) * Complex.I)] (1 : ℂ → ℂ) := by
  let p : ℂ := 1 - (u : ℂ) * Complex.I
  have hadd : Tendsto (fun s : ℂ => s + (u : ℂ) * Complex.I) (𝓝[≠] p) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun s : ℂ => s + (u : ℂ) * Complex.I) := by fun_prop
      have hh := hc.continuousAt.tendsto.mono_left
        (show 𝓝[≠] p ≤ 𝓝 p from nhdsWithin_le_nhds)
      have he : p + (u : ℂ) * Complex.I = 1 := by dsimp [p]; ring
      simpa only [he] using hh
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s + (u : ℂ) * Complex.I ≠ 1
      change s ≠ p at hs
      intro he
      apply hs
      dsimp [p]
      linear_combination he
  have hpole : (fun s : ℂ =>
      -deriv riemannZeta (s + (u : ℂ) * Complex.I) /
        riemannZeta (s + (u : ℂ) * Complex.I) - (s - p)⁻¹)
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have hh := Erdos970.riemannZetaLogDerivResidueBigO.comp_tendsto hadd
    convert hh using 1
    · funext s
      simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply]
      congr 1
      dsimp [p]
      ring
    · rfl
  have hk : DifferentiableAt ℂ (mrtRieszKernel x) p := by
    apply mrt_riesz_kernel_differentiableAt hx
    · intro he
      have hh := congrArg Complex.re he
      norm_num [p] at hh
    · intro he
      have hh := congrArg Complex.re he
      norm_num [p] at hh
    · intro he
      have hh := congrArg Complex.re he
      norm_num [p] at hh
  have hb : mrtRieszKernel x =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    hk.continuousAt.isBigO.mono nhdsWithin_le_nhds
  have hd : (fun s : ℂ => mrtRieszKernel x s - mrtRieszKernel x p)
      =O[𝓝[≠] p] (fun s : ℂ => s - p) := hk.isBigO_sub.mono nhdsWithin_le_nhds
  obtain ⟨C₁, hC₁, h₁⟩ := hpole.exists_nonneg
  obtain ⟨C₂, hC₂, h₂⟩ := hb.exists_nonneg
  obtain ⟨C₃, _, h₃⟩ := hd.exists_nonneg
  apply IsBigO.of_bound (C₁ * C₂ + C₃)
  filter_upwards [h₁.bound, h₂.bound, h₃.bound, self_mem_nhdsWithin] with s hs₁ hs₂ hs₃ hs
  change s ≠ p at hs
  simp only [Pi.one_apply, norm_one, mul_one] at hs₁ hs₂ ⊢
  have hq : ‖(mrtRieszKernel x s - mrtRieszKernel x p) / (s - p)‖ ≤ C₃ := by
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs))).mpr hs₃
  have hid : mrtZetaRieszIntegrand x u s - mrtRieszKernel x p / (s - p) =
      (-deriv riemannZeta (s + (u : ℂ) * Complex.I) /
        riemannZeta (s + (u : ℂ) * Complex.I) - (s - p)⁻¹) * mrtRieszKernel x s +
          (mrtRieszKernel x s - mrtRieszKernel x p) / (s - p) := by
    unfold mrtZetaRieszIntegrand
    ring
  change ‖mrtZetaRieszIntegrand x u s - mrtRieszKernel x p / (s - p)‖ ≤ _
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add (mul_le_mul hs₁ hs₂ (norm_nonneg _) hC₁) hq

end TwoPointCorrelations

end OAI
