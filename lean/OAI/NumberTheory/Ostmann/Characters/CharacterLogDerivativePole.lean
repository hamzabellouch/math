import Mathlib.Analysis.Calculus.LogDeriv
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroSet

namespace OAI

/-! # The exact local poles of a character logarithmic derivative -/

namespace Ostmann

open Filter
open scoped Topology

/-- Removing the actual analytic zero order leaves a nonvanishing analytic factor. -/
theorem PrimitiveComplexCharacter.logDeriv_local_split (χ : PrimitiveComplexCharacter)
    (z : ℂ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      logDeriv χ.L =ᶠ[𝓝[≠] z] fun w =>
        (analyticOrderNatAt χ.L z : ℂ) / (w - z) + logDeriv g w := by
  obtain ⟨g, hg, hgne, he⟩ := (χ.L_analytic z).analyticOrderAt_ne_top.mp (χ.L_order_ne_top z)
  have he' : χ.L =ᶠ[𝓝 z] fun w => (w - z) ^ analyticOrderNatAt χ.L z * g w := by
    simpa only [smul_eq_mul] using he
  have hlog := logDeriv_congr_nhds he'
  refine ⟨g, hg, hgne, ?_⟩
  filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hgne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hgw hgnw hwz
  have hnz : w - z ≠ 0 := sub_ne_zero.mpr hwz
  rw [hw, logDeriv_fun_mul (f := fun u : ℂ => (u - z) ^ analyticOrderNatAt χ.L z)
    (g := g) w (pow_ne_zero _ hnz) hgnw
    ((differentiableAt_id.sub_const z).pow _) hgw.differentiableAt]
  have hp : logDeriv (fun u : ℂ => (u - z) ^ analyticOrderNatAt χ.L z) w =
      (analyticOrderNatAt χ.L z : ℂ) * logDeriv (fun u : ℂ => u - z) w := by
    simpa only [id_eq] using logDeriv_fun_pow
      (f := fun u : ℂ => u - z) (x := w) (differentiableAt_id.sub_const z)
      (analyticOrderNatAt χ.L z)
  rw [hp]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- The residue of L'/L at any point is its actual zero multiplicity. -/
theorem PrimitiveComplexCharacter.logDeriv_residue_limit (χ : PrimitiveComplexCharacter)
    (z : ℂ) : Tendsto (fun w => (w - z) * logDeriv χ.L w) (𝓝[≠] z)
      (𝓝 (analyticOrderNatAt χ.L z : ℂ)) := by
  obtain ⟨g, hg, hgne, hsplit⟩ := χ.logDeriv_local_split z
  have hcont : ContinuousAt (logDeriv g) z :=
    hg.deriv.continuousAt.div hg.continuousAt hgne
  have hlim : Tendsto (fun w => (analyticOrderNatAt χ.L z : ℂ) +
      (w - z) * logDeriv g w) (𝓝[≠] z) (𝓝 (analyticOrderNatAt χ.L z : ℂ)) := by
    have hsub : Tendsto (fun w : ℂ => w - z) (𝓝[≠] z) (𝓝 0) := by
      have hh : Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 (z - z)) := tendsto_id.sub_const z
      simpa only [sub_self] using hh.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds.add
      (hsub.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)))
  apply hlim.congr'
  filter_upwards [hsplit, self_mem_nhdsWithin] with w hw hwz
  rw [hw]
  field_simp [sub_ne_zero.mpr hwz]

end Ostmann

end OAI
