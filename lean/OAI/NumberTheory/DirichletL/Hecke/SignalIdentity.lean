import OAI.NumberTheory.DirichletL.Hecke.Signal
import OAI.NumberTheory.DirichletL.Hecke.Origin
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

private theorem line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

theorem signalMellin_eq_amplitude (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (signal χ H c) c s = amplitude χ H s := by
  have hF := signalMellin_analytic (signal χ H c) a c
    (signal_locallyIntegrable χ H hH hb c) htop (signal_rapidDecayAtZero χ H hH hb c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (signal χ H c) c) {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (amplitude χ H) {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    have hq := quotient_differentiableAt χ H hH ((le_max_right a 1).trans_lt hz)
    exact ((((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul hq).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y => signalMellin_eq_amplitude_on_line χ H hH hb c a ha htop y)

theorem poleRemoved_mul_signalMellin (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    HeckeOrigin.poleRemoved χ s * signalMellin (signal χ H c) c s =
      (s-1) * gaussianMultiplier H s := by
  have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1, signalMellin_eq_amplitude χ H hH hb c a ha htop hs]
  unfold amplitude quotient gaussianMultiplier
  rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
  have hn := LFunction_ne_zero_of_one_lt_re χ hs1
  field_simp

def targetRegularizer (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then s-1 else 1

def regularL (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then HeckeOrigin.poleRemoved χ s else LFunction χ s

theorem targetRegularizer_entire (χ : Character) : Differentiable ℂ (targetRegularizer χ) := by
  by_cases h : χ.residue = 1
  · have he : targetRegularizer χ = fun z : ℂ => z-1 := by funext z; simp [targetRegularizer, h]
    rw [he]
    exact differentiable_id.sub_const 1
  · have he : targetRegularizer χ = fun _ : ℂ => (1 : ℂ) := by funext z; simp [targetRegularizer, h]
    rw [he]
    exact differentiable_const 1

theorem regularL_entire (χ : Character) : Differentiable ℂ (regularL χ) := by
  by_cases h : χ.residue = 1
  · have he : regularL χ = HeckeOrigin.poleRemoved χ := by funext z; simp [regularL, h]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · have he : regularL χ = LFunction χ := by funext z; simp [regularL, h]
    rw [he]
    exact LFunction_entire_nonprincipal χ h

theorem regularL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    regularL χ s = targetRegularizer χ s * LFunction χ s := by
  by_cases h : χ.residue = 1
  · simp only [regularL, targetRegularizer, h, ite_true]
    exact HeckeOrigin.poleRemoved_eq χ h0 (hpole.resolve_right (not_not.mpr h))
  · simp [regularL, targetRegularizer, h]

theorem targetRegularizer_ne_zero (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : targetRegularizer χ s ≠ 0 := by
  by_cases h : χ.residue = 1
  · simpa only [targetRegularizer, h, ite_true, sub_ne_zero] using
      hpole.resolve_right (not_not.mpr h)
  · simp [targetRegularizer, h]

theorem nonzero_of_probe_bounds (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (β ω σ c : ℝ) (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β-7/8) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x^(7/8+c+ω)))
    (herror : (fun x => J x - signal χ H c x) =O[atTop]
      (fun x : ℝ => x^(β+c-σ)))
    {ρ : ℂ} (hρ : β - Supremum.continuationMargin β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := β - Supremum.continuationMargin β ω σ
  have ha2 : a < 2 := by
    have hp := Supremum.continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
    have h := common_signal_bound_with_margin J (signal χ H c) β ω σ c hJ herror
    convert h using 1; dsimp [a]; ring_nf
  have hHd := hH.differentiableOn
  apply nonzero_of_common_signal β ω σ c hω0 (LFunction χ) (regularL χ)
    (targetRegularizer χ) H J (signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (targetRegularizer_entire χ)).mono (Set.subset_univ _))
    hH hb (signal_locallyIntegrable χ H hHd hb c) (signal_rapidDecayAtZero χ H hHd hb c)
    hJ herror _ hρ _ (targetRegularizer_ne_zero χ hpole)
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [regularL_eq χ h0 (Or.inl h1), signalMellin_eq_amplitude χ H hHd hb c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply regularL_eq χ _ hpole
    intro h
    have hbound := Supremum.continuation_boundary_gt (β := β) (σ := σ) hω0
    rw [h] at hρ
    norm_num at hρ
    linarith

end SevenEighths.HeckeSignal

end

end OAI
