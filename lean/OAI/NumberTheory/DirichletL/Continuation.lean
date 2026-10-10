import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import OAI.NumberTheory.DirichletL.Supremum

namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))

def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)

theorem rpow_isBigO_atTop_of_le {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using
    Real.rpow_le_rpow_of_exponent_le hx h

theorem common_signal_bound (J f : ℝ → ℂ) (a b : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ a))
    (herror : (fun x => J x - f x) =O[atTop] (fun x : ℝ => x ^ b)) :
    f =O[atTop] (fun x : ℝ => x ^ max a b) := by
  have h₁ := hJ.trans (rpow_isBigO_atTop_of_le (le_max_left a b))
  have h₂ := herror.trans (rpow_isBigO_atTop_of_le (le_max_right a b))
  simpa only [sub_sub_cancel] using h₁.sub h₂

theorem common_signal_bound_with_margin (J f : ℝ → ℂ) (β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - Supremum.continuationMargin β ω σ)) := by
  simpa only [Supremum.max_signal_exponents] using
    common_signal_bound J f (7 / 8 + c + ω) (β + c - σ) hJ herror

theorem signalMellin_convergent (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) {s : ℂ} (hs : a < s.re) :
    MellinConvergent f (-(s + (c : ℂ))) := by
  apply mellinConvergent_of_isBigO_rpow (a := -(a+c))
    (b := (-(s + (c : ℂ))).re - 1) hlocal
  · simpa only [neg_neg] using htop
  · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  · exact hzero _
  · linarith

theorem signalMellin_analytic (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    AnalyticOnNhd ℂ (signalMellin f c) {s : ℂ | a < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt a)).2
  intro s hs
  have hd : DifferentiableAt ℂ (mellin f) (-(s + (c : ℂ))) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -(a+c))
      (b := (-(s + (c : ℂ))).re - 1) hlocal
    · simpa only [neg_neg] using htop
    · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      change a < s.re at hs
      linarith
    · exact hzero _
    · linarith
  exact (hd.comp s ((differentiableAt_id.add_const (c : ℂ)).neg)).differentiableWithinAt

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

theorem nonzero_of_regularized_signal (a b c : ℝ)
    (L Lregular R W : ℂ → ℂ) (f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | a < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f)
    (heq : ∀ s : ℂ, max a b < s.re →
      Lregular s * signalMellin f c s = R s * W s)
    {ρ : ℂ} (hρ : a < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ)
    (hRρ : R ρ ≠ 0) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hid := product_identity_on_halfPlane a b Lregular (signalMellin f c)
    (fun s => R s * W s) hL (signalMellin_analytic f a c hlocal htop hzero)
    (hR.mul hW) heq hρ
  intro hz
  change Lregular ρ * signalMellin f c ρ = R ρ * W ρ at hid
  rw [hregular, hz, mul_zero, zero_mul] at hid
  exact (mul_ne_zero hRρ hWρ) hid.symm

theorem multiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (h : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : H s ≠ 0 := by
  intro hz
  simp [hz] at h
  norm_num at h

def gaussianMultiplier (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s

theorem gaussianMultiplier_analytic {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) : AnalyticOnNhd ℂ (gaussianMultiplier H) U := by
  exact ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp.mul hH

theorem gaussianMultiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (hH : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : gaussianMultiplier H s ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (multiplier_ne_zero hH)

theorem nonzero_of_common_signal (β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re})
    (hR : AnalyticOnNhd ℂ R
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re})
    (hcontract : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ, max (β - Supremum.continuationMargin β ω σ) 1 < s.re →
      Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ} (hρ : β - Supremum.continuationMargin β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) : L ρ ≠ 0 := by
  have hboundary := Supremum.continuation_boundary_gt (β := β) (σ := σ) hω
  have hH' : AnalyticOnNhd ℂ H
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re} :=
    hH.mono (fun s hs => lt_trans hboundary hs)
  have htop : f =O[atTop] (fun x : ℝ =>
      x ^ ((β - Supremum.continuationMargin β ω σ) + c)) := by
    have hexp : (β - Supremum.continuationMargin β ω σ) + c =
        β + c - Supremum.continuationMargin β ω σ := by ring
    simpa only [hexp] using common_signal_bound_with_margin J f β ω σ c hJ herror
  exact nonzero_of_regularized_signal _ 1 c L Lregular R (gaussianMultiplier H) f
    hL hR (gaussianMultiplier_analytic hH') hlocal htop hzero heq hρ hregular
    hRρ (gaussianMultiplier_ne_zero (hcontract ρ (lt_trans hboundary hρ)))

end SevenEighths.Continuation

end

end OAI
