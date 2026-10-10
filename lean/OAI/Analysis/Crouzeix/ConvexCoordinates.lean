import Mathlib
import OAI.Analysis.Crouzeix.ConformalCollar

namespace OAI

/-! Convex Coordinates. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem convex_image_subdisk {U : Set ℂ} (hconv : Convex ℝ U)
    {f h : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hbij : BijOn h (ball 0 1) U)
    (hinv : InvOn h f U (ball 0 1)) {r : ℝ} (hr1 : r ≤ 1) :
    Convex ℝ (h '' ball 0 r) := by
  rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩ a b ha hb hab
  have hvn : ‖v‖ < r := mem_ball_zero_iff.mp hv
  have hwn : ‖w‖ < r := mem_ball_zero_iff.mp hw
  obtain ⟨s, hslow, hsr⟩ := exists_between (max_lt hvn hwn)
  have hs : 0 < s := (norm_nonneg v).trans_lt (lt_of_le_of_lt (le_max_left _ _) hslow)
  have hvs : ‖v‖ < s := (le_max_left _ _).trans_lt hslow
  have hws : ‖w‖ < s := (le_max_right _ _).trans_lt hslow
  have hscale : ∀ z t : ℂ, ‖t‖ < s → z ∈ ball 0 1 → z * (t / (s : ℂ)) ∈ ball 0 1 := by
    intro z t ht hz
    rw [mem_ball_zero_iff, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have hc : ‖t‖ / s < 1 := (div_lt_one hs).mpr ht
    calc
      ‖z‖ * (‖t‖ / s) ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hc.le (norm_nonneg _)
      _ < 1 := by simpa only [mul_one] using mem_ball_zero_iff.mp hz
  let p : ℂ → ℂ := fun z => a • h (z * (v / (s : ℂ))) + b • h (z * (w / (s : ℂ)))
  have hpU : MapsTo p (ball 0 1) U := fun z hz =>
    hconv (hbij.mapsTo (hscale z v hvs hz)) (hbij.mapsTo (hscale z w hws hz)) ha hb hab
  have hpD : DifferentiableOn ℂ p (ball 0 1) := by
    intro z hz
    have h₁ : DifferentiableAt ℂ (fun z => h (z * (v / (s : ℂ)))) z := ((hh _ (hscale z v hvs hz)).differentiableAt
      (isOpen_ball.mem_nhds (hscale z v hvs hz))).comp z (differentiableAt_id.mul_const _)
    have h₂ : DifferentiableAt ℂ (fun z => h (z * (w / (s : ℂ)))) z := ((hh _ (hscale z w hws hz)).differentiableAt
      (isOpen_ball.mem_nhds (hscale z w hws hz))).comp z (differentiableAt_id.mul_const _)
    exact ((h₁.const_smul a).add (h₂.const_smul b)).differentiableWithinAt
  have hfmap : MapsTo f U (ball 0 1) := (hbij.symm hinv).mapsTo
  have hφD : DifferentiableOn ℂ (f ∘ p) (ball 0 1) := hf.comp hpD hpU
  have hφmap : MapsTo (f ∘ p) (ball 0 1) (closedBall 0 1) :=
    fun z hz => ball_subset_closedBall (hfmap (hpU hz))
  have hp0 : p 0 = h 0 := by simp only [p, zero_mul, ← add_smul, hab, one_smul]
  have hφ0 : (f ∘ p) 0 = 0 := by
    rw [comp_apply, hp0]
    exact hinv.2 (mem_ball_self zero_lt_one)
  have hs1 : ‖(s : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact hsr.trans_le hr1
  have hn := Complex.norm_le_norm_of_mapsTo_ball hφD hφmap hφ0 hs1
  have hps : p (s : ℂ) = a • h v + b • h w := by
    have hn : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [p, mul_div_cancel₀ _ hn]
  have hpUs : a • h v + b • h w ∈ U := hps ▸ hpU (mem_ball_zero_iff.mpr hs1)
  refine ⟨f (a • h v + b • h w), ?_, hinv.1 hpUs⟩
  apply mem_ball_zero_iff.mpr
  have he : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
  rw [comp_apply, hps, he] at hn
  exact hn.trans_lt hsr

end CrouzeixHilbert.Conformal

end

end OAI
