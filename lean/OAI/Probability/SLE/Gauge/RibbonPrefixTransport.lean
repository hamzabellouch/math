import OAI.Probability.SLE.Gauge.WholeSausageScaling
import OAI.Probability.SLE.Gauge.RibbonGoodPrefix

namespace OAI

/-! A successful narrow physical prefix is preserved by the exact SLE
spatial/capacity scaling. The front is transported as its actual first hit,
not chosen as a separate completion certificate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage FrontClockChange ScaleTraceLaw FrontSuccessMeasurability

lemma scalePath_at_scaled_time (c : ℝ≥0) (hc : 0 < c) (p : C(ℝ≥0, ℂ)) (t : ℝ≥0) :
    scalePath c p (c ^ 2 * t) = (c : ℂ) * p t := by
  change (c : ℂ) * p ((c ^ 2 * t) / c ^ 2) = _
  rw [mul_div_cancel_left₀ t (pow_ne_zero 2 hc.ne')]

theorem goodRibbonPrefix_scalePath
    (c : ℝ≥0) (hc : 0 < c) (p : C(ℝ≥0, ℂ)) (P : ℂ → ℂ)
    (g g' : C(ℂ, ℝ)) (hgg' : ∀ z : ℂ, g' ((c : ℂ) * z) = g z)
    (k ε : ℝ)
    (hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => (p : ℝ≥0 → ℂ))
      (fun _ => firstFrontTime (fun t => g (p t)) k) P ε) :
    () ∈ GoodRibbonPrefix (fun _ : Unit => (scalePath c p : ℝ≥0 → ℂ))
      (fun _ => firstFrontTime (fun t => g' (scalePath c p t)) k)
      (fun z => (c : ℂ) * P z) ε := by
  cases hτ : firstFrontTime (fun t => g (p t)) k with
  | top => exact False.elim (hpref.1 hτ)
  | coe T =>
    let e := OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2)
    have heval (t : ℝ≥0) : scalePath c p (e t) = (c : ℂ) * p t :=
      scalePath_at_scaled_time c hc p t
    have hclock : (fun t => g' (scalePath c p (e t))) = (fun t => g (p t)) := by
      funext t
      rw [heval, hgg']
    have hhit := firstFrontTime_attained _ (g.continuous.comp p.continuous) k T hτ
    have hnew := firstFrontTime_of_clock_hit e (fun t => g' (scalePath c p t)) k T
      (by rw [hclock]; exact hτ) (by rw [heval, hgg']; exact hhit)
    have hprefix : MapsTo p (Icc 0 T) (ribbonCore P ε) := by
      simpa only [hτ, WithTop.untopD_coe] using hpref.2.1
    have hend : p T ∈ ribbonCore P (ε / 4) := by
      simpa only [hτ, WithTop.untopD_coe] using hpref.2.2
    change firstFrontTime (fun t => g' (scalePath c p t)) k ≠ ⊤ ∧ _
    rw [hnew]
    refine ⟨WithTop.coe_ne_top, ?_, ?_⟩
    · intro t ht
      have htt : t ≤ e T := by simpa only [WithTop.untopD_coe] using ht.2
      have hu : e.symm t ∈ Icc 0 T := ⟨bot_le, by
        simpa only [e.symm_apply_apply] using e.symm.monotone htt⟩
      obtain ⟨z, hz, hez⟩ := hprefix hu
      refine ⟨z, hz, ?_⟩
      change (c : ℂ) * P z = scalePath c p t
      rw [hez, ← heval, e.apply_symm_apply]
    · obtain ⟨z, hz, hez⟩ := hend
      refine ⟨z, hz, ?_⟩
      change (c : ℂ) * P z = scalePath c p (e T)
      rw [heval, hez]

end SLEExactGauge

end

end OAI
