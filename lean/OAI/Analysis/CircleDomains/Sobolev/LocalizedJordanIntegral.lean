import OAI.Analysis.CircleDomains.Modulus.RegularJordanNormalBox
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-! A form supported in one small normal chart contributes exactly the
integral over that parameter arc of the full periodic Jordan circuit. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma periodic_deriv_of_periodic {γ : ℝ → ℂ} {T : ℝ} (hγ : Periodic γ T) :
    Periodic (deriv γ) T := by
  intro t
  rw [← deriv_comp_add_const]
  have h : (fun s => γ (s+T)) = γ := funext hγ
  rw [h]

lemma planarFormIntegrand_continuous {γ : ℝ → ℂ} {P Q : ℂ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  have hd := (contDiff_infty_iff_deriv.mp hγ).2.continuous
  exact ((hP.comp hγ.continuous).mul (Complex.continuous_re.comp hd)).add
    ((hQ.comp hγ.continuous).mul (Complex.continuous_im.comp hd))

lemma planarFormIntegral_eq_shifted {γ : ℝ → ℂ} (hγ : Periodic γ 1)
    (P Q : ℂ → ℝ) (t : ℝ) :
    planarFormIntegral P Q γ =
      ∫ s in (t-1/2)..(t+1/2),
        P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  have hd := periodic_deriv_of_periodic hγ
  have hp : Periodic (fun s => P (γ s) * (deriv γ s).re +
      Q (γ s) * (deriv γ s).im) 1 := by
    intro s
    dsimp only
    rw [hγ s,hd s]
  have h := hp.intervalIntegral_add_eq 0 (t-1/2)
  simpa only [planarFormIntegral,zero_add,show t-1/2+1 = t+1/2 by ring] using h

lemma normal_box_parameter_mem {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    {s : ℝ} (hs : s ∈ Icc (t-1/2) (t+1/2))
    (hmem : γ s ∈ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r)) :
    s ∈ Ioo (t-r) (t+r) := by
  obtain ⟨p,hp,hep⟩ := hmem
  have hpK : p ∈ Icc (t-r,-r) (t+r,r) :=
    ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩
  have hp0 : p.2 = 0 := (hf p hpK).mp (hep.symm ▸ hγ.mem_frontier s)
  have hps : γ p.1 = γ s := by simpa only [he,curveNormalStrip,hp0,zero_smul,add_zero] using hep
  have hst : p.1 = s := hγ.eq_of_eq_short hps
    (by linarith [hp.1.1,hs.2]) (by linarith [hp.1.2,hs.1])
  exact hst ▸ hp.1

lemma planarFormIntegral_localized {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r) (hrsmall : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q)
    (hzero : ∀ z ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r), P z = 0 ∧ Q z = 0) :
    planarFormIntegral P Q γ =
      ∫ s in (t-r)..(t+r), P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  let f := fun s => P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im
  have hc : Continuous f := planarFormIntegrand_continuous hγ.smooth hP hQ
  have hz (s : ℝ) (hs : s ∈ Icc (t-1/2) (t+1/2))
      (hout : s ∉ Ioo (t-r) (t+r)) : f s = 0 := by
    have hn : γ s ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) :=
      fun h => hout (normal_box_parameter_mem hγ e t r hrsmall he hf hs h)
    simp only [f,(hzero _ hn).1,(hzero _ hn).2,zero_mul,zero_add]
  have hl : (∫ s in (t-1/2)..(t-r), f s) = 0 := by
    calc
      _ = ∫ _s in (t-1/2)..(t-r), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : t-1/2 ≤ t-r)] at hs
        exact hz s ⟨hs.1,by linarith [hs.2]⟩ (fun h => (not_lt_of_ge hs.2) h.1)
      _ = 0 := by simp
  have hu : (∫ s in (t+r)..(t+1/2), f s) = 0 := by
    calc
      _ = ∫ _s in (t+r)..(t+1/2), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : t+r ≤ t+1/2)] at hs
        exact hz s ⟨by linarith [hs.1],hs.2⟩ (fun h => (not_lt_of_ge hs.1) h.2)
      _ = 0 := by simp
  rw [planarFormIntegral_eq_shifted hγ.periodic P Q t]
  change (∫ s in (t-1/2)..(t+1/2), f s) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (t-1/2) (t-r)) (hc.intervalIntegrable (t-r) (t+1/2)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (t-r) (t+r)) (hc.intervalIntegrable (t+r) (t+1/2)),hl,hu]
  simp only [zero_add,add_zero]
  rfl

end CircleDomainRigidity

end

end OAI
