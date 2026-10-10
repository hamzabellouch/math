import OAI.Analysis.LipschitzHilbert.Estimates.RelativeMartingaleExits

namespace OAI

/-! Every sufficiently large interval crosses a relative exit whose jump
controls that interval. This is the finite, initial-value-radius version
of Zorin-Kranich, Bernoulli 26 (2020), Lemma 2.2. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relativeExitTimes_last (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H b : ℕ) (hb : b<H) (x : Ω) :
    ∃ i<H, relativeExitTimes F a H i x≤b ∧ b<relativeExitTimes F a H (i+1) x := by
  have hex : ∃ i, b<relativeExitTimes F a H i x :=
    ⟨H,by simpa only [relativeExitTimes_terminal F a ha H x] using hb⟩
  have hq := Nat.find_spec hex
  have hqpos : 0<Nat.find hex := by
    apply (Nat.find_pos hex).2
    simp [relativeExitTimes]
  have hqH : Nat.find hex≤H := Nat.find_min' hex (by
    simpa only [relativeExitTimes_terminal F a ha H x] using hb)
  refine ⟨Nat.find hex-1, by omega, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa only [Nat.sub_add_cancel hqpos] using hq

theorem runningOscillation_at_last_exit (F : ℕ → Ω → ℝ) (a : ℝ)
    (ha : 0≤a) (ha2 : a≤1/2) (H b i : ℕ) (x : Ω)
    (_hleft : relativeExitTimes F a H i x≤b)
    (hright : b<relativeExitTimes F a H (i+1) x) :
    runningOscillation F b x≤2*runningOscillation F (relativeExitTimes F a H i x) x := by
  have hmax : runningOscillation F b x≤
      runningOscillation F (relativeExitTimes F a H i x) x+a*runningOscillation F b x := by
    apply runningOscillation_le
    intro k hk
    by_cases hki : k≤relativeExitTimes F a H i x
    · exact (le_runningOscillation F hki x).trans
        (le_add_of_nonneg_right (mul_nonneg ha (runningOscillation_nonneg F b x)))
    · have hik : relativeExitTimes F a H i x≤k := (lt_of_not_ge hki).le
      have hsmall := relativeNextExit_before F a H (relativeExitTimes F a H i) x k hik
        (hk.trans_lt hright)
      have hmono := mul_le_mul_of_nonneg_left (runningOscillation_mono F hk x) ha
      calc
        ‖F k x-F 0 x‖ ≤ ‖F k x-F (relativeExitTimes F a H i x) x‖+
            ‖F (relativeExitTimes F a H i x) x-F 0 x‖ := by simpa only [dist_eq_norm] using dist_triangle (F k x) (F (relativeExitTimes F a H i x) x) (F 0 x)
        _ ≤ a*runningOscillation F b x+runningOscillation F (relativeExitTimes F a H i x) x :=
          add_le_add (hsmall.trans hmono) (le_runningOscillation F le_rfl x)
        _ = _ := add_comm _ _
  have hprod := mul_le_mul_of_nonneg_right ha2 (runningOscillation_nonneg F b x)
  linarith

theorem relative_interval_crosses_exit (F : ℕ → Ω → ℝ) (a : ℝ)
    (ha : 0≤a) (ha2 : a≤1/2) (H l b : ℕ) (hb : b<H) (hlb : l≤b) (x : Ω)
    (hlarge : 2*a*runningOscillation F b x<‖F b x-F l x‖)
    (hupper : ‖F b x-F l x‖≤8*a*runningOscillation F b x) :
    ∃ j<H, l<relativeExitTimes F a H (j+1) x ∧
      relativeExitTimes F a H (j+1) x≤b ∧
      ‖F b x-F l x‖≤16*‖F (relativeExitTimes F a H (j+1) x) x-
        F (relativeExitTimes F a H j x) x‖ := by
  obtain ⟨i,hiH,his,hit⟩ := relativeExitTimes_last F a ha H b hb x
  have hli : l<relativeExitTimes F a H i x := by
    by_contra hn
    have hil : relativeExitTimes F a H i x≤l := le_of_not_gt hn
    have hs1 := relativeNextExit_before F a H (relativeExitTimes F a H i) x l hil
      (hlb.trans_lt hit)
    have hs2 := relativeNextExit_before F a H (relativeExitTimes F a H i) x b his hit
    have hrad := mul_le_mul_of_nonneg_left (runningOscillation_mono F hlb x) ha
    have htri : ‖F b x-F l x‖≤‖F b x-F (relativeExitTimes F a H i x) x‖+
        ‖F l x-F (relativeExitTimes F a H i x) x‖ := by
      simpa only [norm_sub_rev (F (relativeExitTimes F a H i x) x) (F l x)] using
        (show ‖F b x-F l x‖≤‖F b x-F (relativeExitTimes F a H i x) x‖+
          ‖F (relativeExitTimes F a H i x) x-F l x‖ by
          simpa only [dist_eq_norm] using dist_triangle (F b x) (F (relativeExitTimes F a H i x) x) (F l x))
    nlinarith
  have hipos : 0 < i := by
    by_contra hn
    have : i=0 := by omega
    simp [this,relativeExitTimes] at hli
  let j := i-1
  have hji : j+1=i := by dsimp [j]; omega
  have hjH : j<H := by dsimp [j]; omega
  have hjump := relativeNextExit_jump F a ha H (relativeExitTimes F a H j)
    (relativeExitTimes_le F a H j) x (by
      change relativeExitTimes F a H (j+1) x<H
      rw [hji]
      exact his.trans_lt hb)
  change a*runningOscillation F (relativeExitTimes F a H (j+1) x) x<
    ‖F (relativeExitTimes F a H (j+1) x) x-F (relativeExitTimes F a H j x) x‖ at hjump
  have hrad := runningOscillation_at_last_exit F a ha ha2 H b i x his hit
  rw [←hji] at hrad
  refine ⟨j,hjH,by simpa only [hji] using hli,by simpa only [hji] using his,?_⟩
  have hm := mul_le_mul_of_nonneg_left hrad ha
  nlinarith

end LipschitzHilbert

end

end OAI
