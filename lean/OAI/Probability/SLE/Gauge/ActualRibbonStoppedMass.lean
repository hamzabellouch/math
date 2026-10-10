import OAI.Probability.SLE.Gauge.ActualRibbonMass

namespace OAI

/-! The retained mass is present at successful completion and is observable
at that stopping time. It supplies the adapted cover tests and the
successful-completion change of measure. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FrontSuccessMeasurability

lemma untopD_le_of_le_finite {a b : WithTop ℝ≥0} (hab : a ≤ b) (hb : b ≠ ⊤) :
    a.untopD 0 ≤ b.untopD 0 := by
  cases a with
  | top => exact False.elim (hb (top_le_iff.mp hab))
  | coe s =>
    cases b with
    | top => exact False.elim (hb rfl)
    | coe t => simpa only [WithTop.untopD_coe, WithTop.coe_le_coe] using hab

/-- All selected mass is measurable by the successful completion time;
no later portion of the trace is used to create a dense candidate. -/
theorem actual_successes_force_stopped_mass
    {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (hc : ∀ ω, Continuous (γ ω))
    (g : C(ℂ, ℝ)) (hg0 : ∀ ω, g (γ ω 0) = 0) (P : ℂ → ℂ)
    (hplanar : PublishedPlanarDiskOpenness) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) (ε κ v c : ℝ) (hε : ε ≤ 1)
    (N : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, 0 < i ∧ i ≤ N) (D : Set ℂ)
    (hregions : ∀ i ∈ I, physicalMiddleRegion P closedRibbon i ε ⊆ D)
    (ω : Ω) (hω : ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε ∩
      ⋂ n ∈ Finset.range N, actualRibbonSuccess γ g P ε κ v c n) :
    ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ N) P ε ∧
      (I.card : ℝ≥0∞) * ENNReal.ofReal c ≤ segmentSausageCharge κ (γ ω) 0
        ((ribbonIntegerFront g γ N ω).untopD 0) v D := by
  have hpref := actual_successes_terminal_prefix γ g P ε κ v c N ω hω
  have hmono := ribbonIntegerFront_monotone g γ hc hg0
  let T := (ribbonIntegerFront g γ N ω).untopD 0
  let f := sourceTracePath γ hc ω
  let p := clampedPath f 0 T
  have htbound (i : ℕ) (hiN : i ≤ N) : (ribbonIntegerFront g γ i ω).untopD 0 ≤ T :=
    untopD_le_of_le_finite (hmono hiN ω) hpref.1
  have hmass := whole_sausage_charge_from_ribbon_steps hplanar P hP hi hε I κ p
    (fun i => (ribbonIntegerFront g γ (i - 1) ω).untopD 0)
    (fun i => (ribbonIntegerFront g γ i ω).untopD 0) v c D hregions
  have hselected (i : ℕ) (hiI : i ∈ I) : ENNReal.ofReal c ≤
      segmentSausageCharge κ p ((ribbonIntegerFront g γ (i - 1) ω).untopD 0)
        ((ribbonIntegerFront g γ i ω).untopD 0) v (physicalMiddleRegion P closedRibbon i ε) := by
    obtain ⟨hi0, hiN⟩ := hI i hiI
    have hsub : i - 1 + 1 = i := Nat.sub_add_cancel hi0
    have hreal : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast hsub
    have hn : i - 1 < N := by omega
    have hs := (mem_iInter.mp (mem_iInter.mp hω.2 (i - 1)) (Finset.mem_range.mpr hn)).2
    have hcharge : ENNReal.ofReal c ≤ segmentSausageCharge κ (γ ω)
        ((ribbonIntegerFront g γ (i - 1) ω).untopD 0) ((ribbonIntegerFront g γ i ω).untopD 0) v
        (physicalMiddleRegion P closedRibbon i ε) := by
      simpa only [mem_ofPred_eq, hsub, hreal] using hs
    have he : EqOn p (γ ω) (Icc ((ribbonIntegerFront g γ (i - 1) ω).untopD 0)
        ((ribbonIntegerFront g γ i ω).untopD 0)) := by
      intro u hu
      have huT := hu.2.trans (htbound i hiN)
      simp only [p, clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        min_eq_left huT, zero_le, max_eq_right, f, sourceTracePath]
    simpa only [segmentSausageCharge, sourceSausageSet_congr_interval he v] using hcharge
  have hh := hmass hselected
  have he := sourceSausageSet_eq_clamped f 0 T (bot_le : (0 : ℝ≥0) ≤ T) v
  refine ⟨hpref, ?_⟩
  change (I.card : ℝ≥0∞) * ENNReal.ofReal c ≤ wholeSausageCharge κ (clampedPath f 0 T) v D at hh
  unfold wholeSausageCharge at hh
  rw [← he] at hh
  simpa only [segmentSausageCharge, f, sourceTracePath, ContinuousMap.coe_mk] using hh

end SLEExactGauge

end

end OAI
