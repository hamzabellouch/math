import OAI.NumberTheory.Jacobsthal.Probability.CompletedMarkEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CanonicalBadCompact

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathMeasures FinitePathGeometry FiniteHistoryTransport CemeteryKernel CemeteryHistoryMap
open LiveKilledPrefixes CompletedMarkEvents CanonicalMarkSlack CanonicalCoupledHistories
open RegeneratingInverseBands ArrivalKernelGeometry ContinuousKilledBins
open Erdos970Dependency.MarkedVisits

theorem canonical_bad_compact_subset {r R b₀ b₁ : ℝ}
    (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : R < 6*b₀)
    (E : Set CostState) (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,
      killHist E N h ∈ badCompactPath (Real.log r) R b₀ b₁ N →
        h ∈ closedNoHitEvent 1 N r b₀ b₁ 1 := by
  have hCosts : ∀ᵐ h ∂finitePathMeasure s N, h ∈ increasingCosts 0 N :=
    rawExtension_increasingCosts 0 N (fun _ => (s,0))
  filter_upwards [canonical_all_marks_slack hr hb₀ hb₁ s N,hCosts] with h hMarks hCost
  rintro ⟨j,hcompact,hNo⟩
  cases hz : killHist E N h j with
  | inr u => rw [hz] at hcompact; exact False.elim hcompact
  | inl z =>
    rw [hz] at hcompact
    have horig := (live_coordinate_original E N j.1 (Finset.mem_Iic.mp j.2) h z hz).1
    have hgapj : gapValue (Real.log r) (h j) ≤ R := by rw [horig]; exact hcompact
    have hNoHit : h ∉ anyPairHit 1 N (Real.log (r/b₁)) (Real.log (b₁/(10*b₀))) := by
      rintro ⟨k,hk,hHit⟩
      have hslack := hMarks 1 k hk hHit
      let m : Finset.Iic N := ⟨1+2*k+1,Finset.mem_Iic.mpr hk⟩
      by_cases hmj : m.1 ≤ j.1
      · have hp := live_prefix_preserved E N j.1 (Finset.mem_Iic.mp j.2) h z hz m.1 hmj
        have hn := hNo m hmj
        rw [hp] at hn
        exact hn ⟨hslack.1,hslack.2.1,hslack.2.2.1,hslack.2.2.2.1,hslack.2.2.2.2.1⟩
      · have hcm := hCost j m (Nat.zero_le _) (by omega)
        have hgm : gapValue (Real.log r) (h m) ≤ gapValue (Real.log r) (h j) :=
          Real.exp_le_exp.mpr (sub_le_sub_left hcm _)
        have hsGap : 6*b₀ < gapValue (Real.log r) (h m) := hslack.2.2.2.2.2
        linarith
    refine ⟨hNoHit,Or.inl ?_⟩
    have hcN := hCost j ⟨N,by simp⟩ (Nat.zero_le _) (Finset.mem_Iic.mp j.2)
    have hgN : gapValue (Real.log r) (rawLast N h) ≤ gapValue (Real.log r) (h j) :=
      Real.exp_le_exp.mpr (sub_le_sub_left hcN _)
    rw [gapValue_log_eq_gapAt hr] at hgN
    linarith

theorem canonical_bad_compact_mass {r R b₀ b₁ : ℝ}
    (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : R < 6*b₀)
    {E : Set CostState} (hE : MeasurableSet E) (s : State) (N : ℕ) :
    ((finitePathMeasure s N).map (killHist E N)) (badCompactPath (Real.log r) R b₀ b₁ N) ≤
      finitePathMeasure s N (closedNoHitEvent 1 N r b₀ b₁ 1) := by
  rw [Measure.map_apply (killHist_measurable hE N) (badCompactPath_measurable _ _ _ _ _)]
  exact measure_mono_ae (canonical_bad_compact_subset hr hb₀ hb₁ hR E s N)

theorem completed_bad_compact_mass {r R b₀ b₁ : ℝ}
    (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : R < 6*b₀)
    (ell S : ℝ) (s : State) (N : ℕ) :
    pathKernel (continuousChain (Real.log r) ell S) N (fun _ => Sum.inl (s,0))
      (badCompactPath (Real.log r) R b₀ b₁ N) ≤
        finitePathMeasure s N (closedNoHitEvent 1 N r b₀ b₁ 1) := by
  rw [← canonical_killing_image s N (Real.log r) ell S]
  exact canonical_bad_compact_mass hr hb₀ hb₁ hR (LowStateHorizon.lowDomain_measurable _ _ _) s N

end NumberTheoryLean.CanonicalBadCompact

end

end Erdos970

end OAI
