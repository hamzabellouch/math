import OAI.Analysis.CircleDomains.Modulus.OneEndedFragmentBudget
import OAI.Analysis.CircleDomains.Selection.LastEntryFragmentProperties
import OAI.Analysis.CircleDomains.Uniformization.TwoEndedFragmentLimits

namespace OAI

/-! Actual retained prefixes and final fragments, with one common
subsequence and the correct one-ended limiting budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def prefixFragment (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0)) (n : ℕ) : TaggedPhysicalPath d :=
  restrictTaggedPhysicalPath d hU (Γ n) (hprefix n)

theorem actual_oneEnded_finite_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W) (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (F : Finset ℕ) {n : ℕ} (hn : ∀j ∈ F, j ≤ n) :
    physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1 +
      (∑j ∈ F, physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1) ≤
      physicalTollCost d g m (Γ n).1 := by
  classical
  have h := oneEnded_restricted_budget d hU (Γ n).1
    (fun j => lastEntryTime (Γ n).1.val (W j))
    (lastEntryTime_monotone (Γ n).1.val W hW hanti (hstart n)) (hprefix n) F
    (fun j hj => hcut n j (hn j hj)) g hg m (hzero n) (hm n 0 (Nat.zero_le _))
    (fun j hj => ⟨hm n j ((hn j hj).trans (Nat.le_succ _)),
      hm n (j+1) (Nat.add_le_add_right (hn j hj) 1)⟩)
  have hc (j : F) : physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1 =
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hcut n j (hn j j.property))) := by
    rw [lastEntryFragmentArray_eq d hU Γ W hcut (hn j j.property)]
    rfl
  rw [← Finset.sum_coe_sort F]
  simp_rw [hc]
  exact h

variable [CompactSpace X]

theorem exists_actual_oneEnded_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W) (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (A : ℝ≥0∞) (hA : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A)) :
    ∃ (s : ℕ → ℕ) (x : ℕ → X) (c : ℕ → ℝ≥0∞) (M : ℝ≥0∞), StrictMono s ∧
      (∀j, Tendsto (fun n => (Γ (s n)).1.val (lastEntryTime (Γ (s n)).1.val (W j))) atTop (𝓝 (x j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut (s n) j).1) atTop (𝓝 (c j))) ∧
      Tendsto (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix (s n)).1) atTop (𝓝 M) ∧
      M + (∑'j, c j) ≤ A := by
  obtain ⟨s, x, _, c, _, M, hs, hx, _, hc, _, hM⟩ := exists_twoEnded_fragment_limits
    (fun n j => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)))
    (fun n j => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)))
    (fun n j => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1)
    (fun _ _ => 0) (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1)
  refine ⟨s, x, c, M, hs, hx, hc, hM, ?_⟩
  have hb := twoEnded_limit_budget_of_eventually
    (fun n j => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut (s n) j).1)
    (fun _ _ => 0) (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix (s n)).1)
    (fun n => physicalTollCost d g m (Γ (s n)).1) c (fun _ => 0) M A
    hc (fun _ => tendsto_const_nhds) hM (hA.comp hs.tendsto_atTop) ?_
  · simpa only [tsum_zero, add_zero] using hb
  · intro F
    filter_upwards [hs.tendsto_atTop.eventually_ge_atTop (F.sup id)] with n hn
    simp only [add_zero]
    apply actual_oneEnded_finite_budget d hU Γ W hcut hprefix hW hanti hstart g hg m hzero hm F
    intro j hj
    exact (Finset.le_sup (f := id) hj).trans hn

end CircleDomainRigidity

end

end OAI
