import OAI.Analysis.CircleDomains.Selection.LastEntryFragmentArray
import OAI.Analysis.CircleDomains.Modulus.TwoEndedFragmentBudget
import OAI.Analysis.CircleDomains.Uniformization.TwoEndedFragmentLimits

namespace OAI

/-! The common limiting budget for actual first-exit, middle, and last-entry
restrictions of the original paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def middleFragment (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V W : ℕ → Set X)
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (n : ℕ) : TaggedPhysicalPath d := restrictTaggedPhysicalPath d hU (Γ n) (hmid n)

theorem actual_twoEnded_finite_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V W : ℕ → Set X)
    (hleft : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j))
    (hright : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hantiV : Antitone V) (hantiW : Antitone W)
    (hendV : ∀n, (Γ n).1.val ⊤ ∉ V 0) (hstartW : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (hmW : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (F : Finset ℕ) {n : ℕ} (hn : ∀j ∈ F, j ≤ n) :
    physicalTollCost d g m (middleFragment d hU Γ V W hmid n).1 +
      (∑j ∈ F, (physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft n j).1 +
        physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright n j).1)) ≤
      physicalTollCost d g m (Γ n).1 := by
  classical
  have h := twoEnded_restricted_budget d hU (Γ n).1
    (fun j => firstExitTime (Γ n).1.val (V j)) (fun j => lastEntryTime (Γ n).1.val (W j))
    (firstExitTime_antitone (Γ n).1.val V hV hantiV (hendV n))
    (lastEntryTime_monotone (Γ n).1.val W hW hantiW (hstartW n)) (hmid n) F
    (fun j hj => hleft n j (hn j hj)) (fun j hj => hright n j (hn j hj)) g hg m
    ⟨hmV n 0 (Nat.zero_le _), hmW n 0 (Nat.zero_le _)⟩
    (fun j hj => ⟨hmV n j ((hn j hj).trans (Nat.le_succ _)),
      hmV n (j+1) (Nat.add_le_add_right (hn j hj) 1)⟩)
    (fun j hj => ⟨hmW n j ((hn j hj).trans (Nat.le_succ _)),
      hmW n (j+1) (Nat.add_le_add_right (hn j hj) 1)⟩)
  have hcost (j : F) :
      physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft n j).1 +
        physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright n j).1 =
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hleft n j (hn j j.property))) +
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hright n j (hn j j.property))) := by
    rw [firstExitFragmentArray_eq d hU Γ V hleft (hn j j.property),
      lastEntryFragmentArray_eq d hU Γ W hright (hn j j.property)]
    rfl
  rw [← Finset.sum_coe_sort F]
  simp_rw [hcost]
  exact h

variable [CompactSpace X]

theorem exists_actual_twoEnded_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V W : ℕ → Set X)
    (hleft : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j))
    (hright : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hantiV : Antitone V) (hantiW : Antitone W)
    (hendV : ∀n, (Γ n).1.val ⊤ ∉ V 0) (hstartW : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (hmW : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (A : ℝ≥0∞) (hA : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A)) :
    ∃ (s : ℕ → ℕ) (x y : ℕ → X) (c e : ℕ → ℝ≥0∞) (M : ℝ≥0∞), StrictMono s ∧
      (∀j, Tendsto (fun n => (Γ (s n)).1.val (firstExitTime (Γ (s n)).1.val (V j))) atTop (𝓝 (x j))) ∧
      (∀j, Tendsto (fun n => (Γ (s n)).1.val (lastEntryTime (Γ (s n)).1.val (W j))) atTop (𝓝 (y j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft (s n) j).1) atTop (𝓝 (c j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright (s n) j).1) atTop (𝓝 (e j))) ∧
      Tendsto (fun n => physicalTollCost d g m (middleFragment d hU Γ V W hmid (s n)).1) atTop (𝓝 M) ∧
      M + (∑'j, c j) + (∑'j, e j) ≤ A := by
  obtain ⟨s, x, y, c, e, M, hs, hx, hy, hc, he, hM⟩ := exists_twoEnded_fragment_limits
    (fun n j => (Γ n).1.val (firstExitTime (Γ n).1.val (V j)))
    (fun n j => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)))
    (fun n j => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft n j).1)
    (fun n j => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright n j).1)
    (fun n => physicalTollCost d g m (middleFragment d hU Γ V W hmid n).1)
  refine ⟨s, x, y, c, e, M, hs, hx, hy, hc, he, hM, ?_⟩
  apply twoEnded_limit_budget_of_eventually _ _ _ _ c e M A hc he hM (hA.comp hs.tendsto_atTop)
  intro F
  filter_upwards [hs.tendsto_atTop.eventually_ge_atTop (F.sup id)] with n hn
  apply actual_twoEnded_finite_budget d hU Γ V W hleft hright hmid hV hW hantiV hantiW
    hendV hstartW g hg m hmV hmW F
  intro j hj
  exact (Finset.le_sup (f := id) hj).trans hn

end CircleDomainRigidity

end

end OAI
