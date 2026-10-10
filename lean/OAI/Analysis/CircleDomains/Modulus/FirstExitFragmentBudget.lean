import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentArray
import OAI.Analysis.CircleDomains.Modulus.EventualFragmentBudget

namespace OAI

/-! Every finite collection of actual first-exit fragments eventually has
cost at most the original path. Their limiting series has the same bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem firstExitFragmentArray_finite_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (F : Finset ℕ) {n : ℕ} (hn : ∀j ∈ F, j ≤ n) :
    (∑j ∈ F, physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1) ≤
      physicalTollCost d g m (Γ n).1 := by
  classical
  rw [← Finset.tsum_subtype]
  have he (j : F) : physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1 =
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hcut n j (hn j j.property))) := by
    rw [firstExitFragmentArray_eq d hU Γ V hcut (hn j j.property)]
    rfl
  simp_rw [he]
  apply sum_restricted_physicalTollCost_le d hU (Γ n).1
    (fun j : F => firstExitTime (Γ n).1.val (V (j+1)))
    (fun j : F => firstExitTime (Γ n).1.val (V j))
    (fun j => hcut n j (hn j j.property))
  · intro i j hij
    exact firstExitFragments_disjoint (Γ n).1.val V hV hanti (hend n)
      (fun h => hij (Subtype.ext h))
  · exact hg
  · intro j
    exact hm n (j+1) (Nat.add_le_add_right (hn j j.property) 1)
  · intro j
    exact hm n j ((hn j j.property).trans (Nat.le_succ n))

theorem firstExitFragmentArray_limiting_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (c : ℕ → ℝ≥0∞) (A : ℝ≥0∞)
    (hc : ∀j, Tendsto (fun n =>
      physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1) atTop (𝓝 (c j)))
    (hA : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A)) :
    (∑'j, c j) ≤ A := by
  apply fragment_limit_budget_of_eventually
    (fun n j => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1)
    c (fun n => physicalTollCost d g m (Γ n).1) A hc hA
  intro F
  filter_upwards [eventually_ge_atTop (F.sup id)] with n hn
  apply firstExitFragmentArray_finite_budget d hU Γ V hcut hV hanti hend g hg m hm F
  intro j hj
  exact (Finset.le_sup (f := id) hj).trans hn

end CircleDomainRigidity

end

end OAI
