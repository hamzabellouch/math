import OAI.Analysis.CircleDomains.Modulus.FirstExitFragmentBudget

namespace OAI

/-! Joint compact hit-position limits and their genuine limiting cost
budget for the actual first-exit fragment array. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_firstExit_fragment_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (A : ℝ≥0∞) (hA : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A)) :
    ∃ (s : ℕ → ℕ) (x : ℕ → X) (c : ℕ → ℝ≥0∞), StrictMono s ∧
      (∀j, x j ∈ frontier (V j)) ∧
      (∀j, Tendsto (fun n => (firstExitFragmentArray d hU Γ V hcut (s n) j).1.val ⊥)
        atTop (𝓝 (x (j+1)))) ∧
      (∀j, Tendsto (fun n => (firstExitFragmentArray d hU Γ V hcut (s n) j).1.val ⊤)
        atTop (𝓝 (x j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m
        (firstExitFragmentArray d hU Γ V hcut (s n) j).1) atTop (𝓝 (c j))) ∧
      (∑'j, c j) ≤ A := by
  let hit : ℕ → ℕ → X := fun n j => (Γ n).1.val (firstExitTime (Γ n).1.val (V j))
  let cost : ℕ → ℕ → ℝ≥0∞ := fun n j =>
    physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1
  obtain ⟨s, _, x, c, hs, _, hx, hc⟩ := exists_joint_fragment_limits hit hit cost
  have hindex (j : ℕ) : ∀ᶠn in atTop, j ≤ s n :=
    hs.tendsto_atTop.eventually_ge_atTop j
  have hxfront (j : ℕ) : x j ∈ frontier (V j) := by
    apply isClosed_frontier.mem_of_tendsto (hx j)
    filter_upwards [hindex j] with n hn
    exact firstExit_frontier (Γ (s n)).1.val (hV j)
      (hanti (hn.trans (Nat.le_succ _)) (hstart (s n)))
      (fun h => hend (s n) (hanti (Nat.zero_le j) h))
  have hstartlim (j : ℕ) : Tendsto
      (fun n => (firstExitFragmentArray d hU Γ V hcut (s n) j).1.val ⊥)
      atTop (𝓝 (x (j+1))) := by
    apply (hx (j+1)).congr'
    filter_upwards [hindex j] with n hn
    exact (firstExitFragmentArray_endpoints d hU Γ V hcut hn).1.symm
  have hstoplim (j : ℕ) : Tendsto
      (fun n => (firstExitFragmentArray d hU Γ V hcut (s n) j).1.val ⊤)
      atTop (𝓝 (x j)) := by
    apply (hx j).congr'
    filter_upwards [hindex j] with n hn
    exact (firstExitFragmentArray_endpoints d hU Γ V hcut hn).2.symm
  refine ⟨s, x, c, hs, hxfront, hstartlim, hstoplim, hc, ?_⟩
  apply fragment_limit_budget_of_eventually (fun n j => cost (s n) j) c
    (fun n => physicalTollCost d g m (Γ (s n)).1) A hc (hA.comp hs.tendsto_atTop)
  intro F
  filter_upwards [hindex (F.sup id)] with n hn
  apply firstExitFragmentArray_finite_budget d hU Γ V hcut hV hanti hend g hg m hm F
  intro j hj
  exact (Finset.le_sup (f := id) hj).trans hn

end CircleDomainRigidity

end

end OAI
