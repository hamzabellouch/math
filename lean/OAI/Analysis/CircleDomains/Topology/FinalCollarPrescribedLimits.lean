import OAI.Analysis.CircleDomains.Uniformization.FirstExitFragmentLimits
import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentProperties
import OAI.Analysis.CircleDomains.Topology.LocalizedCollarSplicing

import OAI.Analysis.CircleDomains.Selection.LastEntryFragmentProperties
import OAI.Analysis.CircleDomains.Probability.ReversedPhysicalOccupation

namespace OAI

/-! The final collar, oriented from the limiting endpoint inward, uses the
prescribed common limits of actual last-entry fragments. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_final_collar_path_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p : X) (V : ℕ → Set X) (hV : ∀j, IsOpen (V j))
    (hnest : ∀j, closure (V (j+1)) ⊆ V j)
    (hshrink : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ V 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ V (n+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j x, x ∈ frontier (V j) → m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (x : ℕ → X) (c : ℕ → ℝ≥0∞)
    (hhitlim : ∀j, Tendsto (fun n => (Γ n).1.val (lastEntryTime (Γ n).1.val (V j)))
      atTop (𝓝 (x j)))
    (hclim : ∀hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (V j) <
        lastEntryTime (Γ n).1.val (V (j+1)),
      ∀j, Tendsto (fun n => physicalTollCost d g m
        (lastEntryFragmentArray d hU Γ V hcut n j).1) atTop (𝓝 (c j)))
    (hcsum : (∑'j, c j) ≤ A) (O : Set X) (hO : O ∈ 𝓝 (x 0))
    (hsmall : ∀j z, z ∈ frontier (V (j+1)) → ∀ε : ℝ≥0∞, 0 < ε →
      ∃ W : Set X, W ∈ 𝓝 z ∧
        ∀a ∈ W ∩ frontier (V (j+1)), ∀b ∈ W ∩ frontier (V (j+1)),
          ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
            ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ closure (V j) ∧
            physicalTollCost d g m ρ.1 ≤ ε)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (k : ℕ) (α : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (α.val, θ) ∧ α.val ⊥ = p ∧
      α.val ⊤ = (Γ k).1.val (lastEntryTime (Γ k).1.val (V 0)) ∧ α.val ⊤ ∈ O ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint α) +
        timeToll α.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + ENNReal.ofReal η := by
  have hanti : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (V j) <
      lastEntryTime (Γ n).1.val (V (j+1)) := fun n j hj =>
    lastEntryFragments_strict (Γ n).1.val V hV hnest (hstart n) (hend n) hj
  let γ : ℕ → ℕ → TaggedPhysicalPath d := fun n j =>
    reversedTaggedPhysicalPath d (lastEntryFragmentArray d hU Γ V hcut n j)
  have hzero {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊥ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (V (j+1))) := by
    change reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊥ = _
    rw [reversedPath_zero]
    exact (lastEntryFragmentArray_endpoints d hU Γ V hcut hj).2
  have hone {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊤ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (V j)) := by
    change reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊤ = _
    rw [reversedPath_one]
    exact (lastEntryFragmentArray_endpoints d hU Γ V hcut hj).1
  have hfront {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊥ ∈ frontier (V (j+1)) ∧
      (γ n j).1.val ⊤ ∈ frontier (V j) := by
    change reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊥ ∈ _ ∧
      reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊤ ∈ _
    rw [reversedPath_zero, reversedPath_one]
    exact (lastEntryFragmentArray_frontiers d hU Γ V hcut hV hanti hstart hend hj).symm
  have hx (j : ℕ) : x j ∈ frontier (V j) := by
    apply isClosed_frontier.mem_of_tendsto (hhitlim j)
    filter_upwards [eventually_ge_atTop j] with n hn
    exact lastEntry_frontier (Γ n).1.val (hV j)
      (fun h => hstart n (hanti (Nat.zero_le j) h))
      (hanti (hn.trans (Nat.le_succ _)) (hend n))
  have hstartlim (j : ℕ) : Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))) := by
    apply (hhitlim (j+1)).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    exact (hzero hn).symm
  have hstoplim (j : ℕ) : Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)) := by
    apply (hhitlim j).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    exact (hone hn).symm
  have hcostlim (j : ℕ) : Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)) := by
    convert hclim hcut j using 1
    ext n
    exact physicalTollCost_reversed d g m (lastEntryFragmentArray d hU Γ V hcut n j).1
  have hallowed (n j : ℕ) (hj : j ≤ n) : AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2) := by
    change AllowedTaggedPath d ν N (reversedTaggedPath
      ((lastEntryFragmentArray d hU Γ V hcut n j).1.val,
        (lastEntryFragmentArray d hU Γ V hcut n j).2))
    exact allowedTaggedPath_reversed d ν N
      ((lastEntryFragmentArray d hU Γ V hcut n j).1.val,
        (lastEntryFragmentArray d hU Γ V hcut n j).2)
      (lastEntryFragmentArray_allowed d hU Γ V hcut ν N hΓ hpoint hj) hpoint
  obtain ⟨weights, hweights, hsum⟩ := exists_positive_summable_weights ℕ
  let e : ℝ≥0∞ := ENNReal.ofReal (η/2)
  let ε : ℕ → ℝ≥0∞ := fun j => e * weights j
  have hepos : 0 < e := ENNReal.ofReal_pos.mpr (by linarith)
  have hefinite : e < ∞ := ENNReal.ofReal_lt_top
  have hεpos (j : ℕ) : 0 < ε j := ENNReal.mul_pos hepos.ne' (hweights j).ne'
  have hεsum : (∑'j, ε j) ≤ e := by
    change (∑'j, e * weights j) ≤ e
    rw [ENNReal.tsum_mul_left]
    simpa only [mul_one] using mul_le_mul' (le_refl e) hsum
  have htail : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀n ≥ j, ∀t, (γ n j).1.val t ∈ W := by
    intro W hW
    obtain ⟨k, hk⟩ := hshrink W hW
    refine ⟨k, fun j hj n hn t => hk j hj ?_⟩
    exact lastEntryFragmentArray_support d hU Γ V hcut hV hanti hstart hend
      hn (mem_range_self (unitInterval.symm t))
  obtain ⟨k, α, θ, hα, hα0, hα1, hαO, hbound⟩ := exists_collar_path_from_fragment_limits_near
    d hU hG ν N p g hg m γ x (fun j => frontier (V j)) (fun j => closure (V j))
    hallowed
    (fun _ _ hj => (hfront hj).1) (fun _ _ hj => (hfront hj).2)
    hstartlim hstoplim c ε ε A e e hA hefinite hefinite hcostlim hcsum hεpos hεsum hεsum
    (fun j => hsmall j (x (j+1)) (hx (j+1)) (ε j) (hεpos j))
    (fun _ j hj => ⟨hm (j+1) _ (hfront hj).1, hm j _ (hfront hj).2⟩)
    htail hshrink O hO w hw hpos hpoint
  refine ⟨k, α, θ, hα, hα0, ?_, hαO, ?_⟩
  · exact hα1.trans (hone (Nat.zero_le k))
  · have he : e + e = ENNReal.ofReal η := by
      dsimp [e]
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η/2) (by linarith : 0 ≤ η/2)]
      congr 1
      ring
    simpa only [add_assoc, he] using hbound

end CircleDomainRigidity

end

end OAI
