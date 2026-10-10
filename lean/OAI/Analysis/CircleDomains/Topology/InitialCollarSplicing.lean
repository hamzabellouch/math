import OAI.Analysis.CircleDomains.Uniformization.FirstExitFragmentLimits
import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentProperties
import OAI.Analysis.CircleDomains.Topology.CollarSplicingFromFragments

namespace OAI

/-! The actual initial collar path, assembled from first-exit restrictions
of the original sequence. Only local joining arcs on the selected collars
remain as geometric data. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_initial_collar_path
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p : X) (V : ℕ → Set X) (hV : ∀j, IsOpen (V j))
    (hnest : ∀j, closure (V (j+1)) ⊆ V j)
    (hshrink : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j x, x ∈ frontier (V j) → m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcostlim : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
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
      α.val ⊤ = (Γ k).1.val (firstExitTime (Γ k).1.val (V 0)) ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint α) +
        timeToll α.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + ENNReal.ofReal η := by
  have hanti : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j) := fun n j hj =>
    firstExitFragments_strict (Γ n).1.val V hV hnest (hstart n) (hend n) hj
  have hcutm := firstExit_toll_zero d Γ V hV hanti hstart hend m hm
  obtain ⟨s, x, c, hs, hx, hstartlim, hstoplim, hc, hcsum⟩ :=
    exists_firstExit_fragment_limits d hU Γ V hcut hV hanti hstart hend g hg m hcutm A hcostlim
  let γ : ℕ → ℕ → TaggedPhysicalPath d := fun n j => firstExitFragmentArray d hU Γ V hcut (s n) j
  have hindex {n j : ℕ} (hj : j ≤ n) : j ≤ s n := hj.trans (hs.id_le n)
  have hfront {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊥ ∈ frontier (V (j+1)) ∧
      (γ n j).1.val ⊤ ∈ frontier (V j) :=
    firstExitFragmentArray_frontiers d hU Γ V hcut hV hanti hstart hend (hindex hj)
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
    exact firstExitFragmentArray_support d hU Γ V hcut hV hanti hstart hend
      (hindex hn) (mem_range_self t)
  obtain ⟨k, α, θ, hα, hα0, hα1, hbound⟩ := exists_collar_path_from_fragment_limits
    d hU hG ν N p g hg m γ x (fun j => frontier (V j)) (fun j => closure (V j))
    (fun n j hj => firstExitFragmentArray_allowed d hU Γ V hcut ν N hΓ hpoint (hindex hj))
    (fun _ _ hj => (hfront hj).1) (fun _ _ hj => (hfront hj).2)
    hstartlim hstoplim c ε ε A e e hA hefinite hefinite hc hcsum hεpos hεsum hεsum
    (fun j => hsmall j (x (j+1)) (hx (j+1)) (ε j) (hεpos j))
    (fun _ j hj => ⟨hm (j+1) _ (hfront hj).1, hm j _ (hfront hj).2⟩)
    htail hshrink w hw hpos hpoint
  refine ⟨s k, α, θ, hα, hα0, ?_, ?_⟩
  · exact hα1.trans (firstExitFragmentArray_endpoints d hU Γ V hcut (Nat.zero_le (s k))).2
  · have he : e + e = ENNReal.ofReal η := by
      dsimp [e]
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η/2) (by linarith : 0 ≤ η/2)]
      congr 1
      ring
    simpa only [add_assoc, he] using hbound

end CircleDomainRigidity

end

end OAI
