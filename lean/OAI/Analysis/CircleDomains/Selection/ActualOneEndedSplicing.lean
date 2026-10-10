import OAI.Analysis.CircleDomains.Topology.OneEndedCollarSplicing
import OAI.Analysis.CircleDomains.Selection.FragmentReindexing

namespace OAI

/-! The one-ended construction retains an original prefix. Its common
prefix and tail budget and compact limits are derived from the input paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_actual_oneEnded_collar_splicing
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set X) (hF : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : X) (W : ℕ → Set X) (hW : ∀j, IsOpen (W j))
    (hnest : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ closure (W 0)) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j z, z ∈ frontier (W j) → m z = 0) (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (hsmall : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houter : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have ha : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hstart' (n : ℕ) : (Γ n).1.val ⊥ ∉ W 0 := fun h => hstart n (subset_closure h)
  have hfront (n : ℕ) := lastEntry_frontier (Γ n).1.val (hW 0) (hstart' n)
    (ha (Nat.zero_le _) (hend n))
  have hprefix (n : ℕ) : ⊥ < lastEntryTime (Γ n).1.val (W 0) := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    have hf := frontier_subset_closure (hfront n)
    rw [h] at hf
    exact hstart n hf
  have hcut (n j : ℕ) (hj : j ≤ n) :=
    lastEntryFragments_strict (Γ n).1.val W hW hnest (hstart' n) (hend n) hj
  obtain ⟨s, x, c, M, hs, hx, hc, hM, hbudget⟩ := exists_actual_oneEnded_limits
    d hU Γ W hcut hprefix hW ha hstart' g hg m hzero
    (lastEntry_toll_zero d Γ W hW ha hstart' hend m hm) A hcost
  let Γs : ℕ → TaggedPhysicalPath d := fun n => Γ (s n)
  apply exists_oneEnded_collar_splicing_of_limits d hU hG ν N Γs (fun n => hΓ (s n))
    F (fun n => hF (s n)) p W hW hnest hshrink (fun n => hstart' (s n))
    (fun n => ha (Nat.add_le_add_right (hs.id_le n) 1) (hend (s n)))
    (fun n => hprefix (s n)) g hg m hm (fun n => hzero (s n)) x c M A hA hx
  · intro hcutS j
    apply (hc j).congr'
    filter_upwards [lastEntryFragmentArray_reindex_eventually d hU Γ W s hs.id_le hcut hcutS j] with n hn
    exact congrArg (fun P : TaggedPhysicalPath d => physicalTollCost d g m P.1) hn.symm
  · exact hM
  · exact hbudget
  · exact hsmall
  · exact houter
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
