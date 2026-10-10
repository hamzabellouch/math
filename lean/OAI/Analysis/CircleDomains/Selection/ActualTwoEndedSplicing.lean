import OAI.Analysis.CircleDomains.Topology.TwoEndedCollarSplicing
import OAI.Analysis.CircleDomains.Modulus.ActualTwoEndedBudget
import OAI.Analysis.CircleDomains.Selection.FragmentReindexing

namespace OAI

/-! The two-ended collar construction on restrictions of the original paths,
with joint limits and finite budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_actual_twoEnded_collar_splicing
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : X) (V W : ℕ → Set X) (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hnestV : ∀j, closure (V (j+1)) ⊆ V j) (hnestW : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrinkV : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ O)
    (hshrinkW : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstartV : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hendW : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (hdis : Disjoint (closure (V 0)) (closure (W 0)))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀j z, z ∈ frontier (V j) → m z = 0)
    (hmW : ∀j z, z ∈ frontier (W j) → m z = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (hsmallV : ∀j, HasShortCollarJoining d ν N g m (frontier (V (j+1))) (closure (V j)))
    (hsmallW : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houterV : HasShortCollarJoining d ν N g m (frontier (V 0)) univ)
    (houterW : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have haV : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestV j))
  have haW : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestW j))
  have hstart (n : ℕ) : (Γ n).1.val ⊥ ∈ V 0 := haV (Nat.zero_le _) (hstartV n)
  have hend (n : ℕ) : (Γ n).1.val ⊤ ∈ W 0 := haW (Nat.zero_le _) (hendW n)
  have hendV (n : ℕ) : (Γ n).1.val ⊤ ∉ V 0 := fun h =>
    disjoint_left.mp hdis (subset_closure h) (subset_closure (hend n))
  have hstartW (n : ℕ) : (Γ n).1.val ⊥ ∉ W 0 := fun h =>
    disjoint_left.mp hdis (subset_closure (hstart n)) (subset_closure h)
  have hleft (n j : ℕ) (hj : j ≤ n) :=
    firstExitFragments_strict (Γ n).1.val V hV hnestV (hstartV n) (hendV n) hj
  have hright (n j : ℕ) (hj : j ≤ n) :=
    lastEntryFragments_strict (Γ n).1.val W hW hnestW (hstartW n) (hendW n) hj
  have hmid (n : ℕ) := firstExit_lt_lastEntry (Γ n).1.val (hV 0) (hW 0) hdis (hstart n) (hend n)
  obtain ⟨s, x, y, c, e, M, hs, hx, hy, hc, he, hM, hbudget⟩ := exists_actual_twoEnded_limits
    d hU Γ V W hleft hright hmid hV hW haV haW hendV hstartW g hg m
    (firstExit_toll_zero d Γ V hV haV hstartV hendV m hmV)
    (lastEntry_toll_zero d Γ W hW haW hstartW hendW m hmW) A hcost
  let Γs : ℕ → TaggedPhysicalPath d := fun n => Γ (s n)
  apply exists_twoEnded_collar_splicing_of_limits d hU hG ν N Γs (fun n => hΓ (s n))
    p q V W hV hW hnestV hnestW hshrinkV hshrinkW
    (fun n => haV (Nat.add_le_add_right (hs.id_le n) 1) (hstartV (s n)))
    (fun n => hendV (s n)) (fun n => hstartW (s n))
    (fun n => haW (Nat.add_le_add_right (hs.id_le n) 1) (hendW (s n)))
    (fun n => hmid (s n)) g hg m hmV hmW x y c e M A hA hx hy
  · intro hcutS j
    apply (hc j).congr'
    filter_upwards [firstExitFragmentArray_reindex_eventually d hU Γ V s hs.id_le hleft hcutS j] with n hn
    exact congrArg (fun P : TaggedPhysicalPath d => physicalTollCost d g m P.1) hn.symm
  · intro hcutS j
    apply (he j).congr'
    filter_upwards [lastEntryFragmentArray_reindex_eventually d hU Γ W s hs.id_le hright hcutS j] with n hn
    exact congrArg (fun P : TaggedPhysicalPath d => physicalTollCost d g m P.1) hn.symm
  · exact hM
  · exact hbudget
  · exact hsmallV
  · exact hsmallW
  · exact houterV
  · exact houterW
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
