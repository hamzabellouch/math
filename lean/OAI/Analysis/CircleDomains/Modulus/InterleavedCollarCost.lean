import OAI.Analysis.CircleDomains.Topology.InterleavedCollarPieces

namespace OAI

/-! Gluing retained fragments and genuine short joining arcs into one
allowed collar path, with the sum of their actual costs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

abbrev TaggedPhysicalPath (d : PathCodeData X Y) :=
  FinitePhysicalPath d.domainEquiv d.basePoint × (ℕ → TagSlot)

def physicalTollCost (d : PathCodeData X Y) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) : ℝ≥0∞ :=
  (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) + boundaryToll γ.val m

theorem exists_allowed_interleaved_collar
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (p : X) (a b : ℕ → TaggedPhysicalPath d)
    (ha : ∀n, AllowedTaggedPath d ν N ((a n).1.val, (a n).2))
    (hb : ∀n, AllowedTaggedPath d ν N ((b n).1.val, (b n).2))
    (hleft : ∀n, (b n).1.val ⊥ = (a (n+1)).1.val ⊤)
    (hright : ∀n, (b n).1.val ⊤ = (a n).1.val ⊥)
    (hatail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, ∀s, (a n).1.val s ∈ V)
    (hbtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, ∀s, (b n).1.val s ∈ V)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hpos : ∀y ∈ d.physicalDomain, c ≤ g y)
    (ha0 : ∀n, m ((a n).1.val ⊥) = 0) (ha1 : ∀n, m ((a n).1.val ⊤) = 0)
    (hb0 : ∀n, m ((b n).1.val ⊥) = 0) (hb1 : ∀n, m ((b n).1.val ⊤) = 0)
    (A E : ℝ≥0∞) (hA : A < ∞) (hE : E < ∞)
    (hacost : (∑'n, physicalTollCost d g m (a n).1) ≤ A)
    (hbcost : (∑'n, physicalTollCost d g m (b n).1) ≤ E)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (η : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, θ) ∧ η.val ⊥ = p ∧ η.val ⊤ = (a 0).1.val ⊤ ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + E := by
  let Γ := interleavePieces a b
  have hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2) := by
    intro n
    dsimp [Γ, interleavePieces]
    split
    · exact ha _
    · exact hb _
  have hΓ0 : ∀n, m ((Γ n).1.val ⊥) = 0 := by
    intro n
    dsimp [Γ, interleavePieces]
    split
    · exact ha0 _
    · exact hb0 _
  have hΓ1 : ∀n, m ((Γ n).1.val ⊤) = 0 := by
    intro n
    dsimp [Γ, interleavePieces]
    split
    · exact ha1 _
    · exact hb1 _
  have hpath (n : ℕ) (s : PathTime) : (Γ n).1.val s =
      interleavePieces (fun n => ((a n).1.val : PathTime → X))
        (fun n => ((b n).1.val : PathTime → X)) n s := by
    dsimp [Γ, interleavePieces]
    split <;> rfl
  have hsum : (∑'n, physicalTollCost d g m (Γ n).1) ≤ A + E := by
    have he := tsum_cost_interleavePieces a b (fun γ => physicalTollCost d g m γ.1)
    exact he.le.trans (add_le_add hacost hbcost)
  have hjoin : ∀n, (Γ (n+1)).1.val ⊤ = (Γ n).1.val ⊥ := by
    intro n
    rw [hpath, hpath]
    exact interleavePieces_join (fun n => (a n).1.val) (fun n => (b n).1.val) hleft hright n
  have htail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, ∀s, (Γ n).1.val s ∈ V := by
    intro V hV
    obtain ⟨k, hk⟩ := interleavePieces_tail
      (fun n => (a n).1.val) (fun n => (b n).1.val) p hatail hbtail V hV
    refine ⟨k, ?_⟩
    intro n hn s
    rw [hpath]
    exact hk n hn s
  obtain ⟨η, θ, hη, hη0, hη1, hcost⟩ := exists_allowed_collar_of_summable_cost d hU hG ν N
    p (fun n => (Γ n).1) (fun n => (Γ n).2) hΓ hjoin htail g hg m c hc hpos hΓ0 hΓ1
    (hsum.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, hE⟩)) hpoint
  refine ⟨η, θ, hη, hη0, ?_, hcost.le.trans hsum⟩
  simpa [Γ, interleavePieces] using hη1

end CircleDomainRigidity

end

end OAI
