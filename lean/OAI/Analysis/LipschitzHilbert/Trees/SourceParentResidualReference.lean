import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualEnvelopes
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferencePhysicalIdentity

namespace OAI

/-! A square estimate uses the parent residual cone. Its exact packet
restriction can be recentered at the path slope; no equality with the
original reference slope is required. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem packetResidual_eq_of_support_subset {σ E : Type*} [AddCommMonoid E] [Module ℂ E]
    (g : AngularGrid) (small big : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ)
    (hsub : small ⊆ big)
    (hsupport : ((g.packetSet big slope stop lower cell).filter
      (fun q => stop q < upper)) ⊆ small) :
    g.packetResidual small slope stop base transition lower upper cell =
      g.packetResidual big slope stop base transition lower upper cell := by
  unfold packetResidual
  apply Finset.sum_congr
  · ext q
    simp only [packetSet,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq,hcell,hlo⟩,hhi⟩
      exact ⟨⟨hsub hq,hcell,hlo⟩,hhi⟩
    · rintro ⟨⟨hq,hcell,hlo⟩,hhi⟩
      exact ⟨⟨hsupport (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hq,hcell,hlo⟩,hhi⟩),hcell,hlo⟩,hhi⟩
  · intro q _
    rfl

end AngularGrid
namespace SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Every actual short residual is unchanged after restriction to the
fixed parent cone. This includes the terminal block. -/
theorem short_parent_residual_eq {τ E : Type*} [AddCommMonoid E] [Module ℂ E]
    (P : SourceLabeledLattice N κ Label Item) (grid : AngularGrid)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (slope : τ → ℝ)
    (t R C B w : ℝ) (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ j, grid.eligible (grid.rootWidth/B^2) (w/P.length j) 0)
    (hangle : ∀ q ∈ packets,
      |t+P.rowSlope q.1 q.2.1-slope (assigned q)| ≤ C*(w/P.length q.1))
    (base : P.PacketIndex → E) (transition : ℕ → ℤ → ℂ)
    (lower upper : ℕ) (pathSlope : ℝ)
    (hwidth : grid.width lower ≤ B*grid.width upper) :
    let stop := fun q : P.PacketIndex => grid.lastEligible (grid.rootWidth/B^2)
      (w/P.length q.1) (div_pos hw (P.length_pos q.1))
    let short := packets.filter (fun q => P.length q.1 ≤ R)
    let selected := sourceReferencePackets packets (fun q => P.length q.1)
      (fun q => t+P.rowSlope q.1 q.2.1) R pathSlope (C+B^3) w
    grid.packetResidual selected (fun q => slope (assigned q)) stop base transition
      lower upper (grid.index lower pathSlope) =
    grid.packetResidual short (fun q => slope (assigned q)) stop base transition
      lower upper (grid.index lower pathSlope) := by
  dsimp only
  apply grid.packetResidual_eq_of_support_subset
  · intro q hq
    obtain ⟨hqp,hshort,_⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hqp,hshort⟩
  · exact grid.short_residual_subset_reference packets (fun q => slope (assigned q))
      (fun q => P.length q.1) (fun q => t+P.rowSlope q.1 q.2.1)
      (fun q => P.length_pos q.1) hw hB (fun q _ => hzero q.1) hangle lower upper hwidth

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
