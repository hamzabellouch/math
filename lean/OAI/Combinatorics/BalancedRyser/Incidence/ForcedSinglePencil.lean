import OAI.Combinatorics.BalancedRyser.Incidence.SinglePencilObstruction
import OAI.Combinatorics.BalancedRyser.Probability.ForcedNonsplitLabels

namespace OAI

namespace Balanced.Configuration
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem forcedNonsplitLabel_through (C : Configuration F) (p : Point F)
    (d : Direction F) : C.NonsplitThrough p (C.forcedNonsplitLabel p d) := by
  classical
  unfold forcedNonsplitLabel
  split
  · rename_i hc
    obtain ⟨⟨e, side⟩, _, he⟩ := Finset.mem_image.mp hc
    have hed : e = d := congrArg Prod.fst he
    subst e
    refine ⟨side, ?_⟩
    rw [he]
    rfl
  · exact onLine_lineThrough d p

theorem forcedNonsplitLabels_through (C : Configuration F) (p : Point F)
    (b : BlockLabel F) (hb : b ∈ C.forcedNonsplitLabels p) : C.NonsplitThrough p b := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hb
  exact forcedNonsplitLabel_through C p d

theorem one_split_impossible_of_pencil_budget (C : Configuration F) (hV : C.Valid)
    {rho : ℝ} {cap : ℕ} (hO : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) : C.splitMultiplicity p ≠ 1 := by
  classical
  intro hb
  have hsub := C.forcedNonsplitLabels_subset hV hO hsize B hlabels hcover p hbudget
  have hAcard : Fintype.card F ≤ (C.forcedNonsplitLabels p).card := by
    have hsum := C.forcedNonsplitLabels_card_add p
    omega
  apply C.one_split_cover_impossible hV p hb B (C.forcedNonsplitLabels p)
    (fun b hbB => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabels b hbB⟩)
    hsub hcard hAcard (C.forcedNonsplitLabels_through p)
  intro x hx
  obtain ⟨b, hbB, hxb⟩ := hcover x hx
  exact Finset.mem_biUnion.mpr ⟨b, hbB, hxb⟩

end
end Balanced.Configuration

end OAI
