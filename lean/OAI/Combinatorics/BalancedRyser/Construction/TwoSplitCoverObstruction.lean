import OAI.Combinatorics.BalancedRyser.Construction.ConstructionPartners
import OAI.Combinatorics.BalancedRyser.Construction.CoverObstruction
import OAI.Combinatorics.BalancedRyser.Construction.LocalCoverObstruction
import OAI.Combinatorics.BalancedRyser.Probability.BlockCapacity

namespace OAI

namespace Balanced.Configuration

noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem splitMultiplicity_le_order_add_one (p : Point F) :
    C.splitMultiplicity p ≤ Fintype.card F + 1 := by
  calc
    C.splitMultiplicity p ≤ (Finset.univ.filter (fun l : Line F => OnLine p l)).card := by
      apply Finset.card_le_card
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    _ = Fintype.card F + 1 := card_lines_through p

theorem two_split_cover_impossible_after_forcing
    (hvalid : C.Valid) (hcompat : C.Compatible)
    (p : Point F) (hb : C.splitMultiplicity p = 2)
    (labels forced : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hsize : labels.card ≤ Fintype.card F)
    (hsubset : forced ⊆ labels)
    (hcount : Fintype.card F - 1 ≤ forced.card)
    (hforced : C.designatedAt p ∩ forced.biUnion C.blockPoints ⊆ C.partnerSet p) :
    ¬ C.points ⊆ labels.biUnion C.blockPoints := by
  classical
  intro hcover
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hremaining : (labels \ forced).card ≤ 1 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hsubset
    omega
  have htarget : (C.designatedAt p).card = 8 := by
    simpa [hb] using ConfigurationStructure.designated_at_card C hvalid hcompat p
  have hpartner : (C.partnerSet p).card ≤ 2 := by
    simpa [hb] using ConstructionPartners.partner_card_le_splitMultiplicity
      C hvalid hcompat p (by omega)
  exact CoverObstruction.eight_points_not_covered_by_two_and_four
    (C.designatedAt p) (C.partnerSet p) (labels \ forced) C.blockPoints
    htarget hpartner hremaining
    (fun b hb' => C.two_split_block_capacity hvalid p hb b
      (hlabels b (Finset.mem_sdiff.mp hb').1))
    (C.residual_cover_after_forcing p labels forced hcover hforced)

omit [Field F] [DecidableEq F] in
theorem zero_split_forced_count_impossible
    (labels forced : Finset (BlockLabel F))
    (hsize : labels.card ≤ Fintype.card F)
    (hsubset : forced ⊆ labels)
    (hcount : Fintype.card F + 1 ≤ forced.card) : False := by
  have hle := Finset.card_le_card hsubset
  omega

end
end Balanced.Configuration

end OAI
