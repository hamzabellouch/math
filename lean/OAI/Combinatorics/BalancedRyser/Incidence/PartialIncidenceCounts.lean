import OAI.Combinatorics.BalancedRyser.Incidence.PartialIncidence
import OAI.Combinatorics.BalancedRyser.Probability.GeneratorEnumeration

namespace OAI

namespace Balanced.PartialAlignment
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev IncidenceCode (F : Type*) :=
  ((Fin 4 → Direction F) × (Fin 4 → Bool)) × Direction F

def transverseHitCodes (D : Finset (Direction F)) (j : ℕ) (L : Line F) :
    Finset (IncidenceCode F) :=
  ((tupleCodesWithOldCount D j).product Finset.univ).filter
    (fun z => Function.Injective z.1.1 ∧ (∀ i, z.1.1 i ≠ z.2) ∧ z.2 ≠ L.1)

def transverseHitCodeProbability (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F) (z : IncidenceCode F) : ℝ :=
  (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)).toOuterMeasure
    {M | (∃ c, ∀ i, OnLine (tuplePoint M ⟨z.1.1,z.1.2⟩ i) (z.2,c)) ∧
      ∃ i, OnLine (tuplePoint M ⟨z.1.1,z.1.2⟩ i) L}).toReal

omit [Field F] in

theorem card_transverseHitCodes_one_le (D : Finset (Direction F)) (L : Line F) :
    (transverseHitCodes D 1 L).card ≤
      64 * D.card * Fintype.card (Direction F) ^ 4 := by
  calc
    _ ≤ ((tupleCodesWithOldCount D 1).product
        (Finset.univ : Finset (Direction F))).card := Finset.card_filter_le _ _
    _ = (tupleCodesWithOldCount D 1).card * Fintype.card (Direction F) := by simp
    _ ≤ (16 * (Nat.choose 4 1 * D.card ^ 1 *
        Fintype.card (Direction F) ^ (4 - 1))) * Fintype.card (Direction F) :=
      Nat.mul_le_mul_right _ (card_tupleCodesWithOldCount_le D 1)
    _ = _ := by norm_num; ring

theorem transverseHitCodeProbability_one_le (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L)
    (z : IncidenceCode F) (hz : z ∈ transverseHitCodes D 1 L) :
    transverseHitCodeProbability D a L z ≤ 4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  obtain ⟨hz,hgen,hg,htrans⟩ := Finset.mem_filter.mp hz
  have hcode := (Finset.mem_product.mp hz).1
  have hcard := (Finset.mem_filter.mp (Finset.mem_product.mp hcode).1).2
  exact canonical_conditional_one_exposed_hit_probability_le
    ⟨z.1.1,z.1.2⟩ hgen D a z.2 hg (by simpa [exposedTupleIndices] using hcard.le)
    L htrans havoid

theorem sum_transverseHitCodeProbability_one_le (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (∑ z ∈ transverseHitCodes D 1 L, transverseHitCodeProbability D a L z) ≤
      4096 * (D.card : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hdir : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    have hd : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
      simp only [Direction, Fintype.card_option]
      omega
    exact_mod_cast hd
  have hcount : ((transverseHitCodes D 1 L).card : ℝ) ≤
      64 * (D.card : ℝ) * (Fintype.card (Direction F) : ℝ) ^ 4 := by
    exact_mod_cast card_transverseHitCodes_one_le D L
  calc
    _ ≤ ∑ _z ∈ transverseHitCodes D 1 L, 4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro z hz
      exact transverseHitCodeProbability_one_le D a L havoid z hz
    _ = ((transverseHitCodes D 1 L).card : ℝ) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by simp
    _ ≤ (64 * (D.card : ℝ) * (Fintype.card (Direction F) : ℝ) ^ 4) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by gcongr
    _ ≤ (64 * (D.card : ℝ) * (2 * (Fintype.card F : ℝ)) ^ 4) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by gcongr
    _ = _ := by field_simp; ring

end
end Balanced.PartialAlignment

end OAI
