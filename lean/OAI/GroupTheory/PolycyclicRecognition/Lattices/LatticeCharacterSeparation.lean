import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactCharacterSeparation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InwardVectorCharacters

namespace OAI

/-! # An integral separating direction from a compact character set -/

noncomputable section
namespace PolycyclicRecognition
open scoped InnerProductSpace
variable {Q E : Type} [CommGroup Q] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_lattice_character_separator (e : Q →* Multiplicative E)
    (hcover : ∃ R : ℝ, ∀ x : E, ∃ q, ‖(e q).toAdd - x‖ ≤ R)
    {C : Set E} (hC : IsCompact C) (hunit : ∀ v ∈ C, ‖v‖ = 1)
    (hzero : (0 : E) ∉ convexHull ℝ C) :
    ∃ t : Q, ∀ v ∈ C, 0 < (inwardVectorCharacter e v t).toAdd := by
  obtain ⟨w, δ, hδ, hw⟩ := exists_inner_separator_of_compact_no_convex_zero hC hzero
  obtain ⟨R, hR⟩ := hcover
  obtain ⟨n, hn⟩ := exists_nat_gt (R / δ)
  have hnR : R < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  obtain ⟨t, ht⟩ := hR (-((n : ℝ) • w))
  refine ⟨t, ?_⟩
  intro v hv
  have herror : ⟪v, (e t).toAdd + (n : ℝ) • w⟫_ℝ ≤ R := by
    have hb := real_inner_le_norm v ((e t).toAdd + (n : ℝ) • w)
    rw [hunit v hv, one_mul] at hb
    exact hb.trans (by simpa only [sub_neg_eq_add] using ht)
  rw [inner_add_right, real_inner_smul_right, ← real_inner_comm v w] at herror
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left (hw v hv).le hn0
  change 0 < -⟪v, (e t).toAdd⟫_ℝ
  linarith

end PolycyclicRecognition

end

end OAI
