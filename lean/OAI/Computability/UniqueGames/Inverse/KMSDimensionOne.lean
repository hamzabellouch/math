import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.Inverse.KMSFoundationLemmas

namespace OAI

section

/-!
# A proved one-dimensional Grassmann expansion case

Distinct lines always intersect trivially, so this Grassmann graph is complete.
Its retention never exceeds global density. This proves a genuine restricted
expansion statement; it does not imply the OPEN large-dimension KMS principle.
-/

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

theorem adjacent_one_iff {n : ℕ} (L M : Vertex n 1) :
    Adjacent L M ↔ L ≠ M := by
  constructor
  · exact fun h => h.1
  · intro hne
    refine ⟨hne, ?_⟩
    have hle : Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) ≤ 1 :=
      (Submodule.finrank_mono inf_le_left).trans_eq L.property
    have hnot : Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) ≠ 1 := by
      intro heq
      have hL : L.val ⊓ M.val = L.val :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (heq.trans L.property.symm)
      have hM : L.val ⊓ M.val = M.val :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right (heq.trans M.property.symm)
      exact hne (Subtype.ext (hL.symm.trans hM))
    omega

theorem neighbors_one_eq {n : ℕ} (L : Vertex n 1) :
    neighbors L = Finset.univ.erase L := by
  ext M
  simp [neighbors, adjacent_one_iff, ne_comm]

private theorem inter_univ_erase {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (x : Ω) : S ∩ Finset.univ.erase x = S.erase x := by
  ext y
  simp [and_comm]

theorem dimensionOne_neighbor_density {n : ℕ} (S : Finset (Vertex n 1))
    {L : Vertex n 1} (hL : L ∈ S) :
    relativeDensity S (neighbors L) =
      ((S.card : ℝ) - 1) / ((Fintype.card (Vertex n 1) : ℝ) - 1) := by
  unfold relativeDensity
  rw [neighbors_one_eq, inter_univ_erase, Finset.card_erase_of_mem hL,
    Finset.card_erase_of_mem (Finset.mem_univ L), Finset.card_univ]
  have hS : 1 ≤ S.card := Finset.one_le_card.mpr ⟨L, hL⟩
  have hV : 1 ≤ Fintype.card (Vertex n 1) := Fintype.card_pos_iff.mpr ⟨L⟩
  rw [Nat.cast_sub hS, Nat.cast_sub hV]
  norm_num

/-- Exact retention of a nonempty collection of binary lines. -/
theorem dimensionOne_retention {n : ℕ} (S : Finset (Vertex n 1))
    (hS : S.Nonempty) :
    retention S = ((S.card : ℝ) - 1) /
      ((Fintype.card (Vertex n 1) : ℝ) - 1) := by
  have hsum : (∑ L ∈ S, relativeDensity S (neighbors L)) =
      (S.card : ℝ) * (((S.card : ℝ) - 1) /
        ((Fintype.card (Vertex n 1) : ℝ) - 1)) := by
    calc
      _ = ∑ _L ∈ S, ((S.card : ℝ) - 1) /
          ((Fintype.card (Vertex n 1) : ℝ) - 1) :=
        Finset.sum_congr rfl fun _ hL => dimensionOne_neighbor_density S hL
      _ = _ := by simp
  unfold retention
  rw [hsum]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS))

/-- The one-dimensional Grassmann graph has retention at most global density.
The cardinality hypothesis rules out the single-vertex, zero-degree case. -/
theorem dimensionOne_retention_le_density {n : ℕ} (S : Finset (Vertex n 1))
    (hS : S.Nonempty) (hV : 1 < Fintype.card (Vertex n 1)) :
    retention S ≤ relativeDensity S Finset.univ := by
  rw [dimensionOne_retention S hS]
  simp only [relativeDensity, Finset.inter_univ, Finset.card_univ]
  have hV' : (1 : ℝ) < Fintype.card (Vertex n 1) := Nat.one_lt_cast.mpr hV
  have hcard : (S.card : ℝ) ≤ Fintype.card (Vertex n 1) :=
    Nat.cast_le.mpr (Finset.card_le_univ S)
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- In dimension one, the whole ambient interval already has the required
density. This is a proved special case, not a premise for higher dimensions. -/
theorem dimensionOne_dense_interval {n : ℕ} (S : Finset (Vertex n 1))
    (hS : S.Nonempty) (hV : 1 < Fintype.card (Vertex n 1))
    {ζ : ℝ} (hζ : ζ ≤ retention S) :
    ζ ≤ relativeDensity S (interval (⊥ : Submodule F2 (Ambient n)) ⊤) := by
  have hI : interval (ell := 1) (⊥ : Submodule F2 (Ambient n)) ⊤ =
      Finset.univ := by simp [interval]
  rw [hI]
  exact hζ.trans (dimensionOne_retention_le_density S hS hV)

end
end UniqueGamesTheorem.Inverse.KMS

end

end OAI
