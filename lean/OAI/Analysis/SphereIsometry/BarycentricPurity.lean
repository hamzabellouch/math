import OAI.Analysis.SphereIsometry.BarycentricIncidence
import OAI.Analysis.SphereIsometry.SubdivisionData

namespace OAI

/-!
# Purity of the actual finite face-chain subdivision

A finite chain can be completed at any positive rank below a retained upper
face. A chain of maximum cardinality among the extensions of a given face
therefore has every rank up to the dimension of an old top face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

/-- Insert an old face of a prescribed positive rank, provided the flag
already contains some old face of at least that rank. The inserted face is
allowed to be already present. -/
theorem chain_exists_insert_rank {c : Finset (FaceVertex K)} (hc : K.chain c)
    {r : ℕ} (hr : 0 < r) (hupper : ∃ U ∈ c, r ≤ U.val.card) :
    ∃ a : FaceVertex K, a.val.card = r ∧ K.chain (insert a c) := by
  classical
  let upper := c.filter (fun b => r ≤ b.val.card)
  have hupp : upper.Nonempty := by
    obtain ⟨U, hUc, hUr⟩ := hupper
    exact ⟨U, Finset.mem_filter.mpr ⟨hUc, hUr⟩⟩
  obtain ⟨U, hUupper, hUmin⟩ := upper.exists_min_image (fun b => b.val.card) hupp
  have hUc : U ∈ c := (Finset.mem_filter.mp hUupper).1
  have hUr : r ≤ U.val.card := (Finset.mem_filter.mp hUupper).2
  obtain ⟨L, hLU, hLcard, hLmax⟩ :
      ∃ L : Finset V, L ⊆ U.val ∧ L.card ≤ r ∧
        ∀ b ∈ c, b.val.card < r → b.val ⊆ L := by
    let lower := c.filter (fun b => b.val.card < r)
    by_cases hlower : lower.Nonempty
    · obtain ⟨L, hLlower, hLmax⟩ := lower.exists_max_image (fun b => b.val.card) hlower
      have hLc : L ∈ c := (Finset.mem_filter.mp hLlower).1
      have hLr : L.val.card < r := (Finset.mem_filter.mp hLlower).2
      refine ⟨L.val, chain_subset_of_card_le hc hLc hUc (by omega),
        hLr.le, ?_⟩
      intro b hb hbr
      exact chain_subset_of_card_le hc hb hLc
        (hLmax b (Finset.mem_filter.mpr ⟨hb, hbr⟩))
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro b hb hbr
      exact False.elim (hlower ⟨b, Finset.mem_filter.mpr ⟨hb, hbr⟩⟩)
  obtain ⟨W, hLW, hWU, hWcard⟩ := Finset.exists_subsuperset_card_eq hLU hLcard hUr
  let a : FaceVertex K :=
    ⟨W, K.down_closed U.property.1 hWU, Finset.card_pos.mp (by omega)⟩
  refine ⟨a, hWcard, chain_insert_iff.mpr ⟨hc, ?_⟩⟩
  intro b hb
  rcases lt_or_ge b.val.card r with hbr | hrb
  · exact Or.inr ((hLmax b hb hbr).trans hLW)
  · have hUb : U.val ⊆ b.val :=
      chain_subset_of_card_le hc hUc hb
        (hUmin b (Finset.mem_filter.mpr ⟨hb, hrb⟩))
    exact Or.inl (hWU.trans hUb)

/-- In a pure old complex, every flag has a common old top face above it. -/
theorem chain_exists_top_upper {m : ℕ} (hK : K.Pure m)
    {c : Finset (FaceVertex K)} (hc : K.chain c) :
    ∃ T : FaceVertex K, T.val.card = m + 1 ∧ ∀ b ∈ c, b.val ⊆ T.val := by
  classical
  obtain ⟨s, hs, hmax⟩ : ∃ s ∈ K.topCells m, ∀ b ∈ c, b.val ⊆ s := by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨s, hs, _⟩ := hK ∅ K.empty_mem
      refine ⟨s, hs, ?_⟩
      intro b hb
      simp at hb
    · obtain ⟨a, ha, hamax⟩ := exists_greatest hc hne
      obtain ⟨s, hs, has⟩ := hK a.val a.property.1
      exact ⟨s, hs, fun b hb => (hamax b hb).trans has⟩
  let T : FaceVertex K :=
    ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
  exact ⟨T, (mem_topCells.mp hs).2, hmax⟩

/-- Every face of the subdivision extends to an actual top flag. -/
theorem sd_pure {m : ℕ} (hK : K.Pure m) : K.sd.Pure m := by
  classical
  intro c hc
  let extensions := K.sd.faces.filter (fun d => c ⊆ d)
  have hcExt : c ∈ extensions :=
    Finset.mem_filter.mpr ⟨hc, Finset.Subset.refl _⟩
  obtain ⟨d, hdExt, hdmax⟩ := extensions.exists_max_image Finset.card ⟨c, hcExt⟩
  have hdface : d ∈ K.sd.faces := (Finset.mem_filter.mp hdExt).1
  have hcd : c ⊆ d := (Finset.mem_filter.mp hdExt).2
  have hdchain := mem_sd_iff.mp hdface
  have hclosed : ∀ a : FaceVertex K, K.chain (insert a d) → a ∈ d := by
    intro a ha
    by_contra hanot
    have hinsert : insert a d ∈ extensions :=
      Finset.mem_filter.mpr ⟨mem_sd_iff.mpr ha, hcd.trans (Finset.subset_insert _ _)⟩
    have hle := hdmax (insert a d) hinsert
    rw [Finset.card_insert_of_notMem hanot] at hle
    omega
  obtain ⟨T, hTcard, hTmax⟩ := chain_exists_top_upper hK hdchain
  have hTd : T ∈ d := hclosed T (chain_insert_iff.mpr
    ⟨hdchain, fun b hb => Or.inr (hTmax b hb)⟩)
  have hranks : K.ranks d = Finset.Icc 1 (m + 1) := by
    apply Finset.Subset.antisymm (ranks_subset hK.cardBound d)
    intro r hr
    obtain ⟨hrpos, hrtop⟩ := Finset.mem_Icc.mp hr
    obtain ⟨a, hacard, hainsert⟩ := chain_exists_insert_rank hdchain
      (show 0 < r by omega) (show ∃ U ∈ d, r ≤ U.val.card from
        ⟨T, hTd, by rw [hTcard]; exact hrtop⟩)
    exact mem_ranks.mpr ⟨a, hclosed a hainsert, hacard⟩
  have hdcard : d.card = m + 1 := by
    rw [← card_ranks hdchain, hranks]
    simp
  exact ⟨d, mem_topCells.mpr ⟨hdface, hdcard⟩, hcd⟩

end Tingley.FiniteComplex

namespace Tingley

/-- Every face of every iterated subdivision of the simplex extends to a
top-dimensional face. The dimension-zero case is included. -/
theorem iter_pure (m k : ℕ) : (iterData (Fin (m + 1)) k).complex.Pure m := by
  classical
  induction k with
  | zero =>
      intro s hs
      refine ⟨Finset.univ, FiniteComplex.mem_topCells.mpr ⟨?_, ?_⟩,
        Finset.subset_univ _⟩
      · exact FiniteComplex.mem_full _
      · change (Finset.univ : Finset (Fin (m + 1))).card = m + 1
        exact Finset.card_fin (m + 1)
  | succ k ih => exact FiniteComplex.sd_pure ih

end Tingley

end

end OAI
