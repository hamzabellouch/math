import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

namespace OAI

/-!
# The local facet count in geometric Sperner's lemma

A simplex with `m + 1` vertices has an odd number of facets labelled by all
labels except the last precisely when the simplex is fully labelled. The
proof below identifies the good facets explicitly: one in the fully labelled
case, and two whenever a good facet exists but the simplex is not full.
-/

namespace Tingley

/-- The labels on the distinguished boundary face. -/
def spernerSmallLabels (m : ℕ) : Finset (Fin (m + 1)) :=
  Finset.univ.erase (Fin.last m)

@[simp] theorem mem_spernerSmallLabels {m : ℕ} {i : Fin (m + 1)} :
    i ∈ spernerSmallLabels m ↔ i ≠ Fin.last m := by
  simp [spernerSmallLabels]

@[simp] theorem card_spernerSmallLabels (m : ℕ) :
    (spernerSmallLabels m).card = m := by
  simp [spernerSmallLabels]

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The codimension-one subsets carrying every label except the last. -/
def spernerGoodFacets (m : ℕ) (label : V → Fin (m + 1)) (σ : Finset V) :
    Finset (Finset V) :=
  σ.powerset.filter fun τ => τ.card = m ∧ τ.image label = spernerSmallLabels m

omit [DecidableEq V] in
@[simp] theorem mem_spernerGoodFacets {label : V → Fin (m + 1)}
    {σ τ : Finset V} :
    τ ∈ spernerGoodFacets m label σ ↔
      τ ⊆ σ ∧ τ.card = m ∧ τ.image label = spernerSmallLabels m := by
  simp [spernerGoodFacets]

omit [DecidableEq V] in
/-- A good facet has one vertex of each of its labels. -/
theorem spernerGoodFacet_injOn {label : V → Fin (m + 1)}
    {σ τ : Finset V} (hτ : τ ∈ spernerGoodFacets m label σ) :
    Set.InjOn label (↑τ : Set V) := by
  obtain ⟨_, hc, hi⟩ := mem_spernerGoodFacets.mp hτ
  apply Finset.card_image_iff.mp
  rw [hi, card_spernerSmallLabels, hc]

/-- A fully labelled simplex has exactly one distinguished good facet. -/
theorem spernerGoodFacets_card_of_full (label : V → Fin (m + 1))
    (σ : Finset V) (hσ : σ.card = m + 1)
    (hfull : σ.image label = Finset.univ) :
    (spernerGoodFacets m label σ).card = 1 := by
  classical
  have hinj : Set.InjOn label (↑σ : Set V) := by
    apply Finset.card_image_iff.mp
    simp [hfull, hσ]
  have hlast : Fin.last m ∈ σ.image label := by
    rw [hfull]
    exact Finset.mem_univ _
  obtain ⟨w, hwσ, hwlabel⟩ := Finset.mem_image.mp hlast
  have hcard : (σ.erase w).card = m := by
    simpa [hσ] using (Finset.card_erase_of_mem hwσ)
  have himage : (σ.erase w).image label = spernerSmallLabels m := by
    ext i
    constructor
    · intro hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      apply mem_spernerSmallLabels.mpr
      intro hvl
      exact (Finset.mem_erase.mp hv).1
        (hinj (Finset.mem_erase.mp hv).2 hwσ (hvl.trans hwlabel.symm))
    · intro hi
      have hine : i ≠ Fin.last m := mem_spernerSmallLabels.mp hi
      have hiσ : i ∈ σ.image label := by simp [hfull]
      obtain ⟨v, hvσ, hvi⟩ := Finset.mem_image.mp hiσ
      refine Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨?_, hvσ⟩, hvi⟩
      intro hvw
      apply hine
      calc
        i = label v := hvi.symm
        _ = label w := congrArg label hvw
        _ = Fin.last m := hwlabel
  have hgood : σ.erase w ∈ spernerGoodFacets m label σ :=
    mem_spernerGoodFacets.mpr ⟨Finset.erase_subset _ _, hcard, himage⟩
  have hfamily : spernerGoodFacets m label σ = {σ.erase w} := by
    ext τ
    constructor
    · intro hτ
      obtain ⟨hτσ, hτcard, hτimage⟩ := mem_spernerGoodFacets.mp hτ
      have hwnot : w ∉ τ := by
        intro hwτ
        have hwmem : label w ∈ spernerSmallLabels m := by
          rw [← hτimage]
          exact Finset.mem_image.mpr ⟨w, hwτ, rfl⟩
        exact (mem_spernerSmallLabels.mp hwmem) hwlabel
      have hsub : τ ⊆ σ.erase w := Finset.subset_erase.mpr ⟨hτσ, hwnot⟩
      apply Finset.mem_singleton.mpr
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hτcard])
    · intro hτ
      have hτeq : τ = σ.erase w := Finset.mem_singleton.mp hτ
      simpa [hτeq] using hgood
  rw [hfamily, Finset.card_singleton]

/-- In a non-full simplex, one good facet determines exactly two good facets.
The second is obtained by exchanging the extra vertex with its equal-label
partner in the first facet. -/
theorem spernerGoodFacets_card_of_nonempty_not_full
    (label : V → Fin (m + 1)) (σ : Finset V) (hσ : σ.card = m + 1)
    (hfull : σ.image label ≠ Finset.univ)
    (hne : (spernerGoodFacets m label σ).Nonempty) :
    (spernerGoodFacets m label σ).card = 2 := by
  classical
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨hτσ, hτcard, hτimage⟩ := mem_spernerGoodFacets.mp hτ
  obtain ⟨w, hwτ, hwσeq⟩ := Finset.exists_eq_insert_iff.mpr
    (show τ ⊆ σ ∧ τ.card + 1 = σ.card from ⟨hτσ, by rw [hτcard, hσ]⟩)
  have hwσ : w ∈ σ := hwσeq ▸ Finset.mem_insert_self w τ
  have hwlabel : label w ≠ Fin.last m := by
    intro hwlast
    apply hfull
    rw [← hwσeq, Finset.image_insert, hwlast, hτimage, spernerSmallLabels]
    exact Finset.insert_erase (Finset.mem_univ _)
  have hwimage : label w ∈ τ.image label := by
    rw [hτimage]
    exact mem_spernerSmallLabels.mpr hwlabel
  obtain ⟨u, huτ, hulabel⟩ := Finset.mem_image.mp hwimage
  have huw : u ≠ w := by
    intro huw
    exact hwτ (huw ▸ huτ)
  let υ : Finset V := insert w (τ.erase u)
  have hwυ : w ∈ υ := Finset.mem_insert_self _ _
  have hυcard : υ.card = m := by
    have hw : w ∉ τ.erase u := fun h => hwτ (Finset.erase_subset _ _ h)
    dsimp only [υ]
    rw [Finset.card_insert_of_notMem hw, Finset.card_erase_add_one huτ, hτcard]
  have hυimage : υ.image label = spernerSmallLabels m := by
    calc
      υ.image label = insert (label w) ((τ.erase u).image label) :=
        Finset.image_insert _ _ _
      _ = insert (label u) ((τ.erase u).image label) := by rw [hulabel]
      _ = (insert u (τ.erase u)).image label := (Finset.image_insert _ _ _).symm
      _ = τ.image label := by rw [Finset.insert_erase huτ]
      _ = spernerSmallLabels m := hτimage
  have hυσ : υ ⊆ σ := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact hv.symm ▸ hwσ
    · exact hτσ (Finset.erase_subset _ _ hv)
  have hυgood : υ ∈ spernerGoodFacets m label σ :=
    mem_spernerGoodFacets.mpr ⟨hυσ, hυcard, hυimage⟩
  have hτυ : τ ≠ υ := by
    intro heq
    exact hwτ (heq.symm ▸ hwυ)
  have hfamily : spernerGoodFacets m label σ = {τ, υ} := by
    ext η
    constructor
    · intro hη
      obtain ⟨hησ, hηcard, _⟩ := mem_spernerGoodFacets.mp hη
      have hηinsert : η ⊆ insert w τ := by simpa only [hwσeq] using hησ
      by_cases hwη : w ∈ η
      · have huη : u ∉ η := by
          intro huη
          exact huw ((spernerGoodFacet_injOn hη) huη hwη hulabel)
        have hηυ : η ⊆ υ := by
          intro v hvη
          rcases Finset.mem_insert.mp (hηinsert hvη) with hvw | hvτ
          · exact Finset.mem_insert.mpr (Or.inl hvw)
          · apply Finset.mem_insert.mpr
            right
            apply Finset.mem_erase.mpr
            refine ⟨?_, hvτ⟩
            intro hvu
            exact huη (hvu ▸ hvη)
        have hηeq : η = υ := Finset.eq_of_subset_of_card_le hηυ
          (by rw [hυcard, hηcard])
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr hηeq
      · have hητ : η ⊆ τ := by
          intro v hvη
          rcases Finset.mem_insert.mp (hηinsert hvη) with hvw | hvτ
          · exact False.elim (hwη (hvw ▸ hvη))
          · exact hvτ
        have hηeq : η = τ := Finset.eq_of_subset_of_card_le hητ
          (by rw [hτcard, hηcard])
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl hηeq
    · intro hη
      rcases Finset.mem_insert.mp hη with hη | hη
      · simpa [hη] using hτ
      · have hηeq : η = υ := Finset.mem_singleton.mp hη
        simpa [hηeq] using hυgood
  rw [hfamily]
  simp [hτυ]

/-- The local mod-two incidence identity, valid also in dimension zero. -/
theorem spernerGoodFacets_card_mod_two (label : V → Fin (m + 1))
    (σ : Finset V) (hσ : σ.card = m + 1) :
    ((spernerGoodFacets m label σ).card : ZMod 2) =
      if σ.image label = Finset.univ then 1 else 0 := by
  classical
  by_cases hfull : σ.image label = Finset.univ
  · simpa only [ite_eq_left hfull, spernerGoodFacets_card_of_full label σ hσ hfull]
      using (Nat.cast_one : ((1 : ℕ) : ZMod 2) = 1)
  · rw [ite_eq_right hfull]
    by_cases hne : (spernerGoodFacets m label σ).Nonempty
    · simpa only [spernerGoodFacets_card_of_nonempty_not_full label σ hσ hfull hne]
        using (ZMod.natCast_self 2)
    · have hempty : spernerGoodFacets m label σ = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty]

end Tingley

end OAI
