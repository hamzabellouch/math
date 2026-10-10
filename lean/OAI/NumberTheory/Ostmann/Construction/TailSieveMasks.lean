import OAI.NumberTheory.Ostmann.ZeroDensity.TailDensityMask
import OAI.NumberTheory.Ostmann.Characters.SparsePairEnergyBudget

namespace OAI

/-! # The two complementary residue masks used by the integer-tail sieve -/
namespace Ostmann
open scoped Classical

theorem tailDensityMask_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) (hp : 0 < p) :
    (tailDensityMask A N p).Nonempty :=
  (tailSupport_nonempty hA N p hp).image _

theorem tailDensityMask_eq_tailResidues (A : Set ℕ) (N p : ℕ) [NeZero p] (_hp : 0 < p) :
    (tailDensityMask A N p : Set (ZMod p)) = tailResidues A N p := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hr).2
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), by simpa⟩,
      ZMod.natCast_zmod_val x⟩

theorem negativeSummandTail_mem_mask_complement {A B : Set ℕ} (N lo hi p : ℕ) [NeZero p]
    (hp : 0 < p) (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hlo : N + p ≤ lo) {x : ℤ} (hx : x ∈ negativeSummandTail B lo hi) :
    (x : ZMod p) ∈ Finset.univ \ tailDensityMask A N p := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hbB, hblo, _⟩ := (mem_summandTail B lo hi b).mp hb
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hm
  have hh : (-(b : ZMod p)) ∈ tailResidues A N p := by
    have he := tailDensityMask_eq_tailResidues A N p hp
    simp only [Int.cast_neg, Int.cast_natCast] at hm
    exact he ▸ hm
  exact Set.disjoint_left.mp hdis hh ⟨b, ⟨hbB, by omega⟩, rfl⟩

theorem tailDensityMask_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    (N p : ℕ) [NeZero p] (hp : 0 < p)
    (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.univ \ tailDensityMask A N p).Nonempty := by
  obtain ⟨x, hx, hlarge⟩ := hB.exists_gt (N + p)
  refine ⟨-(x : ZMod p), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro hm
  have hh : -(x : ZMod p) ∈ tailResidues A N p :=
    (tailDensityMask_eq_tailResidues A N p hp) ▸ hm
  exact Set.disjoint_left.mp hdis hh ⟨x, ⟨hx, hlarge⟩, rfl⟩

theorem tailDensityMask_card_lt {A B : Set ℕ} (hB : B.Infinite)
    (N p : ℕ) [NeZero p] (hp : 0 < p)
    (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (tailDensityMask A N p).card < p := by
  have ht := Finset.card_pos.mpr (tailDensityMask_complement_nonempty hB N p hp hdis)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card] at ht
  omega

theorem tailDensityMask_ratio {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) (hp : 0 < p) :
    (p : ℝ) / (tailDensityMask A N p).card - 1 =
      ((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card := by
  rw [tailDensityMask_card]
  have hs : (tailSupport A N p).card ≠ 0 :=
    (Finset.card_pos.mpr (tailSupport_nonempty hA N p hp)).ne'
  have hsum := tailSupport_card_add_complement A N p
  have hsum' : ((tailSupport A N p).card : ℝ) +
      (Finset.range p \ tailSupport A N p).card = p := by exact_mod_cast hsum
  apply (eq_div_iff (by exact_mod_cast hs)).mpr
  field_simp
  linarith

end Ostmann

end OAI
