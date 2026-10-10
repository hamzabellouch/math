import OAI.NumberTheory.Jacobsthal.Partitions.SourceBlockFibreBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosLargeHeightBlocks ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def actualBlockIndex (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (p : goodPrimes (primeBin R theta) H) :
    Fin (blockCount C0 R theta H) :=
  Classical.choose (unique_original_prime_block C0 R theta H p.val hR htheta
    (Finset.mem_filter.mp p.property).1).exists

theorem actualBlockIndex_mem (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (p : goodPrimes (primeBin R theta) H) :
    p.val ∈ blockPrimes C0 R theta H (actualBlockIndex R theta H C0 hR htheta p) :=
  Classical.choose_spec (unique_original_prime_block C0 R theta H p.val hR htheta
    (Finset.mem_filter.mp p.property).1).exists

theorem actualBlockIndex_eq_iff (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (p : goodPrimes (primeBin R theta) H)
    (i : Fin (blockCount C0 R theta H)) :
    actualBlockIndex R theta H C0 hR htheta p = i ↔ p.val ∈ blockPrimes C0 R theta H i := by
  constructor
  · intro he
    rw [← he]
    exact actualBlockIndex_mem R theta H C0 hR htheta p
  · intro hi
    exact (unique_original_prime_block C0 R theta H p.val hR htheta
      (Finset.mem_filter.mp p.property).1).unique (actualBlockIndex_mem R theta H C0 hR htheta p) hi

noncomputable def indexedFullPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) : Finset (goodPrimes P H) :=
  Finset.univ.filter (fun p => E (actualFullPattern P w H C0 hw hP hlarge p))

noncomputable def fullPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) : Finset ℕ :=
  (indexedFullPrimeEvent P w H C0 hw hP hlarge E).image Subtype.val

theorem fullPrimeEvent_card (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    (fullPrimeEvent P w H C0 hw hP hlarge E).card = (indexedFullPrimeEvent P w H C0 hw hP hlarge E).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem fullPrimeEvent_card_fibres (R theta w : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (hw : 0 ≤ w)
    (hP : ∀ p ∈ primeBin R theta,p.Prime) (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    (fullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E).card =
      ∑ i : Fin (blockCount C0 R theta H),∑ v ∈ Finset.univ.filter E,
        (blockPatternPrimes R theta w H C0 hw hP hlarge i v).card := by
  let f (p : goodPrimes (primeBin R theta) H) :=
    (actualBlockIndex R theta H C0 hR htheta p,actualFullPattern (primeBin R theta) w H C0 hw hP hlarge p)
  let S : Finset (Fin (blockCount C0 R theta H) × ErdosLargePatternLaw.FullPattern w H) :=
    Finset.univ.product (Finset.univ.filter E)
  have hmaps : (indexedFullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E : Set _).MapsTo f (S : Set _) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩⟩
  rw [fullPrimeEvent_card,Finset.card_eq_sum_card_fiberwise hmaps]
  simp only [S,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext p
  simp only [indexedFullPrimeEvent,blockPatternPrimes,Finset.mem_filter,Finset.mem_univ,true_and,f,Prod.mk.injEq,
    actualBlockIndex_eq_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.2.symm ▸ (Finset.mem_filter.mp hv).2,h⟩

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
