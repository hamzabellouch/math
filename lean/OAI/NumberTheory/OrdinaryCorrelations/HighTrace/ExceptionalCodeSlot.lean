import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AttachedMetadata
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TaggedShapeMap
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ProductCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PaddedWeightIdentity

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.TaggedPrimeGroups
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

abbrev ExceptionalCodeSlot (L J n N : ℕ) := Fin N ⊕ ListCodeSlot L J n

noncomputable def exceptionalPrimeCode {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (n N : ℕ) :
    ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N → Option S.Index
  | .inl i => (taggedRecordCode H hh 𝔏 a N i).map Prod.fst
  | .inr k => listPrimeCode v 𝔏 n k

noncomputable def exceptionalShapeCode {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (N : ℕ) :
    Fin N → Option (TaggedShape w) := fun i => (taggedRecordCode H hh 𝔏 a N i).map Prod.snd

lemma exceptionalCodeSlot_card (L J n N : ℕ) :
    Fintype.card (ExceptionalCodeSlot L J n N)=N+n*(L*J+1) := by
  simp only [ExceptionalCodeSlot,Fintype.card_sum,Fintype.card_fin,listCodeSlot_card]

theorem exceptionalPrimeCode_support {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (n N : ℕ)
    (hn : 𝔏.length ≤ n) (hN : (taggedPairSet H hh 𝔏 a).card ≤ N) (p : S.Index) :
    p ∈ exceptionalSupport v hh 𝔏 a ↔ ∃ k, exceptionalPrimeCode H hh 𝔏 a n N k=some p := by
  constructor
  · intro hp
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hp
    rcases k with ⟨p,t⟩ | k
    · obtain ⟨s,hs,he⟩ := (taggedToken_iff_pair H hh 𝔏 a p t.val).mp t.property
      obtain ⟨i,hi⟩ := (FiniteSlotEncoding.mem_iff_code (taggedPairSet H hh 𝔏 a) N hN (p,s)).mp hs
      exact ⟨.inl i,by simp only [exceptionalPrimeCode,taggedRecordCode,hi,Option.map_some,exceptionalPrime]⟩
    · obtain ⟨i,hi⟩ := (listPrimeCode_support v 𝔏 n hn (listSlotPrime v 𝔏 k)).mp
        ((listSupport_iff_slot v 𝔏 _).mpr ⟨k,rfl⟩)
      exact ⟨.inr i,hi⟩
  · rintro ⟨(i | k),hk⟩
    · obtain ⟨⟨q,s⟩,hi,hp⟩ := Option.map_eq_some_iff.mp hk
      dsimp only at hp
      subst q
      have hs := FiniteSlotEncoding.code_mem (taggedPairSet H hh 𝔏 a) N i (p,s) hi
      have ht := (mem_taggedPairSet H hh 𝔏 a p s).mp hs
      exact mem_image.mpr ⟨.inl ⟨p,⟨taggedShapeCode w s,ht⟩⟩,mem_univ _,rfl⟩
    · obtain ⟨i,hi⟩ := (listSupport_iff_slot v 𝔏 p).mp
        ((listPrimeCode_support v 𝔏 n hn p).mpr ⟨k,hk⟩)
      exact mem_image.mpr ⟨.inr i,mem_univ _,hi⟩

lemma localTokenWeight_sameGeometry {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (p : S.Index) (t : LocalToken ℓ) : localTokenWeight v p t=localTokenWeight w p t := by
  simp only [localTokenWeight,H.weight,H.modifiedWeight]

theorem exceptionalShapeCode_product {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (N : ℕ)
    (hN : (taggedPairSet H hh 𝔏 a).card ≤ N) :
    (∏ i : Fin N, paddedShapeWeight (fun p s => localTokenWeight w p (taggedShapeCode w s))
      ((taggedRecordCode H hh 𝔏 a N i).map Prod.fst) (exceptionalShapeCode H hh 𝔏 a N i))=
      ∏ s : TaggedSlot v hh 𝔏 a, localTokenWeight v s.1 s.2.val := by
  simp only [exceptionalShapeCode,padded_same_pair,taggedRecordCode]
  rw [FiniteSlotEncoding.product_code _ _ hN]
  rw [← prod_coe_sort]
  calc
    _ = ∏ z : ↥(taggedPairSet H hh 𝔏 a),
        localTokenWeight v z.val.1 (taggedShapeCode w z.val.2) := by
      apply prod_congr rfl
      intro z hz
      exact (localTokenWeight_sameGeometry H _ _).symm
    _ = _ := (taggedPairEquiv H hh 𝔏 a).prod_comp
      (fun s : TaggedSlot v hh 𝔏 a => localTokenWeight v s.1 s.2.val)

noncomputable def exceptionalTuple {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (n N : ℕ) :
    Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index :=
  fun i => exceptionalPrimeCode H hh 𝔏 a n N ((Fintype.equivFin _).symm i)

noncomputable def exceptionalPick (L J n N : ℕ) (i : Fin N) :
    Fin (Fintype.card (ExceptionalCodeSlot L J n N)) := (Fintype.equivFin _) (.inl i)

lemma exceptionalTuple_pick {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (n N : ℕ) (i : Fin N) :
    exceptionalTuple H hh 𝔏 a n N (exceptionalPick L ⌈C₀*Real.log B⌉₊ n N i) =
      (taggedRecordCode H hh 𝔏 a N i).map Prod.fst := by
  simp only [exceptionalTuple,exceptionalPick,Equiv.symm_apply_apply,exceptionalPrimeCode]

lemma exceptionalTuple_support {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (n N : ℕ)
    (hn : 𝔏.length ≤ n) (hN : (taggedPairSet H hh 𝔏 a).card ≤ N) (p : S.Index) :
    (∃ i, exceptionalTuple H hh 𝔏 a n N i=some p) ↔ p ∈ exceptionalSupport v hh 𝔏 a := by
  rw [exceptionalPrimeCode_support H hh 𝔏 a n N hn hN p]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨(Fintype.equivFin _).symm i,hi⟩
  · rintro ⟨k,hk⟩
    refine ⟨Fintype.equivFin _ k,?_⟩
    simpa only [exceptionalTuple,Equiv.symm_apply_apply] using hk

theorem exceptionalCode_weight {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (n N : ℕ)
    (hn : 𝔏.length ≤ n) (hN : (taggedPairSet H hh 𝔏 a).card ≤ N) :
    (∏ p : S.Index, taggedGroupFactor v hh 𝔏 a p) =
      weight (paddedGroupWeight (fun p : S.Index => (p:ℝ)⁻¹)) (exceptionalTuple H hh 𝔏 a n N) *
        ∏ i : Fin N, paddedShapeWeight (fun p s => localTokenWeight w p (taggedShapeCode w s))
          (exceptionalTuple H hh 𝔏 a n N (exceptionalPick L ⌈C₀*Real.log B⌉₊ n N i))
          (exceptionalShapeCode H hh 𝔏 a N i) := by
  simp_rw [exceptionalTuple_pick]
  rw [exceptionalShapeCode_product H hh 𝔏 a N hN,tagged_product_slots,padded_weight_identity]
  simp_rw [exceptionalTuple_support H hh 𝔏 a n N hn hN]
  congr 1
  rw [← prod_filter]
  simp only [filter_mem_eq_inter,univ_inter]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
