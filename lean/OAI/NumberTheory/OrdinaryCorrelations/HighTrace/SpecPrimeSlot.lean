import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ModifiedWeightSameBand

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

abbrev SpecPrimeSlot (s : S.Specification D h L) :=
  Option ((i : Fin s.length) × {p : ℕ // p ∈ (s.label i).primeFactors})

def specSlotPrime (s : S.Specification D h L) : SpecPrimeSlot s → S.Index
  | none => s.extra
  | some ⟨i,p⟩ => ⟨p.val,D.support _ (s.label_mem i) p.property⟩

lemma specSupport_iff_slot (s : S.Specification D h L) (p : S.Index) :
    (p : ℕ) ∈ s.primeSupport ↔ ∃ k : SpecPrimeSlot s, specSlotPrime s k=p := by
  constructor
  · intro hp
    rcases mem_insert.mp hp with hp | hp
    · exact ⟨none,Subtype.ext hp.symm⟩
    · obtain ⟨i,_,hp⟩ := mem_biUnion.mp hp
      exact ⟨some ⟨i,⟨p.val,hp⟩⟩,Subtype.ext rfl⟩
  · rintro ⟨k,hk⟩
    rcases k with _ | ⟨i,q⟩
    · change s.extra=p at hk
      rw [← hk]
      exact mem_insert_self _ _
    · have hq : q.val=p.val := congrArg Subtype.val hk
      exact mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ _,hq ▸ q.property⟩)

lemma specPrimeSlot_card (s : S.Specification D h L) :
    Fintype.card (SpecPrimeSlot s) ≤ L * ⌈C₀*Real.log B⌉₊ + 1 := by
  change Fintype.card (Option _) ≤ _
  rw [Fintype.card_option,Fintype.card_sigma]
  have hs : (∑ i : Fin s.length, Fintype.card {p : ℕ // p ∈ (s.label i).primeFactors}) ≤
      s.length * ⌈C₀*Real.log B⌉₊ := by
    calc
      _ ≤ ∑ _i : Fin s.length, ⌈C₀*Real.log B⌉₊ := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Fintype.card_coe] using D.omega _ (s.label_mem i)
      _ = _ := by simp
  have hlen := Nat.mul_le_mul_right ⌈C₀*Real.log B⌉₊ s.length_le
  omega

abbrev ListPrimeSlot (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :=
  (i : Fin 𝔏.length) × SpecPrimeSlot (𝔏.get i).spec

def listSlotPrime (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (s : ListPrimeSlot w 𝔏) : S.Index := specSlotPrime (𝔏.get s.1).spec s.2

lemma listSupport_iff_slot (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (p : S.Index) :
    (p : ℕ) ∈ listSupport w 𝔏 ↔ ∃ s : ListPrimeSlot w 𝔏, listSlotPrime w 𝔏 s=p := by
  constructor
  · intro hp
    obtain ⟨s,hs,hp⟩ := mem_biUnion.mp hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hs)
    obtain ⟨k,hk⟩ := (specSupport_iff_slot (𝔏.get i).spec p).mp hp
    exact ⟨⟨i,k⟩,hk⟩
  · rintro ⟨⟨i,k⟩,hk⟩
    exact mem_biUnion.mpr ⟨𝔏.get i,List.mem_toFinset.mpr (List.get_mem _ _),
      (specSupport_iff_slot (𝔏.get i).spec p).mpr ⟨k,hk⟩⟩

lemma listPrimeSlot_card (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    Fintype.card (ListPrimeSlot w 𝔏) ≤ 𝔏.length * (L * ⌈C₀*Real.log B⌉₊ + 1) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Fin 𝔏.length, (L * ⌈C₀*Real.log B⌉₊ + 1) :=
      Finset.sum_le_sum (fun i _ => specPrimeSlot_card (𝔏.get i).spec)
    _ = _ := by simp

abbrev TaggedSlot (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) :=
  (p : S.Index) × {t : LocalToken ℓ // t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p}

abbrev ExceptionalSlot (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) :=
  TaggedSlot w hh 𝔏 a ⊕ ListPrimeSlot w 𝔏

noncomputable def exceptionalPrime (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) : ExceptionalSlot w hh 𝔏 a → S.Index
  | .inl ⟨p,_t⟩ => p
  | .inr k => listSlotPrime w 𝔏 k

noncomputable def exceptionalSupport (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) : Finset S.Index :=
  univ.image (exceptionalPrime w hh 𝔏 a)

lemma recordTokens_nonempty (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : (treeOccurrences w p).Nonempty) :
    (recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).Nonempty := by
  obtain ⟨e,he⟩ := hp
  rw [← recordTokens_cover w hh 𝔏 a p] at he
  obtain ⟨t,ht,_⟩ := mem_biUnion.mp he
  exact ⟨t,ht⟩

lemma tagged_implies_used_none (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : LocalToken ℓ) (ht : t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p) :
    UsedPrime w 𝔏 p ∧ untaggedType w hh 𝔏 a p=none := by
  constructor
  · apply Or.inl
    by_contra hn
    have hm := (mem_filter.mp ht).1
    simp only [recordTokens,hn,ite_false,Finset.notMem_empty] at hm
  · rcases he : untaggedType w hh 𝔏 a p with _ | u
    · rfl
    · rw [taggedTokens_of_some w hh 𝔏 a p u he] at ht
      exact (Finset.notMem_empty _ ht).elim

lemma list_implies_untagged_none (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : (p : ℕ) ∈ listSupport w 𝔏) : untaggedType w hh 𝔏 a p=none := by
  rcases he : untaggedType w hh 𝔏 a p with _ | u
  · rfl
  · have ht : (false,false,u.2.edges.val) ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p := by
      rw [(untaggedType_some w hh 𝔏 a p u he).2]
      exact mem_singleton_self _
    exact (record_untagged_not_in_list w hh 𝔏 a p _ ht rfl hp).elim

theorem mem_exceptionalSupport (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    p ∈ exceptionalSupport w hh 𝔏 a ↔ UsedPrime w 𝔏 p ∧ untaggedType w hh 𝔏 a p=none := by
  constructor
  · intro hp
    obtain ⟨k,_,rfl⟩ := mem_image.mp hp
    rcases k with ⟨p,t⟩ | k
    · exact tagged_implies_used_none w hh 𝔏 a p t.val t.property
    · have hlist := (listSupport_iff_slot w 𝔏 (listSlotPrime w 𝔏 k)).mpr ⟨k,rfl⟩
      exact ⟨Or.inr hlist,list_implies_untagged_none w hh 𝔏 a _ hlist⟩
  · rintro ⟨(htree | hlist),hu⟩
    · obtain ⟨t,ht⟩ := recordTokens_nonempty w hh 𝔏 a p htree
      have hm : t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p :=
        (taggedTokens_of_none w hh 𝔏 a p hu).symm ▸ ht
      exact mem_image.mpr ⟨.inl ⟨p,⟨t,hm⟩⟩,mem_univ _,rfl⟩
    · obtain ⟨k,hk⟩ := (listSupport_iff_slot w 𝔏 p).mp hlist
      exact mem_image.mpr ⟨.inr k,mem_univ _,hk⟩

lemma taggedGroupFactor_exact (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    taggedGroupFactor w hh 𝔏 a p =
      (if p ∈ exceptionalSupport w hh 𝔏 a then (p : ℝ)⁻¹ else 1) *
        ∏ t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p, localTokenWeight w p t := by
  unfold taggedGroupFactor
  rcases he : untaggedType w hh 𝔏 a p with _ | u
  · simp only [he,ite_true,mem_exceptionalSupport,and_true]
  · rw [taggedTokens_of_some w hh 𝔏 a p u he]
    simp only [he,Option.some_ne_none,ite_false,mem_exceptionalSupport,and_false,prod_empty,mul_one]

theorem tagged_product_slots (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) :
    (∏ p : S.Index, taggedGroupFactor w hh 𝔏 a p) =
    (∏ p ∈ exceptionalSupport w hh 𝔏 a, (p : ℝ)⁻¹) *
      ∏ s : TaggedSlot w hh 𝔏 a, localTokenWeight w s.1 s.2.val := by
  simp_rw [taggedGroupFactor_exact]
  rw [prod_mul_distrib,Fintype.prod_sigma]
  congr 1
  · rw [← prod_filter]
    congr 1
    exact filter_mem_eq_inter.trans (univ_inter _)
  · apply Finset.prod_congr rfl
    intro p _
    exact (prod_coe_sort _ (localTokenWeight w p)).symm

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
