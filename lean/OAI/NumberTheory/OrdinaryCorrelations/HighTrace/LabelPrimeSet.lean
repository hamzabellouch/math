import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BitWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Enum

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

def labelPrimeSet (d : ℕ) (hd : d ∈ D.members) : Finset S.Index :=
  d.primeFactors.attach.image (fun p => ⟨p.val,D.support d hd p.property⟩)

lemma mem_labelPrimeSet (d : ℕ) (hd : d ∈ D.members) (p : S.Index) :
    p ∈ labelPrimeSet d hd ↔ p.val ∈ d.primeFactors := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := mem_image.mp hp
    exact congrArg Subtype.val hqp ▸ q.property
  · intro hp
    exact mem_image.mpr ⟨⟨p.val,hp⟩,mem_attach _ _,Subtype.ext rfl⟩

lemma labelPrimeSet_card (d : ℕ) (hd : d ∈ D.members) :
    (labelPrimeSet d hd).card = d.primeFactors.card := by
  rw [labelPrimeSet,card_image_of_injective]
  · exact card_attach
  · intro p q he
    exact Subtype.ext (congrArg (fun z : S.Index => z.val) he)

lemma labelPrimeSet_product (d : ℕ) (hd : d ∈ D.members) :
    (∏ p ∈ labelPrimeSet d hd, p.val)=d := by
  rw [labelPrimeSet,prod_image]
  · change (∏ p ∈ d.primeFactors.attach, p.val)=d
    rw [Finset.prod_attach d.primeFactors (fun p : ℕ => p)]
    exact Nat.prod_primeFactors_of_squarefree (D.squarefree d hd)
  · intro p hp q hq he
    exact Subtype.ext (congrArg (fun z : S.Index => z.val) he)

abbrev SpecMetadata (L : ℕ) := Fin (L+1) × (Fin L → Bool) × Fin (L+1)
abbrev SpecCodeSlot (L J : ℕ) := Option (Fin L × Fin J)

def specMetadata (s : S.Specification D h L) : SpecMetadata L :=
  (⟨s.length,Nat.lt_succ_of_le s.length_le⟩,
   (fun i => if hi : i.val < s.length then decide (s.sign ⟨i.val,hi⟩=1) else false),
   ⟨s.suffix.val,by have := s.suffix.isLt; have := s.length_le; omega⟩)

noncomputable def specPrimeCode (s : S.Specification D h L) :
    SpecCodeSlot L ⌈C₀*Real.log B⌉₊ → Option S.Index
  | none => some s.extra
  | some (i,j) => if hi : i.val < s.length then
      FiniteSlotEncoding.code (labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _))
        ⌈C₀*Real.log B⌉₊ j else none

lemma specPrimeCode_support (s : S.Specification D h L) (p : S.Index) :
    p.val ∈ s.primeSupport ↔ ∃ k, specPrimeCode s k=some p := by
  constructor
  · intro hp
    rcases mem_insert.mp hp with hp | hp
    · exact ⟨none,congrArg some (Subtype.ext hp.symm)⟩
    · obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
      have hc : (labelPrimeSet (s.label i) (s.label_mem i)).card ≤ ⌈C₀*Real.log B⌉₊ := by
        rw [labelPrimeSet_card]
        exact D.omega _ (s.label_mem i)
      obtain ⟨j,hj⟩ := (FiniteSlotEncoding.mem_iff_code _ _ hc p).mp ((mem_labelPrimeSet _ _ p).mpr hp)
      let i' : Fin L := ⟨i.val,lt_of_lt_of_le i.isLt s.length_le⟩
      exact ⟨some (i',j),by simpa only [specPrimeCode,i',dite_eq_left i.isLt] using hj⟩
  · rintro ⟨k,hk⟩
    rcases k with _ | ⟨i,j⟩
    · have he : s.extra=p := Option.some.inj hk
      exact mem_insert.mpr (Or.inl (congrArg (fun z : S.Index => z.val) he).symm)
    · dsimp only [specPrimeCode] at hk
      split_ifs at hk with hi
      · have hp := FiniteSlotEncoding.code_mem _ _ j p hk
        exact mem_insert_of_mem (mem_biUnion.mpr ⟨⟨i.val,hi⟩,mem_univ _,
          (mem_labelPrimeSet _ _ p).mp hp⟩)

def Specification.data (s : S.Specification D h L) :
    (n : ℕ) × ((Fin n → ℕ) × (Fin n → ℤ) × S.Index × Fin n) :=
  ⟨s.length,s.label,s.sign,s.extra,s.suffix⟩

lemma Specification.data_injective : Function.Injective (Specification.data (D := D) (h := h) (L := L)) := by
  intro s t he
  cases s with
  | mk sl slp sll so soz soi sd sdm ss ssm sstep sp spnd su spdiv =>
    cases t with
    | mk tl tlp tll tOff toz toi td tdm ts tsm tstep tp tpnd tu tpdiv =>
      dsimp only [Specification.data] at he
      obtain ⟨hlen,he⟩ := Sigma.mk.inj_iff.mp he
      subst tl
      have heq := eq_of_heq he
      have hlabel : sd=td := congrArg Prod.fst heq
      have hsign : ss=ts := congrArg (fun x => x.2.1) heq
      have hextra : sp=tp := congrArg (fun x => x.2.2.1) heq
      have hsuffix : su=tu := congrArg (fun x => x.2.2.2) heq
      subst td; subst ts; subst tp; subst tu
      have hoff : so=tOff := by
        funext i
        induction i using Fin.induction with
        | zero => exact soz.trans toz.symm
        | succ i ih => linarith only [sstep i,tstep i,ih]
      subst tOff
      rfl

theorem specification_code_injective (s t : S.Specification D h L)
    (hm : specMetadata s=specMetadata t) (hp : specPrimeCode s=specPrimeCode t) : s=t := by
  apply Specification.data_injective
  have hlen : s.length=t.length := congrArg (fun m : SpecMetadata L => m.1.val) hm
  cases s with
  | mk sl slp sll so soz soi sd sdm ss ssm sstep sp spnd su spdiv =>
    cases t with
    | mk tl tlp tll tOff toz toi td tdm ts tsm tstep tp tpnd tu tpdiv =>
      dsimp only at hlen
      subst tl
      have hsuffix : su=tu := Fin.ext (congrArg (fun m : SpecMetadata L => m.2.2.val) hm)
      have hextra : sp=tp := Option.some.inj (congrFun hp none)
      have hlabel : sd=td := by
        funext i
        let i' : Fin L := ⟨i.val,lt_of_lt_of_le i.isLt sll⟩
        have hc : FiniteSlotEncoding.code (labelPrimeSet (sd i) (sdm i)) ⌈C₀*Real.log B⌉₊ =
            FiniteSlotEncoding.code (labelPrimeSet (td i) (tdm i)) ⌈C₀*Real.log B⌉₊ := by
          funext j
          simpa only [specPrimeCode,i',dite_eq_left i.isLt] using congrFun hp (some (i',j))
        have hsets := FiniteSlotEncoding.code_injective
          (by rw [labelPrimeSet_card]; exact D.omega _ (sdm i))
          (by rw [labelPrimeSet_card]; exact D.omega _ (tdm i)) hc
        rw [← labelPrimeSet_product (sd i) (sdm i),← labelPrimeSet_product (td i) (tdm i),hsets]
      have hsign : ss=ts := by
        funext i
        let i' : Fin L := ⟨i.val,lt_of_lt_of_le i.isLt sll⟩
        have he := congrArg (fun m : SpecMetadata L => m.2.1 i') hm
        simp only [specMetadata,i',dite_eq_left i.isLt] at he
        rcases ssm i with hs | hs <;> rcases tsm i with ht | ht <;> simp_all
      simp only [Specification.data,hlabel,hsign,hextra,hsuffix]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
