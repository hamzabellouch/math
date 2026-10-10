import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TopologyTreeSteps
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecPrimeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TaggedShape
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Enum
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexIndex

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

def taggedShapeMap {w v : ClosedLine h ℓ} (H : SameGeometry v w) : TaggedShape v → TaggedShape w
  | .inl Q => .inl (H.shapeMap Q)
  | .inr e => .inr e

lemma taggedShapeMap_code {w v : ClosedLine h ℓ} (H : SameGeometry v w) (s : TaggedShape v) :
    taggedShapeCode w (taggedShapeMap H s)=taggedShapeCode v s := by
  cases s <;> rfl

lemma taggedShapeMap_weight {w v : ClosedLine h ℓ} (H : SameGeometry v w) (p : S.Index)
    (s : TaggedShape v) :
    localTokenWeight w p (taggedShapeCode w (taggedShapeMap H s)) =
      localTokenWeight v p (taggedShapeCode v s) := by
  cases s with
  | inl Q => exact (H.weight p Q.edges.val).symm
  | inr e => rfl

lemma taggedShapeMap_surjective {w v : ClosedLine h ℓ} (H : SameGeometry v w) :
    Function.Surjective (taggedShapeMap H) := by
  intro t
  cases t with
  | inl Q =>
    obtain ⟨R,hR⟩ := H.shapeEquiv.surjective Q
    exact ⟨.inl R,congrArg Sum.inl hR⟩
  | inr e => exact ⟨.inr e,rfl⟩

noncomputable def taggedPairSet {w v : ClosedLine h ℓ} (_H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) : Finset (S.Index × TaggedShape w) :=
  univ.filter (fun z => taggedShapeCode w z.2 ∈ taggedTokens v hh 𝔏 (recordAt v hh 𝔏 a) z.1)

lemma mem_taggedPairSet {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (p : S.Index) (s : TaggedShape w) :
    (p,s) ∈ taggedPairSet H hh 𝔏 a ↔
      taggedShapeCode w s ∈ taggedTokens v hh 𝔏 (recordAt v hh 𝔏 a) p := by
  simp only [taggedPairSet,mem_filter,mem_univ,true_and]

lemma taggedToken_iff_pair {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (p : S.Index) (t : LocalToken ℓ) :
    t ∈ taggedTokens v hh 𝔏 (recordAt v hh 𝔏 a) p ↔
      ∃ s : TaggedShape w, (p,s) ∈ taggedPairSet H hh 𝔏 a ∧ taggedShapeCode w s=t := by
  constructor
  · intro ht
    obtain ⟨s,hs⟩ := record_tagged_shape v hh 𝔏 a p t ht
    refine ⟨taggedShapeMap H s,?_,?_⟩
    · rw [mem_taggedPairSet,taggedShapeMap_code,hs]
      exact ht
    · exact (taggedShapeMap_code H s).trans hs
  · rintro ⟨s,hs,rfl⟩
    exact (mem_taggedPairSet H hh 𝔏 a p s).mp hs

noncomputable def taggedRecordCode {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (N : ℕ) :
    Fin N → Option (S.Index × TaggedShape w) := FiniteSlotEncoding.code (taggedPairSet H hh 𝔏 a) N

theorem tag_tokens_eq_of_code {w v u : ClosedLine h ℓ}
    (H : SameGeometry v w) (I : SameGeometry u w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (𝔐 : List (AttachedSpec u D L))
    (a : S.FixedResidues v) (b : S.FixedResidues u) (N : ℕ)
    (hN : (taggedPairSet H hh 𝔏 a).card ≤ N) (hM : (taggedPairSet I hh 𝔐 b).card ≤ N)
    (hc : taggedRecordCode H hh 𝔏 a N=taggedRecordCode I hh 𝔐 b N) (p : S.Index) :
    taggedTokens v hh 𝔏 (recordAt v hh 𝔏 a) p=taggedTokens u hh 𝔐 (recordAt u hh 𝔐 b) p := by
  have hs := FiniteSlotEncoding.code_injective hN hM hc
  ext t
  rw [taggedToken_iff_pair H hh 𝔏 a p t,taggedToken_iff_pair I hh 𝔐 b p t,hs]

noncomputable def taggedPairEquiv {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) :
    ↥(taggedPairSet H hh 𝔏 a) ≃ TaggedSlot v hh 𝔏 a :=
  Equiv.ofBijective
    (fun z => ⟨z.val.1,⟨taggedShapeCode w z.val.2,(mem_taggedPairSet H hh 𝔏 a _ _).mp z.property⟩⟩)
    ⟨by
      intro x y he
      have hp : x.val.1=y.val.1 := congrArg Sigma.fst he
      have hT : taggedShapeCode w x.val.2=taggedShapeCode w y.val.2 :=
        congrArg (fun z : TaggedSlot v hh 𝔏 a => z.2.val) he
      exact Subtype.ext (Prod.ext hp (taggedShapeCode_injective w hT)),
    by
      rintro ⟨p,t⟩
      obtain ⟨s,hs,he⟩ := (taggedToken_iff_pair H hh 𝔏 a p t.val).mp t.property
      refine ⟨⟨(p,s),hs⟩,?_⟩
      exact congrArg (fun z => (Sigma.mk p z : TaggedSlot v hh 𝔏 a)) (Subtype.ext he)⟩

lemma taggedPairSet_card {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) :
    (taggedPairSet H hh 𝔏 a).card=Fintype.card (TaggedSlot v hh 𝔏 a) := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (taggedPairEquiv H hh 𝔏 a)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
