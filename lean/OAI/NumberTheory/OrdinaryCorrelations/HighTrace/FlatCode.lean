import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalCodeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TaggedEdgeProduct

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

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

abbrev FlatCode (S : PrimeSystem) (w₀ : ClosedLine h ℓ) (C₀ B : ℝ) (L n N : ℕ) :=
  ListMetadata ℓ L n ×
    (Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index) ×
    (Fin N → Option (TaggedShape w₀)) ×
    (S.Index → Option (TokenType w₀))

noncomputable def flatCode (x : RecordPacket D L w₀ hh r hr₀ n N) : FlatCode S w₀ C₀ B L n N :=
  (listMetadata x.line x.primitives n x.length_le,
   exceptionalTuple x.geometry hh x.primitives x.residues n N,
   exceptionalShapeCode x.geometry hh x.primitives x.residues N,
   untaggedReference x.geometry hh x.primitives x.residues)

lemma tagCount (x : RecordPacket D L w₀ hh r hr₀ n N) :
    (taggedPairSet x.geometry hh x.primitives x.residues).card ≤ N := by
  rw [taggedPairSet_card]
  exact x.residues_count

theorem flatCode_injective : Function.Injective
    (flatCode : RecordPacket D L w₀ hh r hr₀ n N → FlatCode S w₀ C₀ B L n N) := by
  intro x y he
  apply code_injective
  have hp := congrArg (fun c : FlatCode S w₀ C₀ B L n N => c.2.1) he
  have hs := congrArg (fun c : FlatCode S w₀ C₀ B L n N => c.2.2.1) he
  refine Prod.ext ?_ ?_
  · exact congrArg (fun c : FlatCode S w₀ C₀ B L n N => c.1) he
  · apply Prod.ext
    · funext k
      have hk := congrFun hp (Fintype.equivFin (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N) (.inr k))
      simpa only [flatCode,exceptionalTuple,Equiv.symm_apply_apply,exceptionalPrimeCode,code] using hk
    · apply Prod.ext
      · funext i
        have hi := congrFun hp (exceptionalPick L ⌈C₀*Real.log B⌉₊ n N i)
        dsimp only [flatCode] at hi
        rw [exceptionalTuple_pick,exceptionalTuple_pick] at hi
        have hj := congrFun hs i
        dsimp only [flatCode,exceptionalShapeCode] at hj
        change taggedRecordCode x.geometry hh x.primitives x.residues N i =
          taggedRecordCode y.geometry hh y.primitives y.residues N i
        rcases hx : taggedRecordCode x.geometry hh x.primitives x.residues N i with _ | ⟨p,s⟩ <;>
          rcases hy : taggedRecordCode y.geometry hh y.primitives y.residues N i with _ | ⟨q,t⟩
        · rfl
        · simp [hx,hy] at hi
        · simp [hx,hy] at hi
        · simp only [hx,hy,Option.map_some,Option.some.injEq] at hi hj
          exact congrArg some (Prod.ext hi hj)
      · exact congrArg (fun c : FlatCode S w₀ C₀ B L n N => c.2.2.2) he

noncomputable def flatTagged (c : FlatCode S w₀ C₀ B L n N) (i : Fin N) :
    Option (S.Index × TaggedShape w₀) :=
  (c.2.1 (exceptionalPick L ⌈C₀*Real.log B⌉₊ n N i)).bind
    (fun p => (c.2.2.1 i).map (fun s => (p,s)))

lemma flatTagged_code (x : RecordPacket D L w₀ hh r hr₀ n N) :
    flatTagged x.flatCode=taggedRecordCode x.geometry hh x.primitives x.residues N := by
  funext i
  simp only [flatTagged,flatCode,exceptionalTuple_pick,exceptionalShapeCode]
  cases taggedRecordCode x.geometry hh x.primitives x.residues N i <;> rfl

noncomputable def flatEdge (c : FlatCode S w₀ C₀ B L n N) (e : Fin ℓ) : ℝ :=
  ∏ p : S.Index, if ∃ i s, flatTagged c i=some (p,s) ∧ e ∈ tokenEdges (taggedShapeCode w₀ s)
    then (p : ℝ) else 1

lemma flatEdge_pos (c : FlatCode S w₀ C₀ B L n N) (e : Fin ℓ) : 0 < flatEdge c e := by
  apply prod_pos
  intro p hp
  split_ifs
  · exact_mod_cast (S.prime_mem _ p.property).pos
  · norm_num

lemma flatEdge_code (x : RecordPacket D L w₀ hh r hr₀ n N) :
    flatEdge x.flatCode=taggedEdgeProduct x.line hh x.primitives x.residues := by
  funext e
  unfold flatEdge taggedEdgeProduct
  simp_rw [flatTagged_code]
  apply prod_congr rfl
  intro p hp
  congr 1
  apply propext
  constructor
  · rintro ⟨i,s,hi,he⟩
    have hs := FiniteSlotEncoding.code_mem
      (taggedPairSet x.geometry hh x.primitives x.residues) N i (p,s) hi
    exact mem_biUnion.mpr ⟨taggedShapeCode w₀ s,
      (mem_taggedPairSet x.geometry hh x.primitives x.residues p s).mp hs,he⟩
  · rintro hE
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp hE
    obtain ⟨s,hs,hst⟩ := (taggedToken_iff_pair x.geometry hh x.primitives x.residues p t).mp ht
    obtain ⟨i,hi⟩ := (FiniteSlotEncoding.mem_iff_code
      (taggedPairSet x.geometry hh x.primitives x.residues) N x.tagCount (p,s)).mp hs
    exact ⟨i,s,hi,hst ▸ he⟩

noncomputable def flatGate (H τ : ℝ) (c : FlatCode S w₀ C₀ B L n N) : Prop :=
  unorderedBins (TypeFibers.multiplicity c.2.2.2) (flatEdge c) H τ (TypeFibers.unordered c.2.2.2)

lemma flatCode_gate (x : RecordPacket D L w₀ hh r hr₀ n N) : flatGate D.H τ x.flatCode := by
  unfold flatGate
  rw [flatEdge_code]
  exact record_unordered_bins x.geometry hh x.primitives x.residues x.labels

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
