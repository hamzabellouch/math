import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UntaggedEdgeCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AttachedMetadata
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TaggedShapeMap

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

structure RecordPacket (D : S.DivisorFamily B τ C₀) (L : ℕ)
    (w₀ : ClosedLine h ℓ) (hh : 0 < h) (r : ℕ)
    (hr₀ : (returnSteps w₀).card=r) (n N : ℕ) where
  line : ClosedLine h ℓ
  labels : ∀ i, line.label i ∈ D.members
  returns : (returnSteps line).card=r
  topology : encodeTopology line r returns=encodeTopology w₀ r hr₀
  primitives : List (AttachedSpec line D L)
  length_le : primitives.length ≤ n
  record : AssignedRecord S ℓ
  realized : ∃ a : S.FixedResidues line,
    recordAt line hh primitives a=record ∧ Fintype.card (TaggedSlot line hh primitives a) ≤ N

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

noncomputable def residues (x : RecordPacket D L w₀ hh r hr₀ n N) : S.FixedResidues x.line :=
  x.realized.choose

lemma realized_residues (x : RecordPacket D L w₀ hh r hr₀ n N) :
    recordAt x.line hh x.primitives x.residues=x.record := x.realized.choose_spec.1

lemma residues_count (x : RecordPacket D L w₀ hh r hr₀ n N) :
    Fintype.card (TaggedSlot x.line hh x.primitives x.residues) ≤ N := x.realized.choose_spec.2

lemma geometry (x : RecordPacket D L w₀ hh r hr₀ n N) : SameGeometry x.line w₀ :=
  sameGeometry_of_topology x.returns hr₀ x.topology

abbrev Code (S : PrimeSystem) (w₀ : ClosedLine h ℓ) (C₀ B : ℝ) (L n N : ℕ) :=
  ListMetadata ℓ L n ×
    (ListCodeSlot L ⌈C₀*Real.log B⌉₊ n → Option S.Index) ×
    (Fin N → Option (S.Index × TaggedShape w₀)) ×
    (S.Index → Option (TokenType w₀))

noncomputable def code (x : RecordPacket D L w₀ hh r hr₀ n N) : Code S w₀ C₀ B L n N :=
  (listMetadata x.line x.primitives n x.length_le,
   listPrimeCode x.line x.primitives n,
   taggedRecordCode x.geometry hh x.primitives x.residues N,
   untaggedReference x.geometry hh x.primitives x.residues)

theorem code_injective : Function.Injective
    (code : RecordPacket D L w₀ hh r hr₀ n N → Code S w₀ C₀ B L n N) := by
  intro x y hc
  have hmeta := congrArg (fun c : Code S w₀ C₀ B L n N => c.1) hc
  have hprime := congrArg (fun c : Code S w₀ C₀ B L n N => c.2.1) hc
  have htag := congrArg (fun c : Code S w₀ C₀ B L n N => c.2.2.1) hc
  have hunt := congrArg (fun c : Code S w₀ C₀ B L n N => c.2.2.2) hc
  have hT (p : S.Index) :
      taggedTokens x.line hh x.primitives (recordAt x.line hh x.primitives x.residues) p =
      taggedTokens y.line hh y.primitives (recordAt y.line hh y.primitives y.residues) p := by
    apply tag_tokens_eq_of_code x.geometry y.geometry hh x.primitives y.primitives
      x.residues y.residues N _ _ htag p
    · rw [taggedPairSet_card]
      exact x.residues_count
    · rw [taggedPairSet_card]
      exact y.residues_count
  have hU : untaggedEdgeCode x.line hh x.primitives x.residues =
      untaggedEdgeCode y.line hh y.primitives y.residues := by
    funext p
    rw [← untaggedReference_edges x.geometry,← untaggedReference_edges y.geometry]
    exact congrArg (fun f : S.Index → Option (TokenType w₀) =>
      (f p).map (fun t => (t.1,t.2.edges.val))) hunt
  have hline : x.line=y.line := line_eq_of_record_codes x.line y.line hh x.labels y.labels r
    x.returns y.returns (x.topology.trans y.topology.symm) x.primitives y.primitives
    x.residues y.residues hT hU
  cases x with
  | mk v hv hrv htv 𝔏 h𝔏 R hR =>
    cases y with
    | mk u hu hru htu 𝔐 h𝔐 T hS =>
      dsimp only at hline
      subst u
      have hlist : 𝔏=𝔐 := list_code_injective v 𝔏 𝔐 n h𝔏 h𝔐 hmeta hprime
      subst 𝔐
      have hrecs : R=T := by
        rw [← hR.choose_spec.1,← hS.choose_spec.1]
        apply recordTokens_injective_on_records v hh 𝔏 hR.choose hS.choose
        intro p
        exact tokens_eq_of_codes v v hh 𝔏 𝔏 hR.choose hS.choose p (hT p) (congrFun hU p)
      subst T
      rfl

instance finite : Finite (RecordPacket D L w₀ hh r hr₀ n N) :=
  Finite.of_injective code code_injective

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
