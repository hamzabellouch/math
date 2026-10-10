import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ModifiedWeightSameBand
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TopologyTreeSteps
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

def untaggedEdgeCode (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    Option (Bool × Finset (Fin ℓ)) :=
  (untaggedType w hh 𝔏 a p).map (fun t => (t.1,t.2.edges.val))

lemma tokens_eq_of_codes (w v : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (𝔐 : List (AttachedSpec v D L))
    (a : S.FixedResidues w) (b : S.FixedResidues v) (p : S.Index)
    (hT : taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = taggedTokens v hh 𝔐 (recordAt v hh 𝔐 b) p)
    (hU : untaggedEdgeCode w hh 𝔏 a p = untaggedEdgeCode v hh 𝔐 b p) :
    recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = recordTokens v hh 𝔐 (recordAt v hh 𝔐 b) p := by
  rcases he : untaggedType w hh 𝔏 a p with _ | t <;>
    rcases hf : untaggedType v hh 𝔐 b p with _ | u
  · rw [← taggedTokens_of_none w hh 𝔏 a p he,← taggedTokens_of_none v hh 𝔐 b p hf]
    exact hT
  · simp only [untaggedEdgeCode,he,hf,Option.map_none,Option.map_some] at hU
    contradiction
  · simp only [untaggedEdgeCode,he,hf,Option.map_none,Option.map_some] at hU
    contradiction
  · simp only [untaggedEdgeCode,he,hf,Option.map_some] at hU
    have hE : t.2.edges.val = u.2.edges.val := congrArg Prod.snd (Option.some.inj hU)
    rw [(untaggedType_some w hh 𝔏 a p t he).2,(untaggedType_some v hh 𝔐 b p u hf).2,hE]

theorem line_eq_of_record_codes (w v : ClosedLine h ℓ) (hh : 0 < h)
    (hw : ∀ i, w.label i ∈ D.members) (hv : ∀ i, v.label i ∈ D.members)
    (r : ℕ) (hwr : (returnSteps w).card=r) (hvr : (returnSteps v).card=r)
    (ht : encodeTopology w r hwr=encodeTopology v r hvr)
    (𝔏 : List (AttachedSpec w D L)) (𝔐 : List (AttachedSpec v D L))
    (a : S.FixedResidues w) (b : S.FixedResidues v)
    (hT : ∀ p, taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = taggedTokens v hh 𝔐 (recordAt v hh 𝔐 b) p)
    (hU : untaggedEdgeCode w hh 𝔏 a = untaggedEdgeCode v hh 𝔐 b) : w=v := by
  apply topology_tree_labels_injective w v hh r hwr hvr ht
  intro e he
  have hev : e ∈ v.treeSteps := topology_treeSteps hwr hvr ht ▸ he
  rw [← recordTokens_recover_label w hh 𝔏 a hw e he,
    ← recordTokens_recover_label v hh 𝔐 b hv e hev]
  apply Finset.prod_congr rfl
  intro p hp
  rw [tokens_eq_of_codes w v hh 𝔏 𝔐 a b p (hT p) (congrFun hU p)]

def untaggedReference {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) : S.Index → Option (TokenType w) :=
  fun p => (untaggedType v hh 𝔏 a p).map (fun t => (t.1,H.shapeMap t.2))

lemma untaggedReference_edges {w v : ClosedLine h ℓ} (H : SameGeometry v w) (hh : 0 < h)
    (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (p : S.Index) :
    (untaggedReference H hh 𝔏 a p).map (fun t => (t.1,t.2.edges.val)) =
      untaggedEdgeCode v hh 𝔏 a p := by
  simp only [untaggedReference,untaggedEdgeCode,Option.map_map]
  rfl

lemma tokenWeight_reference {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (pC pZ : S.Index) (t : TokenType v) :
    tokenWeight v pC pZ t = tokenWeight w pC pZ (t.1,H.shapeMap t.2) := by
  unfold tokenWeight
  exact H.modifiedWeight _ _

lemma untaggedReference_injective {w v : ClosedLine h ℓ} (H : SameGeometry v w) :
    Function.Injective (fun t : TokenType v => (t.1,H.shapeMap t.2)) := by
  intro t u he
  apply Prod.ext
  · exact congrArg (fun z : TokenType w => z.1) he
  · exact H.shapeEquiv.injective (congrArg Prod.snd he)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
