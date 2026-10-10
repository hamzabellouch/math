import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FlatCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FirstEdges

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

lemma geometry_goodEdges {v w : ClosedLine h ℓ} (H : SameGeometry v w) : goodEdges v=goodEdges w := by
  ext e
  simp only [goodEdges,mem_filter,H.trees,H.good]

lemma pivotEdges_reference {v w : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) :
    pivotEdges (slotShape (TypeFibers.multiplicity (untaggedReference H hh 𝔏 a)))
      (slotCore (TypeFibers.multiplicity (untaggedReference H hh 𝔏 a))) =
    pivotEdges (slotShape (TypeFibers.multiplicity (untaggedType v hh 𝔏 a)))
      (slotCore (TypeFibers.multiplicity (untaggedType v hh 𝔏 a))) := by
  classical
  ext e
  by_cases he : e ∈ goodEdges v
  · have hew : e ∈ goodEdges w := geometry_goodEdges H ▸ he
    rw [pivotEdges_fibers w _ e hew,pivotEdges_fibers v _ e he]
    constructor
    · rintro ⟨p,t,hp,hc,ht⟩
      obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp hp
      exact ⟨p,u,hu,hc,ht⟩
    · rintro ⟨p,t,hp,hc,ht⟩
      refine ⟨p,(t.1,H.shapeMap t.2),?_,hc,ht⟩
      simp only [untaggedReference,hp,Option.map_some]
  · have hew : e ∉ goodEdges w := geometry_goodEdges H ▸ he
    simp only [pivotEdges,mem_filter,he,hew,false_and]

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

noncomputable def flatPivots (c : FlatCode S w₀ C₀ B L n N) : ℕ :=
  (pivotEdges (slotShape (TypeFibers.multiplicity c.2.2.2))
    (slotCore (TypeFibers.multiplicity c.2.2.2))).card

theorem flatCode_good_cover (x : RecordPacket D L w₀ hh r hr₀ n N) :
    (goodEdges w₀).card ≤ N + (recordU x.line x.record.1).card + flatPivots x.flatCode := by
  have hc := good_edges_record_cover x.line hh x.primitives x.residues
  have hU := congrArg (fun R : AssignedRecord S ℓ => (recordU x.line R.1).card) x.realized_residues
  rw [hU,geometry_goodEdges x.geometry] at hc
  unfold flatPivots flatCode
  rw [pivotEdges_reference]
  exact hc.trans (Nat.add_le_add_right (Nat.add_le_add_right x.residues_count _) _)

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
