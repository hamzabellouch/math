import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralCoordinateMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.WeakStableFactorization

namespace OAI

/-! # Weak stable displacements preserve the lower unitriangular coordinate -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutralProductParam_mul_upper (n : ℕ)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n)
    (g : G n) (hg : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i) :
    ∃ (u : UpperRootTime n) (v : transverseNeutralSpace n),
      neutralProductParam n ((z.1.1,u),v)=neutralProductParam n z*g := by
  obtain ⟨w,hw,t,ht⟩ := upper_triangular_positive_diagonal_factorization g hg hpos
  let v : transverseNeutralSpace n := z.2+⟨w,hw⟩
  let t' := (completeRootChain n).rootDilation v.val 1 t
  have hm : (completeRootChain n).word z.1.2*(completeRootChain n).word t' ∈
      positiveRootGeneratedGroup (allPositiveRoots n) :=
    (positiveRootGeneratedGroup _).mul_mem (upperRootWord_mem n _) (upperRootWord_mem n _)
  obtain ⟨u,hu⟩ := upperRootWord_surjective n ⟨_,hm⟩
  refine ⟨u,v,?_⟩
  change z.1.1.val.val*(completeRootChain n).word u*diagonalOneParameter v.val v.prop 1=
    (z.1.1.val.val*(completeRootChain n).word z.1.2*
      diagonalOneParameter z.2.val z.2.prop 1)*g
  rw [hu]
  dsimp only [t']
  rw [(completeRootChain n).word_rootDilation v.val v.prop,
    diagonalOneParameter_neg,ht]
  have hd : diagonalOneParameter v.val v.prop 1=
      diagonalOneParameter z.2.val z.2.prop 1*diagonalOneParameter w hw 1 :=
    diagonalOneParameter_add_weights _ _ _ _ _
  rw [hd]
  group

theorem neutral_unit_coordinate_of_upper_displacement (n : ℕ)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (g : G n) (hg : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (heq : neutralProductParam n w=neutralProductParam n z*g) :
    z.1.1=w.1.1 := by
  obtain ⟨u,v,huv⟩ := neutralProductParam_mul_upper n z g hg hpos
  have hz := (neutralProductParam_isOpenEmbedding n).injective (huv.trans heq.symm)
  simpa only using
    congrArg (fun q : NeutralCoordinateBase n × transverseNeutralSpace n => q.1.1) hz

theorem neutral_graph_upper_displacement (n : ℕ)
    (E : Set (NeutralCoordinateBase n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hz : z.1 ∈ E) (hw : w.1 ∈ E)
    (g : G n) (hg : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (heq : neutralProductParam n w=neutralProductParam n z*g) :
    ∃ v : transverseNeutralSpace n, g=diagonalOneParameter v.val v.prop 1 := by
  have hN := neutral_unit_coordinate_of_upper_displacement n z w g hg hpos heq
  have hu := hE z.1 hz w.1 hw hN
  have hb : z.1=w.1 := Prod.ext hN hu
  have hc : (z.1,z.2+(w.2-z.2))=w := by
    refine Prod.ext ?_ ?_
    · exact hb
    · change z.2+(w.2-z.2)=w.2
      abel
  have ht := neutralProductParam_add n z (w.2-z.2)
  rw [hc] at ht
  exact ⟨w.2-z.2,mul_left_cancel (heq.symm.trans ht)⟩

end DukePrimeDegree

end

end OAI
