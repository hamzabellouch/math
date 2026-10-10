import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralUpperRootChart
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootCoordinates

namespace OAI

/-! # An actual product chart with neutral translation as its final factor -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootDilation_opposite_cancel (n : ℕ)
    (v : transverseNeutralSpace n) (r : ℝ) (u : UpperRootTime n) :
    (completeRootChain n).rootDilation v.val (-r)
      ((completeRootChain n).rootDilation v.val r u)=u := by
  apply ((completeRootChain n).word_isEmbedding_remaining (completeRootChain_final n)).injective
  rw [(completeRootChain n).word_rootDilation _ v.prop,
    (completeRootChain n).word_rootDilation _ v.prop]
  rw [diagonalOneParameter_neg]
  group

def neutralRootSkewHomeomorph (n : ℕ) :
    (UnitDiagonalTransverse n × transverseNeutralSpace n) × UpperRootTime n ≃ₜ
      (UnitDiagonalTransverse n × transverseNeutralSpace n) × UpperRootTime n where
  toFun z := (z.1,(completeRootChain n).rootDilation z.1.2.val (-1) z.2)
  invFun z := (z.1,(completeRootChain n).rootDilation z.1.2.val 1 z.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    change (completeRootChain n).rootDilation z.1.2.val 1
      ((completeRootChain n).rootDilation z.1.2.val (-1) z.2)=z.2
    simpa only [neg_neg] using upperRootDilation_opposite_cancel n z.1.2 (-1) z.2
  right_inv z := Prod.ext rfl (upperRootDilation_opposite_cancel n z.1.2 1 z.2)
  continuous_toFun := continuous_fst.prodMk
    ((completeRootChain n).continuous_rootDilation _ _ _
      (continuous_subtype_val.comp continuous_fst.snd) continuous_const continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    ((completeRootChain n).continuous_rootDilation _ _ _
      (continuous_subtype_val.comp continuous_fst.snd) continuous_const continuous_snd)

def neutralUpperRootHomeomorph (n : ℕ) :
    UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n) ≃ₜ
      PositiveTransverse n × UpperRootTime n :=
  ((Homeomorph.refl (UnitDiagonalTransverse n)).prodCongr
    (Homeomorph.prodComm (UpperRootTime n) (transverseNeutralSpace n))).trans
    ((Homeomorph.prodAssoc _ _ _).symm.trans
      ((neutralRootSkewHomeomorph n).trans
        ((neutralTransverseHomeomorph n).symm.prodCongr
          (Homeomorph.refl (UpperRootTime n)))))

lemma neutralUpperRootHomeomorph_apply (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n)) :
    neutralUpperRootHomeomorph n z =
      (transverseNeutralReconstruct (z.1,z.2.2),
        (completeRootChain n).rootDilation z.2.2.val (-1) z.2.1) := rfl

lemma isOpen_positiveTransverse (n : ℕ) :
    IsOpen {s : UpperRootTransverse n | ∀ i, 0 < s.val.val i i} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (by fun_prop)

lemma neutralUpperRootParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (neutralUpperRootParam n) := by
  have hi : Topology.IsOpenEmbedding (fun z : PositiveTransverse n × UpperRootTime n =>
      (z.1.val,z.2)) :=
    (isOpen_positiveTransverse n).isOpenEmbedding_subtypeVal.prodMap
      (Topology.IsOpenEmbedding.id (X := UpperRootTime n))
  have H := (upperRootParam_isOpenEmbedding n).comp
    (hi.comp (neutralUpperRootHomeomorph n).isOpenEmbedding)
  convert H using 1
  funext z
  exact neutralUpperRootParam_eq n z

lemma neutralUpperRootQuotientParam_localHomeomorph (n : ℕ) (g : G n) :
    IsLocalHomeomorph (fun z : UnitDiagonalTransverse n ×
      (UpperRootTime n × transverseNeutralSpace n) =>
        Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g*neutralUpperRootParam n z)) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp
      (neutralUpperRootParam_isOpenEmbedding n).isLocalHomeomorph)

end DukePrimeDegree

end

end OAI
