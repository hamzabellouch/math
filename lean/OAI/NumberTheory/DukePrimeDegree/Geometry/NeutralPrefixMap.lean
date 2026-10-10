import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralCoordinateMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLift
import OAI.NumberTheory.DukePrimeDegree.Geometry.RestrictedCoordinateMap

namespace OAI

/-! # The actual change from neutral coordinates to full-root prefix coordinates -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma emptyRootPattern (n : ℕ) : InitialRootPattern (∅ : Finset (Fin n × Fin n)) := by
  intro p hp
  simp at hp

abbrev neutralEmptyPrefix (n : ℕ) : RootPrefixCoordinates n ∅ PUnit.{1} :=
  RootPrefixCoordinates.empty n

def neutralToPrefix (n : ℕ) (z : NeutralCoordinateBase n × transverseNeutralSpace n) :
    (UpperRootTransverse n × PUnit.{1}) × UpperRootTime n :=
  (((transverseNeutralReconstruct (z.1.1,z.2)).val,PUnit.unit),
    (completeRootChain n).rootDilation z.2.val (-1) z.1.2)

lemma neutralToPrefix_param (n : ℕ) (g : G n)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) :
    (neutralEmptyPrefix n).timeGroupParam (completeRootChain n)
        (emptyRootPattern n) (completeRootChain_final n) g (neutralToPrefix n z)=
      g*neutralProductParam n z := by
  unfold RootPrefixCoordinates.timeGroupParam
  rw [RootPrefixCoordinates.groupParam_eq_mul]
  change g*((transverseNeutralReconstruct (z.1.1,z.2)).val.val *
      (1*(completeRootChain n).word
        ((completeRootChain n).rootDilation z.2.val (-1) z.1.2))) = _
  rw [one_mul]
  have he := (neutralUpperRootParam_eq n (z.1.1,(z.1.2,z.2))).symm
  rw [upperRootParam_eq_mul] at he
  exact congrArg (g*·) he

theorem neutralToPrefix_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (neutralToPrefix n) := by
  have hf := (neutralEmptyPrefix n).timeGroupParam_isOpenEmbedding
    (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) (1 : G n)
  apply Topology.IsOpenEmbedding.of_comp (neutralToPrefix n) hf
  convert neutralProductParam_isOpenEmbedding n using 1
  funext z
  exact (neutralToPrefix_param n 1 z).trans (one_mul _)

lemma neutralToPrefix_base (n : ℕ)
    (x y : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hN : x.1.1=y.1.1) (hv : x.2=y.2) :
    (neutralToPrefix n x).1=(neutralToPrefix n y).1 := by
  change (Subtype.val (transverseNeutralReconstruct (x.1.1,x.2)),PUnit.unit)=
    (Subtype.val (transverseNeutralReconstruct (y.1.1,y.2)),PUnit.unit)
  rw [hN,hv]

lemma neutralToPrefix_fiber_injective (n : ℕ)
    (x y : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hv : x.2=y.2) (hu : (neutralToPrefix n x).2=(neutralToPrefix n y).2) :
    x.1.2=y.1.2 := by
  change (completeRootChain n).rootDilation x.2.val (-1) x.1.2=
    (completeRootChain n).rootDilation y.2.val (-1) y.1.2 at hu
  rw [←hv] at hu
  have H := congrArg ((completeRootChain n).rootDilation x.2.val 1) hu
  have hx := upperRootDilation_opposite_cancel n x.2 (-1) x.1.2
  have hy := upperRootDilation_opposite_cancel n x.2 (-1) y.1.2
  simp only [neg_neg] at hx hy
  exact hx.symm.trans (H.trans hy)

theorem neutralToPrefix_restrict_le (n : ℕ) (g : G n)
    (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (R : Set (NeutralCoordinateBase n × transverseNeutralSpace n))
    (hRB : ∀ z ∈ R, neutralToPrefix n z ∈ B.domain) :
    (((quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)).restrict R).map
        (neutralToPrefix n) ≤ B.coordinateMeasure μ := by
  have H := map_restrict_comap_le (quotientLiftMeasure n μ s)
    ((neutralEmptyPrefix n).timeGroupParam (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    ((neutralEmptyPrefix n).timeGroupParam_isOpenEmbedding (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g).measurableEmbedding
    (neutralToPrefix n) (neutralToPrefix_isOpenEmbedding n).measurableEmbedding
    R B.domain hRB
  have he : (neutralEmptyPrefix n).timeGroupParam (completeRootChain n)
        (emptyRootPattern n) (completeRootChain_final n) g ∘ neutralToPrefix n=
      fun z => g*neutralProductParam n z := funext (neutralToPrefix_param n g)
  rw [he,←B.coordinateMeasure_eq_lift_restrict μ s hsm hs] at H
  exact H

end DukePrimeDegree

end

end OAI
