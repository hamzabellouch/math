import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.CentralSequenceSigmaIdeal
import OAI.Analysis.JiangSu.Nonunital.Regularization

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open TraceCone Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable (U : Ultrafilter ℕ)

omit [CompactSpace (NormalizedTrace A)] in
lemma sequenceQuotientMap_constant (a : A) :
    sequenceQuotientMap (A := A) U (boundedConstant (A := A) a)=quotientInclusion U a := rfl

def weightedSequence (a : Positive A) (z : lp (fun _ : ℕ => A) ∞) : lp (fun _ : ℕ => A) ∞ :=
  boundedConstant (A := A) (CFC.sqrt a.1)*z*boundedConstant (A := A) (CFC.sqrt a.1)

omit [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] in
@[simp] lemma weightedSequence_apply (a : Positive A) (z : lp (fun _ : ℕ => A) ∞) (n : ℕ) :
    weightedSequence a z n=CFC.sqrt a.1*z n*CFC.sqrt a.1 := rfl

omit [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] in
lemma weightedSequence_nonneg (a : Positive A) (z : lp (fun _ : ℕ => A) ∞)
    (hz : ∀ n,0≤z n) (n : ℕ) : 0≤weightedSequence a z n := by
  rw [weightedSequence_apply]
  have h := star_left_conjugate_nonneg (hz n) (CFC.sqrt a.1)
  simpa only [(CFC.sqrt_nonneg a.1).isSelfAdjoint.star_eq] using h

omit [CompactSpace (NormalizedTrace A)] in
lemma weightedSequence_quotient (a : Positive A) (z : lp (fun _ : ℕ => A) ∞)
    (hz : sequenceQuotientMap (A := A) U z=1) :
    sequenceQuotientMap (A := A) U (weightedSequence a z)=quotientInclusion U a.1 := by
  simp only [weightedSequence,map_mul,sequenceQuotientMap_constant,hz,mul_one]
  rw [←map_mul,CFC.sqrt_mul_sqrt_self a.1 a.2]

theorem generalized_tracially_large (hsimple : TopologicallySimple A)
    (hcone : AllDenselyFiniteTracesBounded A) (ν : ℕ → ExtendedTrace A)
    (a : Positive A) (ha0 : a.1≠0) (ha : generalizedLimitValue U ν (fun _ => a)<∞)
    (z : lp (fun _ : ℕ => A) ∞) (hzp : ∀ n,0≤z n) (hz : sequenceQuotientMap (A := A) U z=1) :
    generalizedLimitValue U ν (fun n => ⟨weightedSequence a z n,weightedSequence_nonneg a z hzp n⟩)=
      generalizedLimitValue U ν (fun _ => a) := by
  obtain ⟨R,σ,hν⟩ := generalized_limit_finite_multiple U hsimple hcone ν a ha0 ha
  rw [hν (weightedSequence a z) (weightedSequence_nonneg a z hzp)]
  have ha' := hν (boundedConstant (A := A) a.1) (fun _ => a.2)
  change generalizedLimitValue U ν (fun _ => a)=_ at ha'
  rw [ha',weightedSequence_quotient U a z hz,sequenceQuotientMap_constant]

variable [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "F" => CentralSequenceAlgebra (A := A) U
local notation "q" => centralSequenceToTracial (A := A) U

theorem positive_full_trace_representative (f : F) (hfp : 0≤f) (hfn : ‖f‖≤1) (hf : q f=1) :
    ∃ z : lp (fun _ : ℕ => A) ∞, (∀ n,0≤z n) ∧ (∀ n,‖z n‖≤1) ∧
      sequenceQuotientMap (A := A) U z=1 ∧ ∃ Z : normCentralizer (A := A) U,
        NormUltra.QuotientAlgebra.mk U z=(Z:NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) ∧
        centralSequenceQuotient U Z=f := by
  obtain ⟨Z,hZ,hZp,hZn⟩ := CStarLift.exists_positive_contraction
    (centralSequenceQuotient (A := A) U)
    (NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U)) hfp hfn
  have hZp' := (normCentralizer_nonneg_iff U Z).mp hZp
  obtain ⟨z,hz,hzp,hzn⟩ := NormUltra.QuotientAlgebra.positive_contraction_representative hZp' hZn
  refine ⟨z,hzp,hzn,?_,Z,hz,hZ⟩
  change normToTracial U (NormUltra.QuotientAlgebra.mk U z)=1
  rw [hz]
  change q (centralSequenceQuotient U Z)=1
  rw [hZ,hf]

end NonunitalGamma

end
end

end OAI
