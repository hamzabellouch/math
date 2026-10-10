import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.CentralMatrix
import OAI.Analysis.JiangSu.CentralSequences.SigmaOrderZeroLift
import OAI.Analysis.JiangSu.CentralSequences.CentralGeneralizedLargeness
import OAI.Analysis.JiangSu.CuntzSemigroup.CompletedOrthogonalRanks

namespace OAI


noncomputable section
namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma stabilized_cuntz_zero_le (x : CuntzClass (MatrixLimit A)) : 0 ≤ x := by
  induction x using Quotient.inductionOn with | h a =>
  exact CuntzBelow.zero a

lemma stabilized_cuntz_le_succ_nsmul (x : CuntzClass (MatrixLimit A)) (k : ℕ) : x ≤ (k+1) • x := by
  have h := CuntzClass.matrixAdd_mono (le_refl x) (stabilized_cuntz_zero_le (k • x))
  change x+0 ≤ x+k • x at h
  simpa only [add_zero,add_comm,succ_nsmul] using h

theorem stabilized_cuntz_almost_unperforated
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone)
    (x y : CuntzClass (MatrixLimit A)) (k : ℕ) (hxy : (k+1) • x ≤ k • y) : x ≤ y := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  change (k+1) • CuntzClass.mk a ≤ k • CuntzClass.mk b at hxy
  change CuntzClass.mk a ≤ CuntzClass.mk b
  by_cases hb : b.1=0
  · have he : b=Positive.zero := Subtype.ext hb
    subst b
    have hz : k • CuntzClass.mk (Positive.zero (A := MatrixLimit A))=0 := by
      change k • (0 : CuntzClass (MatrixLimit A))=0
      exact nsmul_zero k
    rw [hz] at hxy
    exact (stabilized_cuntz_le_succ_nsmul (CuntzClass.mk a) k).trans hxy
  · apply hcmp a b hb
    intro τ hτ ht
    let σ := boundedStabilized τ (hcone τ hτ)
    have hh := σ.stabilizedCuntzRank_monotone hxy
    simp only [map_nsmul,ExtendedTrace.stabilizedCuntzRank_mk,nsmul_eq_mul] at hh
    change (k+1 : ℕ) * σ.rank a ≤ (k : ℕ) * σ.rank b at hh
    change σ.rank b=1 at ht
    rw [ht,mul_one] at hh
    change σ.rank a<1
    by_contra hn
    have ha : 1 ≤ σ.rank a := le_of_not_gt hn
    have hmul : ((k+1:ℕ):ℝ≥0∞) ≤ ((k+1:ℕ):ℝ≥0∞)*σ.rank a := by
      simpa using mul_le_mul_right ha ((k+1:ℕ):ℝ≥0∞)
    have hbad := hmul.trans hh
    have hk : ¬(k+1 : ℕ) ≤ k := by omega
    exact hk (by exact_mod_cast hbad)

end NonunitalGamma

end


noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain TraceCone Filter Topology
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable [CompactSpace (NormalizedTrace A)] (U : Ultrafilter ℕ)
variable [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "F" => CentralSequenceAlgebra (A := A) U
local notation "q" => centralSequenceToTracial (A := A) U

 theorem stably_projectionless_uniform_mcduff
    (hsimple : TopologicallySimple A) (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone)
    (hnuc : NuclearUnitization.IsNuclear A) (m : ℕ) (hm : 0 < m) :
    ∃ φ : CStarMatrix (Fin m) (Fin m) ℂ →CP F,
      (∀ M, ‖φ M‖≤‖M‖) ∧
      (∀ M N, φ M*φ N=φ (M*N)*φ 1) ∧
      (∀ M N, 0≤M → 0≤N → M*N=0 → φ M*φ N=0) ∧ q (φ 1)=1 ∧
      ∃ z : lp (fun _ : ℕ => A) ∞, (∀ n,0≤z n) ∧ (∀ n,‖z n‖≤1) ∧
        sequenceQuotientMap (A := A) U z=1 ∧
        (∃ Z : normCentralizer (A := A) U,
          NormUltra.QuotientAlgebra.mk U z=(Z:NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) ∧
          centralSequenceQuotient U Z=φ 1) ∧
        ∀ (ν : ℕ → ExtendedTrace A) (a : Positive A), a.1≠0 →
          generalizedLimitValue U ν (fun _ => a)<∞ →
          ∀ hzp : ∀ n,0≤z n,
          generalizedLimitValue U ν (fun n => ⟨weightedSequence a z n,weightedSequence_nonneg a z hzp n⟩)=
            generalizedLimitValue U ν (fun _ => a) := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  obtain ⟨η,hη⟩ := comparison_central_matrix U Fact.out hsimple hstable hcone hcmp hnuc m hm
  obtain ⟨φ,hφ,hφn,hφrel,hφoz,hφ1⟩ := central_matrix_order_zero_lift U m hm η
    (fun M a => (hη M a).eq)
  have hφp : 0≤φ 1 := map_nonneg φ zero_le_one
  have hφn1 : ‖φ 1‖≤1 := (hφn 1).trans_eq norm_one
  obtain ⟨z,hzp,hzn,hz,hZ⟩ := positive_full_trace_representative U (φ 1) hφp hφn1 hφ1
  refine ⟨φ,hφn,hφrel,hφoz,hφ1,z,hzp,hzn,hz,hZ,?_⟩
  intro ν a ha0 ha hzp'
  exact generalized_tracially_large U hsimple hcone ν a ha0 ha z hzp' hz

end NonunitalGamma

end

end OAI
