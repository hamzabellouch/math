import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.SequentialLimitSimplicity
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropHom
import OAI.Analysis.JiangSu.CentralSequences.CentralSaturation

namespace OAI

section

noncomputable section
namespace SequentialCStar.System
open NormUltra NormUltra.QuotientAlgebra RationalTerms Filter Topology NonunitalGamma
open scoped ENNReal

local instance nonunitalSequentialRationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
local instance nonunitalSequentialRationalTower {E : Type*} [CStarAlgebra E] : IsScalarTower ℚ ℂ E :=
  IsScalarTower.restrictScalars ℚ ℂ E
variable {B : ℕ→Type} [∀ n,CStarAlgebra (B n)] [∀ n,Nontrivial (B n)]
variable (S : System B)
variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
local notation "Fω" => CentralSequenceAlgebra (A := A) U

theorem nonunital_finite_stage_models (d : ℕ→S.Limit) (hdI : d 0=algebraMap ℂ S.Limit Complex.I)
    (hstage : ∀ j,∃ (n : ℕ) (a : B n),S.inclusion n a=d j)
    (hsupply : ∀ n,Nonempty (B n →⋆ₐ[ℂ] Fω)) :
    NonunitalCentralSaturation.FiniteModels (A := A) U d := by
  classical
  choose n b hb using hstage
  intro E
  let F : Finset ℕ := insert 0 (E.biUnion Term.support)
  let M : ℕ := F.sup n
  have hn (j : ℕ) (hj : j∈F) : n j≤M := Finset.le_sup hj
  let y : ℕ→B M := fun j=>if hj:j∈F then S.map (hn j hj) (b j) else 0
  have hy (j : ℕ) (hj : j∈F) : S.inclusion M (y j)=d j := by
    dsimp [y]
    rw [dite_eq_left hj,S.inclusion_compatible,hb]
  obtain ⟨φ⟩ := hsupply M
  let w : ℕ→Fω := fun j=>φ (y j)
  refine ⟨w,?_,?_,?_⟩
  · intro j
    by_cases hj:j∈F
    · have he := S.inclusion_norm M (y j)
      rw [hy j hj] at he
      exact (NonUnitalStarAlgHom.norm_apply_le φ (y j)).trans he.symm.le
    · simp only [w,y,dite_eq_right hj,map_zero,norm_zero]
      exact norm_nonneg _
  · have he : y 0=algebraMap ℂ (B M) Complex.I := by
      apply (S.inclusion_isometry M).injective
      rw [hy 0 (Finset.mem_insert_self 0 _),hdI]
      exact ((S.inclusion M).commutes Complex.I).symm
    change φ (y 0)=_
    rw [he]
    exact φ.commutes Complex.I
  · intro e he
    have hinc : (S.inclusion M) (e.eval y)=e.eval d := by
      have hm := e.map_eval y ((S.inclusion M).restrictScalars ℚ)
      exact hm.trans (e.eval_agree _ d (fun j hj=>hy j
        (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨e,he,hj⟩))))
    have hφe : φ (e.eval y)=e.eval w := e.map_eval y (φ.restrictScalars ℚ)
    rw [←hφe]
    have hi := S.inclusion_norm M (e.eval y)
    rw [hinc] at hi
    exact (NonUnitalStarAlgHom.norm_apply_le φ (e.eval y)).trans hi.symm.le

theorem nonunital_embedding_of_stage_maps [∀ n,TopologicalSpace.SeparableSpace (B n)]
    (hsupply : ∀ n,Nonempty (B n →⋆ₐ[ℂ] Fω)) : Nonempty (S.Limit →⋆ₐ[ℂ] Fω) := by
  obtain ⟨d,hd,hdI,hs⟩ := S.exists_dense_stage_sequence
  exact NonunitalCentralSaturation.rational_saturation U d hd hdI
    (S.nonunital_finite_stage_models U d hdI hs hsupply)
end SequentialCStar.System

end
end

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local instance originalNonunitalStageSeparable (n : ℕ) : TopologicalSpace.SeparableSpace (OriginalJiangSu.Stage n) := by
  infer_instance
local instance (n : ℕ) : Semiring (OriginalJiangSu.Stage n) :=
  (inferInstance : CStarAlgebra (OriginalJiangSu.Stage n)).toSemiring

theorem comparison_original_jiang_su_embedding
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone) :
    ∃ φ : OriginalJiangSu.Algebra →⋆ₐ[ℂ] Fω,Function.Injective φ := by
  have hs (n : ℕ) : Nonempty (OriginalJiangSu.Stage n →⋆ₐ[ℂ] Fω) :=
    comparison_prime_drop_hom U hnuc hsimple hstable hcone hcmp _ _
      (by have := (OriginalJiangSu.pair n).p_gt; omega) (by have := (OriginalJiangSu.pair n).q_gt; omega) ((OriginalJiangSu.pair n).coprime)
  obtain ⟨φ⟩ := OriginalJiangSu.system.nonunital_embedding_of_stage_maps U hs
  let : Nontrivial Fω := ⟨⟨0,1,fun h=>by
    have he := congrArg (centralSequenceToTracial (A := A) U) h
    exact zero_ne_one (by simpa only [map_zero,map_one] using he)⟩⟩
  exact ⟨φ,CurrentMain.simple_starAlgHom_injective OriginalJiangSu.simple φ⟩

end NonunitalSI

end
end

end OAI
