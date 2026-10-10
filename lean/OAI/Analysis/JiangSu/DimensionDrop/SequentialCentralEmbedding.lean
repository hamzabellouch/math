import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.SequentialLimitSimplicity
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropGeneratedHom
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerArrayTest

namespace OAI

section

noncomputable section
namespace SequentialCStar.System
open NormUltra NormUltra.QuotientAlgebra RationalTerms Filter Topology
open scoped ENNReal

local instance sequentialRationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
local instance sequentialRationalTower {E : Type*} [CStarAlgebra E] : IsScalarTower ℚ ℂ E :=
  IsScalarTower.restrictScalars ℚ ℂ E
variable {C : ℕ→Type*} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable (S : System C)
variable {A : Type*} [CStarAlgebra A] (U : Ultrafilter ℕ)
local notation "N" => QuotientAlgebra (fun _ : ℕ=>A) U

 theorem finite_stage_models (d : ℕ→S.Limit) (hdI : d 0=algebraMap ℂ S.Limit Complex.I)
    (hstage : ∀ j,∃ (n : ℕ) (a : C n),S.inclusion n a=d j)
    (hsupply : ∀ n,∃ φ : C n →⋆ₐ[ℂ] N,∀ a z,Commute (diagonalHom U a) (φ z)) :
    CentralFiniteModels (A := A) U d := by
  classical
  choose n b hb using hstage
  intro E
  let F : Finset ℕ := insert 0 (E.biUnion Term.support)
  let M : ℕ := F.sup n
  have hn (j : ℕ) (hj : j∈F) : n j≤M := Finset.le_sup hj
  let y : ℕ→C M := fun j=>if hj:j∈F then S.map (hn j hj) (b j) else 0
  have hy (j : ℕ) (hj : j∈F) : S.inclusion M (y j)=d j := by
    dsimp [y]
    rw [dite_eq_left hj,S.inclusion_compatible,hb]
  obtain ⟨φ,hφ⟩ := hsupply M
  let w : ℕ→N := fun j=>φ (y j)
  refine ⟨w,?_,fun a j=>hφ a (y j),?_,?_⟩
  · intro j
    by_cases hj:j∈F
    · have he := S.inclusion_norm M (y j)
      rw [hy j hj] at he
      exact (NonUnitalStarAlgHom.norm_apply_le φ (y j)).trans he.symm.le
    · simp only [w,y,dite_eq_right hj,map_zero,norm_zero]
      exact norm_nonneg _
  · have he : y 0=algebraMap ℂ (C M) Complex.I := by
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

 theorem central_embedding_of_stage_maps [∀ n,TopologicalSpace.SeparableSpace (C n)]
    [TopologicalSpace.SeparableSpace A] (hfree : (U : Filter ℕ)≤atTop)
    (hsupply : ∀ n,∃ φ : C n →⋆ₐ[ℂ] N,∀ a z,Commute (diagonalHom U a) (φ z)) :
    ∃ φ : S.Limit →⋆ₐ[ℂ] N,∀ a z,Commute (diagonalHom U a) (φ z) := by
  obtain ⟨d,hd,hdI,hs⟩ := S.exists_dense_stage_sequence
  exact central_rational_saturation U d hfree hd hdI (S.finite_stage_models U d hdI hs hsupply)
end SequentialCStar.System

end
end

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology CompletelyPositiveOperations JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U
local instance originalStageSeparable (n : ℕ) : TopologicalSpace.SeparableSpace (OriginalJiangSu.Stage n) := by
  infer_instance
local instance (n : ℕ) : Semiring (OriginalJiangSu.Stage n) :=
  (inferInstance : CStarAlgebra (OriginalJiangSu.Stage n)).toSemiring

 theorem comparison_original_jiang_su_embedding (hfree : (U : Filter ℕ)≤atTop)
    (hnuc : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) :
    ∃ φ : OriginalJiangSu.Algebra →⋆ₐ[ℂ] N,Function.Injective φ ∧
      ∀ a z,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ z) := by
  have hs (n : ℕ) : ∃ φ : OriginalJiangSu.Stage n →⋆ₐ[ℂ] N,
      ∀ a z,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ z) := by
    obtain ⟨φ⟩ := comparison_prime_drop_hom U hfree hnuc hsimple hinf hcmp _ _
      (by have := (OriginalJiangSu.pair n).p_gt; omega) (by have := (OriginalJiangSu.pair n).q_gt; omega) ((OriginalJiangSu.pair n).coprime)
    refine ⟨(unitalNormCentralizer (A := A) U).subtype.comp φ,?_⟩
    intro a z
    exact ((φ z).property a).symm
  obtain ⟨φ,hφ⟩ := OriginalJiangSu.system.central_embedding_of_stage_maps U hfree hs
  have hdiag (a : A) : ‖NormUltra.QuotientAlgebra.diagonalHom U a‖=‖a‖ := by
    change ‖NormUltra.QuotientAlgebra.mk U (boundedDiagonal a)‖=‖a‖
    rw [NormUltra.QuotientAlgebra.norm_mk_eq_limsup]
    exact Filter.limsup_const (f := (U : Filter ℕ)) ‖a‖
  let : Nontrivial N := (AddMonoidHomClass.isometry_of_norm
    (NormUltra.QuotientAlgebra.diagonalHom U) hdiag).injective.nontrivial
  refine ⟨φ,?_,hφ⟩
  exact CurrentMain.simple_starAlgHom_injective OriginalJiangSu.simple φ

end DirectComparison

end
end

end OAI
