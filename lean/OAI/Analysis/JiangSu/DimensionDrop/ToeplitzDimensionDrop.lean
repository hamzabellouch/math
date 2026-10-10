import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.HalfFlip
import OAI.Analysis.JiangSu.Absorption.CanonicalUnitalAbsorption
import OAI.Analysis.JiangSu.DimensionDrop.SequentialCentralEmbedding
import OAI.Analysis.JiangSu.DimensionDrop.SequentialEmbedding
import OAI.Analysis.JiangSu.Traceless.TracelessFiniteIdentityExcision

namespace OAI

section

noncomputable section
namespace CurrentMain.ProjectionRow
open CompletelyPositiveOperations
open scoped ComplexOrder CStarAlgebra

variable {B I : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [Fintype I] [DecidableEq I]

omit [PartialOrder B] [StarOrderedRing B] in
lemma matrixHom_matrixUnit (V : ProjectionRow I (1:B)) (i j : I) :
    V.matrixHom (matrixUnit i j)=V.entry i*star (V.entry j) := by
  classical
  change (∑ k,∑ l,(Matrix.single i j (1:ℂ)) k l • V.coeff 1 k l)=_
  simp [Matrix.single_apply,coeff,ite_and]

def toeplitzWitness (V : ProjectionRow I (1:B)) (p : I) :
    DimensionDropRelations.Witness (B := B) p where
  φ := (V.matrixHom : CStarMatrix I I ℂ →CP B)
  contractive := fun M=>NonUnitalStarAlgHom.norm_apply_le V.matrixHom M
  orderZero := fun M N=>by
    change V.matrixHom M*V.matrixHom N=V.matrixHom (M*N)*V.matrixHom 1
    rw [←map_mul,←map_mul,mul_one]
  s := V.entry p*(1-V.sample 1)
  small := by
    change star (V.entry p*(1-V.sample 1))*(V.entry p*(1-V.sample 1))=1-V.matrixHom 1
    rw [V.matrixHom_one,star_mul,star_sub,star_one,V.range_projection.isSelfAdjoint.star_eq]
    calc
      _=(1-V.sample 1)*(star (V.entry p)*V.entry p)*(1-V.sample 1) := by noncomm_ring
      _=1-V.sample 1 := by
        rw [V.gram_diag,mul_one]
        have hh := V.range_projection.isIdempotentElem.eq
        noncomm_ring [hh]
  support := by
    change V.matrixHom (matrixUnit p p)*(V.entry p*(1-V.sample 1))=V.entry p*(1-V.sample 1)
    rw [V.matrixHom_matrixUnit]
    calc
      _=V.entry p*(star (V.entry p)*V.entry p)*(1-V.sample 1) := by noncomm_ring
      _=V.entry p*(1-V.sample 1) := by rw [V.gram_diag,mul_one]

end CurrentMain.ProjectionRow

end
end

section

noncomputable section
namespace CurrentMain.Traceless
open Pureness DirectComparison Filter Topology JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U
local notation "C" => unitalNormCentralizer (A := A) U
local instance (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

theorem empty_comparison_dimension_drop_hom (hnuc : IsNuclear.{0,0} A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : EmptyTraceComparison A) (hfree : (U : Filter ℕ)≤atTop)
    (n : ℕ) (hn : 0<n) : Nonempty (DimensionDrop (n+1) n →⋆ₐ[ℂ] C) := by
  obtain ⟨x,_hxn,hx,hx1,hxc⟩ := identity_cross_excision_ultrapower U hnuc hsimple hinf hcmp hfree
  let v : ℕ→C := fun i=>⟨NormUltra.QuotientAlgebra.mk U (x i),fun a=>hxc i a⟩
  let V : ProjectionRow (Fin n) (1:C) := {
    projection := IsStarProjection.one _
    entry := fun i=>v i
    gram_diag := fun i=>Subtype.ext (hx1 i)
    gram_offdiag := fun i j hij=>by
      apply Subtype.ext
      change star (NormUltra.QuotientAlgebra.mk U (x i))*NormUltra.QuotientAlgebra.mk U (x j)=0
      have hh := hx i j 1
      have hneq : (i:ℕ)≠(j:ℕ) := fun he=>hij (Fin.ext he)
      simpa only [normInclusion_one,mul_one,ite_eq_right hneq] using hh }
  exact ⟨(V.toeplitzWitness (⟨0,hn⟩ : Fin n)).dimensionDropHom⟩

theorem empty_comparison_prime_drop_hom (hnuc : IsNuclear.{0,0} A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : EmptyTraceComparison A) (hfree : (U : Filter ℕ)≤atTop)
    (p q : ℕ) (hp : 0<p) (hq : 0<q) (hco : p.Coprime q) :
    Nonempty (DimensionDrop p q →⋆ₐ[ℂ] C) := by
  obtain ⟨n,hn,⟨ψ⟩⟩ := prime_drop_into_consecutive hp hq hco
  obtain ⟨φ⟩ := empty_comparison_dimension_drop_hom U hnuc hsimple hinf hcmp hfree n hn
  exact ⟨φ.comp ψ⟩

end CurrentMain.Traceless

end
end

section

noncomputable section
namespace CurrentMain.Traceless
open Pureness DirectComparison Filter Topology JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U
local instance (n : ℕ) : Semiring (OriginalJiangSu.Stage n) :=
  (inferInstance : CStarAlgebra (OriginalJiangSu.Stage n)).toSemiring

theorem empty_comparison_original_jiang_su_embedding (hnuc : IsNuclear.{0,0} A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : EmptyTraceComparison A) (hfree : (U : Filter ℕ)≤atTop) :
    ∃ φ : OriginalJiangSu.Algebra →⋆ₐ[ℂ] N,Function.Injective φ ∧
      ∀ a z,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ z) := by
  have hs (n : ℕ) : ∃ φ : OriginalJiangSu.Stage n →⋆ₐ[ℂ] N,
      ∀ a z,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ z) := by
    obtain ⟨φ⟩ := empty_comparison_prime_drop_hom U hnuc hsimple hinf hcmp hfree _ _
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
  exact ⟨φ,CurrentMain.simple_starAlgHom_injective OriginalJiangSu.simple φ,hφ⟩

end CurrentMain.Traceless

end
end

section

noncomputable section
namespace OriginalJiangSu
open Pureness CStarAbsorption
open scoped CStarAlgebra TensorProduct

theorem spatial_connected_half_flip :
    ConnectedApproximateInnerHalfFlip (ActualSpatial.tensorMap Algebra Algebra) :=
  connected_half_flip _ (ActualSpatial.tensorMap_injective _ _)

theorem spatial_half_flip :
    ApproximateInnerHalfFlip (ActualSpatial.tensorMap Algebra Algebra) :=
  spatial_connected_half_flip.toApproximate

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [TopologicalSpace.SeparableSpace A]

theorem absorption_of_embedding (U : Ultrafilter ℕ)
    (φ : Algebra →⋆ₐ[ℂ] NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U)
    (hφ : ∀ a z,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ z)) :
    Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.Tensor A Algebra) := by
  exact ActualSpatial.unital_absorption_of_embedding A Algebra U φ hφ
    nuclear simple spatial_half_flip

theorem absorption_of_embedding_exists (U : Ultrafilter ℕ)
    (h : ∃ φ : Algebra →⋆ₐ[ℂ] NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U,
      Function.Injective φ ∧ ∀ a z,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ z)) :
    Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.Tensor A Algebra) := by
  obtain ⟨φ,-,hφ⟩ := h
  exact absorption_of_embedding U φ hφ
end OriginalJiangSu

namespace DirectComparison
open Pureness CurrentMain Filter
open scoped CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
include U hfree in
 theorem comparison_original_jiang_su_absorption
    (hnuc : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : StrictComparison A) :
    Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.Tensor A OriginalJiangSu.Algebra) := by
  exact OriginalJiangSu.absorption_of_embedding_exists U
    (comparison_original_jiang_su_embedding U hfree hnuc hsimple hinf hcmp)
end DirectComparison

namespace CurrentMain.Traceless
open Pureness Filter
open scoped CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
include U hfree in
 theorem empty_comparison_original_jiang_su_absorption
    (hnuc : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : EmptyTraceComparison A) :
    Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.Tensor A OriginalJiangSu.Algebra) := by
  exact OriginalJiangSu.absorption_of_embedding_exists U
    (empty_comparison_original_jiang_su_embedding U hnuc hsimple hinf hcmp hfree)
end CurrentMain.Traceless

namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter
open scoped CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
include U in
 theorem comparison_original_jiang_su_absorption
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone) :
    Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.NonunitalTensor A OriginalJiangSu.Algebra) := by
  obtain ⟨φ,-⟩ := comparison_original_jiang_su_embedding U hnuc hsimple hstable hcone hcmp
  exact ActualSpatial.nonunital_absorption_of_embedding A OriginalJiangSu.Algebra U φ
    OriginalJiangSu.nuclear OriginalJiangSu.simple OriginalJiangSu.spatial_connected_half_flip
end NonunitalSI

end
end

end OAI
