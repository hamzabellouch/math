import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.RelativeCentralMap

namespace OAI

section

noncomputable section
namespace NonunitalRelative
open NonunitalGamma NormUltra NormUltra.QuotientAlgebra Filter
open scoped CStarAlgebra ENNReal

variable {A E D : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E] [CStarAlgebra D]
variable (U : Ultrafilter ℕ)
local notation "NA" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "NE" => QuotientAlgebra (fun _ : ℕ => E) U

def constantHom : E →⋆ₐ[ℂ] NE where
  toFun := normInclusion U
  map_zero' := map_zero _
  map_one' := rfl
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul]
    rfl

@[simp] lemma constantHom_apply (e : E) : constantHom U e=normInclusion U e := rfl

lemma normInclusion_norm (a : A) : ‖normInclusion U a‖=‖a‖ := by
  change ‖mk U (boundedConstant (A := A) a)‖=‖a‖
  rw [norm_mk_eq_limsup]
  change Filter.limsup (fun _ : ℕ => ‖a‖) (U : Filter ℕ)=‖a‖
  exact Filter.limsup_const (f := (U : Filter ℕ)) ‖a‖

lemma normInclusion_isometry : Isometry (normInclusion (A := A) U) :=
  AddMonoidHomClass.isometry_of_norm (normInclusion U) (normInclusion_norm U)

lemma map_commute_constant (j : A →⋆ₙₐ[ℂ] E) (b : E) (hc : ∀ a,Commute (j a) b)
    (x : NA) : Commute (NonunitalNormMaps.quotientMap U j x) (normInclusion U b) := by
  obtain ⟨a,rfl⟩ := mk_surjective x
  change mk U (NonunitalNormMaps.boundedMap j a)*mk U (boundedConstant (A := E) b)=
    mk U (boundedConstant (A := E) b)*mk U (NonunitalNormMaps.boundedMap j a)
  rw [←mk_mul,←mk_mul]
  congr 1
  ext n
  exact (hc (a n)).eq

variable (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E) (hc : ∀ a d,Commute (j a) (κ d))

def diagonalCentral : D →⋆ₐ[ℂ] Centralizer U j where
  toFun d := ⟨normInclusion U (κ d),fun a => ((hc a d).symm.map (normInclusion U)).eq⟩
  map_zero' := Subtype.ext (by change normInclusion U (κ 0)=0; rw [map_zero,map_zero])
  map_one' := Subtype.ext (by change normInclusion U (κ 1)=1; rw [map_one]; rfl)
  map_add' d e := Subtype.ext (by change normInclusion U (κ (d+e))=_+_; rw [map_add,map_add])
  map_mul' d e := Subtype.ext (by change normInclusion U (κ (d*e))=_*_; rw [map_mul,map_mul])
  map_star' d := Subtype.ext (by change normInclusion U (κ (star d))=star _; rw [map_star,map_star])
  commutes' c := Subtype.ext (by
    change constantHom U (κ (algebraMap ℂ D c))=algebraMap ℂ NE c
    rw [AlgHomClass.commutes,AlgHomClass.commutes])

def diagonal : D →⋆ₐ[ℂ] RelativeQuotient U j :=
  (RelativeCentral.quotientMap (inclusion U j)).comp (diagonalCentral U j κ hc)

variable [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ)≤atTop)]

lemma factor_commute_diagonal (x : CentralSequenceAlgebra (A := A) U) (d : D) :
    Commute (factor U j x) (diagonal U j κ hc d) := by
  obtain ⟨y,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
  change Commute (RelativeCentral.quotientMap (inclusion U j) (centralMap U j y))
    (RelativeCentral.quotientMap (inclusion U j) (diagonalCentral U j κ hc d))
  apply Commute.map
  apply Subtype.ext
  exact (map_commute_constant U j (κ d) (fun a => hc a d) (y:NA)).eq

end NonunitalRelative

end
end

end OAI
