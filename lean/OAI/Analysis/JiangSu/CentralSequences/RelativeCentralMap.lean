import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormCentralSequenceAlgebra
import OAI.Analysis.JiangSu.CentralSequences.RelativeCentralQuotient
import OAI.Analysis.JiangSu.CentralSequences.UnitalTraceKernelSigma
import OAI.Analysis.JiangSu.Nonunital.NormMaps

namespace OAI

section

noncomputable section
namespace NonunitalRelative
open NonunitalGamma NormUltra Filter
open scoped CStarAlgebra ENNReal

variable {A E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E]
variable (U : Ultrafilter ℕ) (j : A →⋆ₙₐ[ℂ] E)
local notation "NA" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "NE" => QuotientAlgebra (fun _ : ℕ => E) U

def inclusion : A →⋆ₙₐ[ℂ] NE := (normInclusion U).comp j
abbrev Centralizer := RelativeCentral.centralizer (inclusion U j)
abbrev RelativeQuotient := RelativeCentral.Quotient (inclusion U j)

def centralMap : normCentralizer (A := A) U →⋆ₙₐ[ℂ] Centralizer U j where
  toFun x := ⟨NonunitalNormMaps.quotientMap U j (x:NA),fun a =>
    (NonunitalNormMaps.quotientMap_commute U j a (x:NA) (x.property a)).eq⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ (x : NA) (y : NA))
  map_mul' x y := Subtype.ext (map_mul _ (x : NA) (y : NA))
  map_star' x := Subtype.ext (map_star _ (x : NA))
  map_smul' c x := Subtype.ext (map_smul _ c (x : NA))

lemma centralMap_quotient_eq (x y : normCentralizer (A := A) U)
    (h : centralSequenceQuotient U x=centralSequenceQuotient U y) :
    RelativeCentral.quotientMap (inclusion U j) (centralMap U j x)=
      RelativeCentral.quotientMap (inclusion U j) (centralMap U j y) := by
  have hh := (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff (normAnnihilator U) x y).mp h
  apply (RelativeCentral.quotient_eq_iff _ _ _).mpr
  intro a
  have hha : ((x:NA)-(y:NA))*normInclusion U a=0 ∧ normInclusion U a*((x:NA)-(y:NA))=0 := hh a
  have hl := congrArg (NonunitalNormMaps.quotientMap U j) hha.1
  have hr := congrArg (NonunitalNormMaps.quotientMap U j) hha.2
  change (NonunitalNormMaps.quotientMap U j (x:NA)-NonunitalNormMaps.quotientMap U j (y:NA))*normInclusion U (j a)=0 ∧
    normInclusion U (j a)*(NonunitalNormMaps.quotientMap U j (x:NA)-NonunitalNormMaps.quotientMap U j (y:NA))=0
  constructor
  · simpa only [map_mul,map_sub,map_zero,NonunitalNormMaps.quotientMap_inclusion] using hl
  · simpa only [map_mul,map_sub,map_zero,NonunitalNormMaps.quotientMap_inclusion] using hr

def factorNonunital : CentralSequenceAlgebra (A := A) U →⋆ₙₐ[ℂ] RelativeQuotient U j where
  toFun := Quotient.lift (fun x => RelativeCentral.quotientMap (inclusion U j) (centralMap U j x))
    (fun x y h => centralMap_quotient_eq U j x y (Quotient.sound h))
  map_zero' := by change RelativeCentral.quotientMap _ (centralMap U j 0)=0; rw [map_zero,map_zero]
  map_add' x y := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    obtain ⟨y,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) y
    change RelativeCentral.quotientMap _ (centralMap U j (x+y))=_
    rw [map_add,map_add]; rfl
  map_mul' x y := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    obtain ⟨y,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) y
    change RelativeCentral.quotientMap _ (centralMap U j (x*y))=_
    rw [map_mul,map_mul]; rfl
  map_smul' c x := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    change RelativeCentral.quotientMap _ (centralMap U j (c • x))=_
    rw [map_smul,map_smul]; rfl
  map_star' x := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    change RelativeCentral.quotientMap _ (centralMap U j (star x))=_
    rw [map_star,map_star]; rfl

@[simp] lemma factorNonunital_mk (x : normCentralizer (A := A) U) :
    factorNonunital U j (centralSequenceQuotient U x)=
      RelativeCentral.quotientMap (inclusion U j) (centralMap U j x) := rfl

variable [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ)≤atTop)]
lemma factorNonunital_one : factorNonunital U j 1=1 := by
  change RelativeCentral.quotientMap (inclusion U j) (centralMap U j (centralLocalUnit U))=1
  rw [←map_one (RelativeCentral.quotientMap (inclusion U j))]
  apply (RelativeCentral.quotient_eq_iff _ _ _).mpr
  intro a
  have hl := congrArg (NonunitalNormMaps.quotientMap U j) (centralLocalUnit_mul U a)
  have hr := congrArg (NonunitalNormMaps.quotientMap U j) (mul_centralLocalUnit U a)
  simp only [map_mul,NonunitalNormMaps.quotientMap_inclusion] at hl hr
  change (NonunitalNormMaps.quotientMap U j ((centralLocalUnit (A := A) U : normCentralizer (A := A) U):NA)-1)*normInclusion U (j a)=0 ∧
    normInclusion U (j a)*(NonunitalNormMaps.quotientMap U j ((centralLocalUnit (A := A) U : normCentralizer (A := A) U):NA)-1)=0
  constructor
  · rw [sub_mul,one_mul,hl,sub_self]
  · rw [mul_sub,mul_one,hr,sub_self]

def factor : CentralSequenceAlgebra (A := A) U →⋆ₐ[ℂ] RelativeQuotient U j where
  toFun := factorNonunital U j
  map_zero' := map_zero _
  map_one' := factorNonunital_one U j
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,factorNonunital_one,Algebra.algebraMap_eq_smul_one]

@[simp] lemma factor_mk (x : normCentralizer (A := A) U) :
    factor U j (centralSequenceQuotient U x)=
      RelativeCentral.quotientMap (inclusion U j) (centralMap U j x) := rfl

end NonunitalRelative

end
end

end OAI
