import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerBasic

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))

lemma normNull_tracialNull (x : lp (fun _ : ℕ => A) ∞)
    (hx : x ∈ NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U) : q x=0 := by
  change (familyNullIdeal T (U : Filter ℕ)).quotientMap x = 0
  rw [familyQuotientMap_eq_zero]
  exact squeeze_zero (fun n => familyTwoNorm_nonneg T (x n))
    (fun n => familyTwoNorm_le_norm T (x n)) hx

def normToTracial : N →⋆ₙₐ[ℂ] FamilyUltrapower T U where
  toFun := Quotient.lift q (by
    intro x y h
    change (NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U).quotientRel x y at h
    rw [Submodule.quotientRel_def] at h
    have he := normNull_tracialNull U (x-y) h
    rw [map_sub,sub_eq_zero] at he
    exact he)
  map_zero' := map_zero q
  map_add' x y := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    obtain ⟨y,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective y
    exact map_add q x y
  map_mul' x y := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    obtain ⟨y,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective y
    exact map_mul q x y
  map_smul' c x := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    exact map_smul q c x
  map_star' x := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    exact map_star q x

@[simp] lemma normToTracial_mk (x : lp (fun _ : ℕ => A) ∞) :
    normToTracial (A := A) U (NormUltra.QuotientAlgebra.mk U x)=q x := rfl

lemma normToTracial_surjective : Function.Surjective (normToTracial (A := A) U) := by
  intro x
  obtain ⟨y,rfl⟩ := (familyNullIdeal T (U : Filter ℕ)).quotientMap_surjective x
  exact ⟨NormUltra.QuotientAlgebra.mk U y,rfl⟩

end DirectComparison

end
end

end OAI
