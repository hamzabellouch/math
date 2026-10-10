import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.Frames

namespace OAI

/-! Comparison with abelian projections. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma abelian_orthogonal_mul {p r t : M} (hp : AbelianProjection p)
    (hr : IsStarProjection r) (ht : IsStarProjection t) (hrp : r ≤ p) (htp : t ≤ p)
    (hrt : r*t=0) (a : M) : r*a*t=0 := by
  have hpr := (hr.le_iff_mul_eq_right hp.1).mp hrp
  have hrp' := (hr.le_iff_mul_eq_left hp.1).mp hrp
  have hpt := (ht.le_iff_mul_eq_right hp.1).mp htp
  have he : p*r*p=r := by rw [hpr,hrp']
  have hc := hp.2 r a
  rw [he] at hc
  calc
    r*a*t = r*(p*a*p)*t := by rw [← mul_assoc,← mul_assoc,hrp',mul_assoc,mul_assoc,hpt,← mul_assoc]
    _ = (p*a*p)*(r*t) := by rw [hc.eq,mul_assoc]
    _ = 0 := by rw [hrt,mul_zero]

include e hτ htr hfaith in

theorem abelian_subequivalent_full {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q)
    (hfull : ∀ r : M, IsStarProjection r → r ≠ 0 → ∃ a : M, q*a*r ≠ 0) :
    ∃ v : PartialIso M, v.initial=p ∧ v.final ≤ q := by
  classical
  let L := HochschildSakai.mul_hasPreadjoint e
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hzero : (0 : PartialIso M) ∈ S := by
    exact ⟨by simpa using hp.1.nonneg,by simpa using hq.nonneg⟩
  obtain ⟨v,_hv0,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsq,hsup⟩ := PartialIso.chain_upper e τ L hτ htr hfaith hp.1 hq
      c hchain ⟨y,hy⟩ (fun w hw => hc hw)
    exact ⟨s,⟨hsp,hsq⟩,hsup⟩) 0 hzero
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  have hr := (v.initial_proj.le_iff_sub hp.1).mp hvp
  have hs := (v.final_proj.le_iff_sub hq).mp hvq
  have hir : v.initial*(p-v.initial)=0 := by
    rw [mul_sub,(v.initial_proj.le_iff_mul_eq_left hp.1).mp hvp,
      v.initial_proj.isIdempotentElem.eq,sub_self]
  have hvr : ∀ a : M, v.final*a*(p-v.initial)=0 := by
    intro a
    have h := abelian_orthogonal_mul hp v.initial_proj hr hvp
      (sub_le_self _ v.initial_proj.nonneg) hir (star (v:M)*a)
    calc
      v.final*a*(p-v.initial) = (v:M)*(v.initial*(star (v:M)*a)*(p-v.initial)) := by
        simp only [← mul_assoc,v.mul_initial,PartialIso.final]
      _ = 0 := by rw [h,mul_zero]
  refine ⟨v,?_,hvq⟩
  by_contra hi
  obtain ⟨a,ha⟩ := hfull (p-v.initial) hr (sub_ne_zero.mpr (Ne.symm hi))
  have hba : (q-v.final)*a*(p-v.initial) ≠ 0 := by
    simpa only [sub_mul,hvr a,sub_zero] using ha
  obtain ⟨w,hw0,hwi,hwf⟩ := partialIso_of_nonzero_corner e hs hr
    ((q-v.final)*a*(p-v.initial)) hba
    (by rw [← mul_assoc,← mul_assoc,hs.isIdempotentElem.eq])
    (by rw [mul_assoc,hr.isIdempotentElem.eq])
  have hio := projection_orthogonal_of_le_sub hp.1 v.initial_proj w.initial_proj hvp hwi
  have hfo := projection_orthogonal_of_le_sub hq v.final_proj w.final_proj hvq hwf
  have hmem : v.orthogonalSum w hio hfo ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial+w.initial ≤ v.initial+(p-v.initial) := add_le_add_right hwi _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final+w.final ≤ v.final+(q-v.final) := add_le_add_right hwf _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hio hfo
  have he := le_antisymm (hmax.2 hmem hle) hle
  have hh : (v:M)+w=v := congrArg (fun z : PartialIso M => (z:M)) he
  exact hw0 (add_eq_left.mp hh)

include e hτ htr hfaith in
lemma abelian_trace_le_full {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q)
    (hfull : ∀ r : M, IsStarProjection r → r ≠ 0 → ∃ a : M, q*a*r ≠ 0) :
    (τ p).re ≤ (τ q).re := by
  obtain ⟨v,hv,hvq⟩ := abelian_subequivalent_full e τ hτ htr hfaith hp hq hfull
  have ht : τ p=τ v.final := by rw [← hv]; exact htr _ _
  rw [ht]
  exact Complex.re_le_re (τ.monotone hvq)

end HochschildTypeII

end

end OAI
