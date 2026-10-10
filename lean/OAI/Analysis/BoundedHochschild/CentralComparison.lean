import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.Frames
import OAI.Analysis.BoundedHochschild.CentralSeparation

namespace OAI

/-! Comparison of projections using central weighted traces. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildRigidity HochschildComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htr : t ≤ p-r) : r*t=0 := by
  have hpr := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]

include e hτ htr hfaith in
lemma exists_maximal_partialIso {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ p ∧ v.final ≤ q ∧
      ∀ a : M, (q-v.final)*a*(p-v.initial)=0 := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.nonneg,by simpa using hq.nonneg⟩
  obtain ⟨v,_hz,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsq,hsup⟩ := PartialIso.chain_upper e τ (HochschildSakai.mul_hasPreadjoint e)
      hτ htr hfaith hp hq c hchain ⟨y,hy⟩ (fun z hz => hc hz)
    exact ⟨s,⟨hsp,hsq⟩,hsup⟩) 0 hz
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  refine ⟨v,hvp,hvq,fun a => ?_⟩
  by_contra ha
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  obtain ⟨w,hw0,hwp,hwq⟩ := partialIso_of_nonzero_corner e hq' hp'
    ((q-v.final)*a*(p-v.initial)) ha
    (by rw [← mul_assoc,← mul_assoc,hq'.isIdempotentElem.eq])
    (by rw [mul_assoc,hp'.isIdempotentElem.eq])
  have hi := orthogonal_of_le_sub hp v.initial_proj w.initial_proj hvp hwp
  have hf := orthogonal_of_le_sub hq v.final_proj w.final_proj hvq hwq
  have hs : v.orthogonalSum w hi hf ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial+w.initial ≤ v.initial+(p-v.initial) := add_le_add_right hwp _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final+w.final ≤ v.final+(q-v.final) := add_le_add_right hwq _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hi hf
  have he := le_antisymm (hmax.2 hs hle) hle
  have hvw : (v : M)+w=v := congrArg (fun z : PartialIso M => (z : M)) he
  exact hw0 (add_eq_left.mp hvw)

include e hτ htr hfaith in

theorem central_comparison {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ (z : M) (v : PartialIso M), CentralProjection z ∧ v.initial ≤ p ∧ v.final ≤ q ∧
      z*v.final=z*q ∧ (1-z)*v.initial=(1-z)*p := by
  obtain ⟨v,hvp,hvq,horth⟩ := exists_maximal_partialIso e τ hτ htr hfaith hp hq
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  have horth' : ∀ a : M, (p-v.initial)*a*(q-v.final)=0 := by
    intro a
    have hh := congrArg star (horth (star a))
    simpa only [star_mul,star_star,star_zero,hp'.isSelfAdjoint.star_eq,
      hq'.isSelfAdjoint.star_eq,mul_assoc] using hh
  obtain ⟨z,hz,hpz,hzq⟩ := central_separator e τ hτ htr hfaith hp' hq' horth'
  have hzp : z*(p-v.initial)=p-v.initial := (hp'.le_iff_mul_eq_right hz.1).mp hpz
  refine ⟨z,v,hz,hvp,hvq,?_,?_⟩
  · exact (sub_eq_zero.mp (by simpa only [mul_sub] using hzq)).symm
  · have hh : (1-z)*(p-v.initial)=0 := by rw [sub_mul,one_mul,hzp,sub_self]
    exact (sub_eq_zero.mp (by simpa only [mul_sub] using hh)).symm

omit [StarOrderedRing M] in
include htr in
lemma central_weighted_trace_partialIso (v : PartialIso M) (z : M)
    (hz : ∀ a : M, Commute z a) : τ (z*v.initial)=τ (z*v.final) := by
  change τ (z*(star (v:M)*(v:M)))=τ (z*((v:M)*star (v:M)))
  calc
    _ = τ ((z*star (v:M))*(v:M)) := by rw [mul_assoc]
    _ = τ ((v:M)*(z*star (v:M))) := htr _ _
    _ = τ (z*((v:M)*star (v:M))) := by rw [← mul_assoc,← (hz (v:M)).eq,mul_assoc]

include e hτ htr hfaith in

theorem subequivalent_of_central_trace_le {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (ht : ∀ z : M, CentralProjection z → (τ (z*p)).re ≤ (τ (z*q)).re) :
    ∃ v : PartialIso M, v.initial=p ∧ v.final ≤ q := by
  obtain ⟨v,hvp,hvq,horth⟩ := exists_maximal_partialIso e τ hτ htr hfaith hp hq
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  have horth' : ∀ a : M, (p-v.initial)*a*(q-v.final)=0 := by
    intro a
    have hh := congrArg star (horth (star a))
    simpa only [star_mul,star_star,star_zero,hp'.isSelfAdjoint.star_eq,
      hq'.isSelfAdjoint.star_eq,mul_assoc] using hh
  obtain ⟨z,hz,hpz,hzq⟩ := central_separator e τ hτ htr hfaith hp' hq' horth'
  have hzp : z*(p-v.initial)=p-v.initial := (hp'.le_iff_mul_eq_right hz.1).mp hpz
  have ht' := ht z hz
  have he := central_weighted_trace_partialIso τ htr v z hz.2
  have hzqt : τ (z*q)=τ (z*v.final) := by
    have hh := congrArg τ hzq
    simpa only [mul_sub,map_sub,map_zero,sub_eq_zero] using hh
  have hzero : τ (p-v.initial)=0 := by
    apply Complex.ext
    · change (τ (p-v.initial)).re=0
      have heq : (τ (p-v.initial)).re=(τ (z*p)).re-(τ (z*v.initial)).re := by
        rw [← hzp,mul_sub,map_sub,Complex.sub_re]
      have hn := Complex.re_le_re (τ.map_nonneg hp'.nonneg)
      change 0 ≤ (τ (p-v.initial)).re at hn
      rw [hzqt,← he] at ht'
      rw [heq]
      linarith
    · exact (τ.map_nonneg hp'.nonneg).2.symm
  have hpzero : p-v.initial=0 := hfaith _ (by
    simpa only [hp'.isSelfAdjoint.star_eq,hp'.isIdempotentElem.eq] using hzero)
  exact ⟨v,(sub_eq_zero.mp hpzero).symm,hvq⟩

include e hτ htr hfaith in
theorem equivalent_of_central_trace_eq {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (ht : ∀ z : M, CentralProjection z → τ (z*p)=τ (z*q)) :
    ∃ v : M, star v*v=p ∧ v*star v=q := by
  obtain ⟨v,hv,hvq⟩ := subequivalent_of_central_trace_le e τ hτ htr hfaith hp hq
    (fun z hz => le_of_eq (congrArg Complex.re (ht z hz)))
  have he : τ v.initial=τ v.final := htr _ _
  have ht1 : τ p=τ q := by
    simpa only [one_mul] using ht 1 ⟨IsStarProjection.one M,fun a => Commute.one_left a⟩
  have hback : q ≤ v.final := by
    apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith hq v.final_proj
      (Or.inr hvq)
    rw [← he,hv,ht1]
  exact ⟨v,hv,le_antisymm hvq hback⟩

end HochschildCentralComparison

end

end OAI
