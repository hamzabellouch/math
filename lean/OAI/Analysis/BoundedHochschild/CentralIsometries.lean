import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CentralComparison

namespace OAI

/-! Central cuts and extensions of partial isometries. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildComparison FinitePathMain HochschildMatrixSystems
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_mul_pair {z : M} (hz : CentralProjection z) (a b : M) :
    (z*a)*(z*b)=z*(a*b) := by
  calc
    _ = z*(a*z)*b := by simp only [mul_assoc]
    _ = z*(z*a)*b := by rw [← (hz.2 a).eq]
    _ = z*(a*b) := by rw [← mul_assoc z z,hz.1.isIdempotentElem.eq,mul_assoc]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_mul_sandwich {z : M} (hz : CentralProjection z) (a : M) : z*a*z=z*a := by
  rw [mul_assoc,← (hz.2 a).eq,← mul_assoc,hz.1.isIdempotentElem.eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralProjection_mul {z t : M} (hz : CentralProjection z) (ht : CentralProjection t) :
    CentralProjection (z*t) := ⟨hz.1.mul ht.1 (hz.2 t),fun a => (hz.2 a).mul_left (ht.2 a)⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralProjection_one_sub {z : M} (hz : CentralProjection z) : CentralProjection (1-z) :=
  ⟨hz.1.one_sub,fun a => (Commute.one_left a).sub_left (hz.2 a)⟩

namespace PartialIso

def centralCut (v : PartialIso M) (z : M) (hz : CentralProjection z) : PartialIso M where
  val := z*v
  mul_star_mul := by
    have hs : star (z*(v:M))=z*star (v:M) := by
      rw [star_mul,hz.1.isSelfAdjoint.star_eq,← (hz.2 (star (v:M))).eq]
    rw [hs,central_mul_pair hz,central_mul_pair hz,v.mul_star_mul]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCut_coe (v : PartialIso M) (z : M) (hz : CentralProjection z) :
    ((centralCut v z hz : PartialIso M):M)=z*(v:M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCut_initial (v : PartialIso M) (z : M) (hz : CentralProjection z) :
    (centralCut v z hz).initial=z*v.initial := by
  change star (z*(v:M))*(z*(v:M))=z*(star (v:M)*(v:M))
  rw [star_mul,hz.1.isSelfAdjoint.star_eq,← (hz.2 (star (v:M))).eq,central_mul_pair hz]

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCut_final (v : PartialIso M) (z : M) (hz : CentralProjection z) :
    (centralCut v z hz).final=z*v.final := by
  change (z*(v:M))*star (z*(v:M))=z*((v:M)*star (v:M))
  rw [star_mul,hz.1.isSelfAdjoint.star_eq,← (hz.2 (star (v:M))).eq,central_mul_pair hz]

lemma centralCut_initial_le (v : PartialIso M) (z : M) (hz : CentralProjection z) :
    (centralCut v z hz).initial ≤ v.initial := by
  apply ((centralCut v z hz).initial_proj.le_iff_mul_eq_left v.initial_proj).mpr
  rw [centralCut_initial,mul_assoc,v.initial_proj.isIdempotentElem.eq]

lemma centralCut_final_le (v : PartialIso M) (z : M) (hz : CentralProjection z) :
    (centralCut v z hz).final ≤ v.final := by
  apply ((centralCut v z hz).final_proj.le_iff_mul_eq_left v.final_proj).mpr
  rw [centralCut_final,mul_assoc,v.final_proj.isIdempotentElem.eq]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in

theorem unitary_extension (v : PartialIso M) :
    ∃ u : unitary M, (u:M)*v.initial=v ∧ (u:M)*v.initial*star (u:M)=v.final := by
  have hcompl : ∀ z : M, CentralProjection z → τ (z*(1-v.initial))=τ (z*(1-v.final)) := by
    intro z hz
    rw [mul_sub,mul_sub,map_sub,map_sub,central_weighted_trace_partialIso τ htr v z hz.2]
  obtain ⟨w,hwi,hwf⟩ := subequivalent_of_central_trace_le e τ hτ htr hfaith
    v.initial_proj.one_sub v.final_proj.one_sub
    (fun z hz => le_of_eq (congrArg Complex.re (hcompl z hz)))
  have hwf' : w.final=1-v.final := by
    apply le_antisymm hwf
    apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
      v.final_proj.one_sub w.final_proj (Or.inr hwf)
    have hwtr : τ w.initial=τ w.final := htr _ _
    rw [← hwtr,hwi,map_sub,map_sub]
    have hvtr : τ v.initial=τ v.final := htr _ _
    rw [hvtr]
  have hi : v.initial*w.initial=0 := by
    rw [hwi,mul_sub,mul_one,v.initial_proj.isIdempotentElem.eq,sub_self]
  have hf : v.final*w.final=0 := by
    rw [hwf',mul_sub,mul_one,v.final_proj.isIdempotentElem.eq,sub_self]
  let s := v.orthogonalSum w hi hf
  have hsi : s.initial=1 := by rw [PartialIso.orthogonalSum_initial,hwi,add_sub_cancel]
  have hsf : s.final=1 := by rw [PartialIso.orthogonalSum_final,hwf',add_sub_cancel]
  let u : unitary M := ⟨s,⟨hsi,hsf⟩⟩
  have huv : (u:M)*v.initial=v := (v.le_orthogonalSum w hi hf).2
  refine ⟨u,huv,?_⟩
  have hvstar : v.initial*star (u:M)=star (v:M) := by
    simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq] using congrArg star huv
  calc
    (u:M)*v.initial*star (u:M) = ((u:M)*v.initial)*(v.initial*star (u:M)) := by
      rw [← mul_assoc,mul_assoc (u:M) v.initial v.initial,v.initial_proj.isIdempotentElem.eq]
    _ = v.final := by rw [huv,hvstar]; rfl
end PartialIso

end HochschildCentralComparison

end

end OAI
