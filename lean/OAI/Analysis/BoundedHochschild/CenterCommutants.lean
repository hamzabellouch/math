import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CentralQuantization

namespace OAI

/-! Central structure of matrix commutants. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open BoundedHochschild HochschildComparison FinitePathMain HochschildCentralQuantization
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {n : ℕ} (E : MatrixSystem M n)

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_commutant_coe (b : E.commutant) (hb : ∀ x : E.commutant, Commute b x) :
    ∀ x : M, Commute (b:M) x := by
  intro x
  rw [← E.reconstruct x]
  apply Commute.sum_right
  intro i hi
  apply Commute.sum_right
  intro j hj
  exact (b.property i j).mul_right (show Commute (b:M) (E.coefficient i j x) from
    congrArg (fun z : E.commutant => (z:M)) (hb ⟨_,E.coefficient_mem i j x⟩).eq)

lemma deflate_abelian (i : Fin n) {q : E.commutant} (hq : AbelianProjection q) :
    AbelianProjection (E.entry i i*(q:M)) := by
  have hqM : IsStarProjection (q:M) :=
    ⟨congrArg (fun z : E.commutant => (z:M)) hq.1.isIdempotentElem.eq,
      congrArg (fun z : E.commutant => (z:M)) hq.1.isSelfAdjoint.star_eq⟩
  let p := E.entry i i*(q:M)
  have hp : IsStarProjection p := (E.diagonal_proj i).mul hqM (q.property i i).symm
  have hpe : p ≤ E.entry i i := (hp.le_iff_mul_eq_right (E.diagonal_proj i)).mpr
    (by dsimp [p]; rw [← mul_assoc,(E.diagonal_proj i).isIdempotentElem.eq])
  have hep : E.entry i i*p=p := (hp.le_iff_mul_eq_right (E.diagonal_proj i)).mp hpe
  have hpe' : p*E.entry i i=p := (hp.le_iff_mul_eq_left (E.diagonal_proj i)).mp hpe
  have hcoef (a : M) : E.coefficient i i (p*a*p)=(q:M)*E.coefficient i i a*(q:M) := by
    rw [← E.coefficient_of_commutant i q.property, E.coefficient_mul,E.coefficient_mul]
    change E.coefficient i i (p*a*p)=E.coefficient i i ((p*E.entry i i*a)*E.entry i i*p)
    rw [hpe',mul_assoc (p*a),hep]
  refine ⟨hp,?_⟩
  intro a b
  have hab := congrArg (fun x : E.commutant => (x:M))
    (hq.2 ⟨_,E.coefficient_mem i i a⟩ ⟨_,E.coefficient_mem i i b⟩).eq
  change ((q:M)*E.coefficient i i a*(q:M))*((q:M)*E.coefficient i i b*(q:M))=
    ((q:M)*E.coefficient i i b*(q:M))*((q:M)*E.coefficient i i a*(q:M)) at hab
  rw [← hcoef,← hcoef,E.coefficient_mul,E.coefficient_mul] at hab
  have hleft (x : M) : E.entry i i*(p*x*p)=p*x*p := by
    calc
      _ = (E.entry i i*p)*x*p := by simp only [mul_assoc]
      _ = _ := by rw [hep]
  have hright (x : M) : (p*x*p)*E.entry i i=p*x*p := by
    calc
      _ = (p*x)*(p*E.entry i i) := by simp only [mul_assoc]
      _ = _ := by rw [hpe']
  rw [hright,hright] at hab
  have hh := congrArg (fun x : M => E.entry i i*x*E.entry i i) hab
  rw [E.coefficient_corner,E.coefficient_corner] at hh
  change (p*a*p)*(p*b*p)=(p*b*p)*(p*a*p)
  have hreduce (x y : M) : E.entry i i*((p*x*p)*(p*y*p))*E.entry i i=(p*x*p)*(p*y*p) := by
    rw [← mul_assoc (E.entry i i),hleft,mul_assoc (p*x*p),hright]
  simpa only [hreduce] using hh

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
lemma commutant_typeII1 (hn : 0<n) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hII : TypeII1 M) : TypeII1 E.commutant := by
  constructor
  · intro a ha
    apply Subtype.ext
    exact hII.1 (a:M) (congrArg (fun x : E.commutant => (x:M)) ha)
  · intro z hz
    by_contra hzne
    obtain ⟨q,hq,_hqz,hq0⟩ := hz.2 z hz.1 le_rfl hzne
    have hab := E.deflate_abelian ⟨0,hn⟩ hq
    have hh := HochschildTypeII.no_abelian_projection e τ hτ htr hfaith hII hab
    have hc := E.coefficient_of_commutant ⟨0,hn⟩ q.property
    rw [hh,E.coefficient_nil] at hc
    exact hq0 (Subtype.ext hc.symm)

omit [StarOrderedRing M] in
lemma centrallyCentered_expectation (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    {x : M} (hx : CentrallyCentered τ x) :
    CentrallyCentered (E.commutantTrace τ) ⟨E.expectation x,E.commute_expectation x⟩ := by
  intro z hz
  have hzM := E.central_commutant_coe z hz
  change τ ((z:M)*E.expectation x)=0
  have he : (z:M)*E.expectation x=E.expectation ((z:M)*x) := by
    change (z:M)*((n:ℂ)⁻¹ • ∑ i,∑ j,E.entry i j*x*E.entry j i)=_
    simp only [E.expectation_apply,mul_smul_comm,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc,← mul_assoc,(hzM (E.entry i j)).eq]
    simp only [mul_assoc]
  rw [he,E.trace_expectation τ htr hn]
  exact hx z hzM

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
