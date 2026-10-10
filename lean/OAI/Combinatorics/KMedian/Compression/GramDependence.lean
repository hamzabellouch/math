import Mathlib

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

theorem gram_det_ne_zero (A : Matrix R C ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ))) :
    (A.transpose*A).det ≠ 0 := by
  intro hz
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hzero : A*ᵥv=0 := by
    have hh := congrArg (dotProduct v) hker
    rw [← mulVec_mulVec,dotProduct_mulVec,dotProduct_zero,vecMul_transpose,
      dotProduct_self_eq_zero] at hh
    exact hh
  have hlin : Function.Injective ((fun r c => (A r c:ℚ)) *ᵥ ·) :=
    Matrix.mulVec_injective_iff.mpr hi
  have hcast : (fun r c => (A r c:ℚ))*ᵥ(fun c => (v c:ℚ))=0 := by
    ext r
    have hh := congrFun hzero r
    change (∑ c, A r c*v c)=0 at hh
    change (∑ c, (A r c:ℚ)*(v c:ℚ))=0
    exact_mod_cast hh
  have hvQ := hlin (hcast.trans (mulVec_zero _).symm)
  apply hv
  ext c
  have hh := congrFun hvQ c
  change (v c:ℚ)=0 at hh
  change v c=0
  exact_mod_cast hh

theorem gram_span_relation (A : Matrix R C ℤ) (w : R → ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ)))
    (hc : (fun r => (w r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c => fun r => (A r c:ℚ)))) :
    let B := A.transpose*A
    let z := B.cramer (A.transpose*ᵥw)
    ∀ r, (A*ᵥz) r=B.det*w r := by
  let AQ : Matrix R C ℚ := fun r c => A r c
  have hc' : (fun r => (w r:ℚ)) ∈ LinearMap.range AQ.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  obtain ⟨x,hx⟩ := hc'
  change AQ*ᵥx=(fun r => (w r:ℚ)) at hx
  let B := A.transpose*A
  let z := B.cramer (A.transpose*ᵥw)
  have hz := Matrix.mulVec_cramer B (A.transpose*ᵥw)
  have hdet : B.det ≠ 0 := gram_det_ne_zero A hi
  have hB : Function.Injective ((fun c d => (B c d:ℚ))*ᵥ ·) := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (((Int.castRingHom ℚ).mapMatrix B).det)
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    apply isUnit_iff_ne_zero.mpr
    change (B.det:ℚ) ≠ 0
    exact_mod_cast hdet
  have hBcast : (fun c d => (B c d:ℚ))=AQ.transpose*AQ := by
    exact Matrix.map_mul (L:=A.transpose) (M:=A) (f:=Int.castRingHom ℚ)
  have hzQ : (AQ.transpose*AQ)*ᵥ(fun c => (z c:ℚ))=(B.det:ℚ) •
      (AQ.transpose*ᵥ(fun r => (w r:ℚ))) := by
    rw [← hBcast]
    ext c
    have hh := congrFun hz c
    simp only [mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at hh ⊢
    change (∑ d, (B c d:ℚ)*(z d:ℚ))=(B.det:ℚ)*∑ r, (A r c:ℚ)*(w r:ℚ)
    change (∑ d, B c d*z d)=B.det*∑ r, A r c*w r at hh
    exact_mod_cast hh
  have he : (fun c => (z c:ℚ))=(B.det:ℚ) • x := by
    apply hB
    change ((fun c d => (B c d:ℚ))*ᵥ(fun c => (z c:ℚ))) =
      (fun c d => (B c d:ℚ))*ᵥ((B.det:ℚ) • x)
    rw [hBcast,hzQ,mulVec_smul,← mulVec_mulVec,hx]
  change ∀ r, (A*ᵥz) r=B.det*w r
  intro r
  have heq : (AQ*ᵥ(fun c => (z c:ℚ))) r=(B.det:ℚ)*(w r:ℚ) := by
    rw [he,mulVec_smul,hx]
    rfl
  simp only [mulVec,dotProduct,AQ] at heq ⊢
  exact_mod_cast heq

end MetricKMedian.Compression

end OAI
