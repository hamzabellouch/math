import Mathlib
import OAI.Analysis.FreeWords.Bicommutant
import OAI.Analysis.FreeWords.PolarGeometry

namespace OAI

noncomputable section

namespace UniversalStrongKK

open scoped InnerProductSpace

noncomputable section

end

end UniversalStrongKK

namespace KKPolarSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKPolarSupport

namespace KKPolarSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem polarOp_ker (a S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (x : H) (hx : S x = 0) :
    polarOp a S x = 0 := by
  have hxorth : x ∈ (closedRange S)ᗮ := by
    rw [closedRange, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    rintro y ⟨z, rfl⟩
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS]
    change ⟪z, S x⟫_ℂ = 0
    rw [hx, inner_zero_right]
  have hp := ((closedRange S).starProjection_apply_eq_zero_iff).mpr hxorth
  have hp' : (closedRange S).orthogonalProjectionOnto x = 0 := Subtype.ext hp
  simp [polarOp, hp']

omit [CompleteSpace H] in
theorem closedRange_invariant (S B : H →L[ℂ] H) (h : Commute B S) :
    ∀ x ∈ closedRange S, B x ∈ closedRange S := by
  change S.toLinearMap.range.topologicalClosure ≤ (closedRange S).comap B.toLinearMap
  apply Submodule.topologicalClosure_minimal
  · rintro y ⟨x, rfl⟩
    change B (S x) ∈ closedRange S
    rw [← mul_apply_eq_comp, h.eq, mul_apply_eq_comp]
    exact Submodule.le_topologicalClosure _ ⟨B x, rfl⟩
  · exact (Submodule.isClosed_topologicalClosure _).preimage B.continuous

theorem polarOp_commute (a S B : H →L[ℂ] H) (hAS : ∀ x, ‖a x‖ = ‖S x‖)
    (hBa : Commute B a) (hBS : Commute B S) (hBsS : Commute (star B) S) :
    Commute B (polarOp a S) := by
  have hp : Commute B (closedRange S).starProjection :=
    UniversalStrongKK.commute_projection_of_invariant _ _
      (closedRange_invariant S B hBS) (closedRange_invariant S (star B) hBsS)
  have heq : ∀ x : closedRange S, B (polarOp a S x) = polarOp a S (B x) := by
    intro z
    refine (closedRangeMap_dense S).induction_on (p := fun z => B (polarOp a S z) = polarOp a S (B z)) z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      change B (polarOp a S (S x)) = polarOp a S (B (S x))
      have hBSx : B (S x) = S (B x) := congrArg (fun T : H →L[ℂ] H => T x) hBS.eq
      rw [polarOp_apply_range a S hAS, hBSx, polarOp_apply_range a S hAS]
      exact congrArg (fun T : H →L[ℂ] H => T x) hBa.eq
  have hVp : ∀ x, polarOp a S ((closedRange S).starProjection x) = polarOp a S x := by
    intro x
    change polarOnRange a S ((closedRange S).orthogonalProjectionOnto ((closedRange S).starProjection x)) =
      polarOnRange a S ((closedRange S).orthogonalProjectionOnto x)
    congr 1
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  ext x
  change B (polarOp a S x) = polarOp a S (B x)
  calc
    B (polarOp a S x) = B (polarOp a S ((closedRange S).starProjection x)) := by rw [hVp]
    _ = polarOp a S (B ((closedRange S).starProjection x)) := heq ((closedRange S).orthogonalProjectionOnto x)
    _ = polarOp a S ((closedRange S).starProjection (B x)) := by
      exact congrArg (polarOp a S) (congrArg (fun T : H →L[ℂ] H => T x) hp.eq)
    _ = polarOp a S (B x) := hVp _

def opAbs (a : H →L[ℂ] H) : H →L[ℂ] H := cfc Real.sqrt (star a*a)

theorem opAbs_selfadjoint (a : H →L[ℂ] H) : IsSelfAdjoint (opAbs a) := IsSelfAdjoint.cfc

theorem opAbs_mul_self (a : H →L[ℂ] H) : opAbs a * opAbs a = star a*a := by
  change cfc Real.sqrt (star a*a) * cfc Real.sqrt (star a*a) = _
  rw [← sq, ← cfc_pow Real.sqrt 2 (star a*a) Real.continuous_sqrt.continuousOn
    (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _))]
  calc
    cfc (fun x : ℝ => Real.sqrt x ^ 2) (star a*a) = cfc (fun x : ℝ => x) (star a*a) := by
      apply cfc_congr
      intro x hx
      exact Real.sq_sqrt (spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) hx)
    _ = star a*a := cfc_id' ℝ _

theorem opAbs_norm (a : H →L[ℂ] H) (x : H) : ‖a x‖ = ‖opAbs a x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right]
  change ⟪x, (star a*a) x⟫_ℂ = ⟪x, (star (opAbs a)*opAbs a) x⟫_ℂ
  rw [(opAbs_selfadjoint a).star_eq, opAbs_mul_self]

theorem opAbs_commute (a B : H →L[ℂ] H) (hBa : Commute B a) (hBas : Commute B (star a)) :
    Commute B (opAbs a) := by
  have habs : Commute (star a*a) B := (hBas.mul_right hBa).symm
  have hself : IsSelfAdjoint (star a*a) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  exact (habs.cfc (by simpa only [hself.star_eq] using habs) Real.sqrt).symm

theorem polar_decomposition (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) (ha : a ∈ M) :
    ∃ v : H →L[ℂ] H, v ∈ M ∧
      v * cfc Real.sqrt (star a*a) = a ∧
      IsStarProjection (star v*v) ∧ v*star v*v = v ∧
      (∀ x : H, cfc Real.sqrt (star a*a) x = 0 → v x = 0) := by
  refine ⟨polarOp a (opAbs a), ?_, polarOp_mul a _ (opAbs_norm a),
    polarOp_projection a _ (opAbs_norm a), polarOp_partial a _ (opAbs_norm a),
    polarOp_ker a _ (opAbs_selfadjoint a)⟩
  rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro B hB
  have hBa : Commute B a := (VonNeumannAlgebra.mem_commutant_iff.mp hB a ha).symm
  have hBas : Commute B (star a) := (VonNeumannAlgebra.mem_commutant_iff.mp hB _ (star_mem ha)).symm
  have hBsa : Commute (star B) a :=
    (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hB) a ha).symm
  have hBsas : Commute (star B) (star a) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hB) _ (star_mem ha)).symm
  exact (polarOp_commute a _ B (opAbs_norm a) hBa (opAbs_commute a B hBa hBas)
    (opAbs_commute a (star B) hBsa hBsas)).eq

end

end KKPolarSupport

namespace KKPolarSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem polar_decomposition_bounds (M : VonNeumannAlgebra H) (a : H →L[ℂ] H)
    (ha : a ∈ M) (p q : H →L[ℂ] H) (_ : IsStarProjection p) (hq : IsStarProjection q)
    (hap : a*p=a) (hqa : q*a=a) :
    ∃ v : H →L[ℂ] H, v ∈ M ∧ v*star v*v=v ∧ v*p=v ∧ q*v=v ∧
      (v=0 → a=0) := by
  obtain ⟨v, hvM, hva, hvi, hv, hk⟩ := polar_decomposition M a ha
  change v*opAbs a=a at hva
  change ∀ x : H, opAbs a x=0 → v x=0 at hk
  have hvp0 : v*(1-p)=0 := by
    ext x
    change v ((1-p) x)=0
    apply hk
    apply norm_eq_zero.mp
    rw [← opAbs_norm]
    have he : a*(1-p)=0 := by rw [mul_sub, mul_one, hap, sub_self]
    exact (congrArg (fun T : H →L[ℂ] H => ‖T x‖) he).trans (by simp)
  have hvp : v*p=v := by
    rw [mul_sub, mul_one] at hvp0
    exact (sub_eq_zero.mp hvp0).symm
  have hsa : opAbs a*star v=star a := by
    simpa only [star_mul, (opAbs_selfadjoint a).star_eq] using congrArg star hva
  have haq : star a*q=star a := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hqa
  have heS : opAbs a*(star v*(1-q))=0 := by
    rw [← mul_assoc, hsa, mul_sub, mul_one, haq, sub_self]
  have heV : (v*star v)*(1-q)=0 := by
    ext x
    change v (star v ((1-q) x))=0
    apply hk
    exact congrArg (fun T : H →L[ℂ] H => T x) heS
  have heV' : (1-q)*(v*star v)=0 := by
    simpa only [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq, star_star, star_zero]
      using congrArg star heV
  have hqv0 : (1-q)*v=0 := by
    calc
      (1-q)*v = (1-q)*(v*star v*v) := by rw [hv]
      _ = ((1-q)*(v*star v))*v := by simp only [mul_assoc]
      _ = 0 := by rw [heV', zero_mul]
  have hqv : q*v=v := by
    rw [sub_mul, one_mul] at hqv0
    exact (sub_eq_zero.mp hqv0).symm
  refine ⟨v,hvM,hv,hvp,hqv,?_⟩
  intro h0
  simpa only [h0, zero_mul] using hva.symm

end

end KKPolarSupport
end

end OAI
