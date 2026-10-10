import OAI.Geometry.SurfaceImmersion.Geometry.CurveTransverseVector

namespace OAI

/-! An explicit invertible three-dimensional frame along a regular curve. -/
noncomputable section
open Set Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def curveNormalLinear (v a : Fin 3 → ℝ) : (Base × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.snd ℝ Base ℝ).smulRight v +
    ((ContinuousLinearMap.proj (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ Base ℝ)).smulRight a +
    ((ContinuousLinearMap.proj (1 : Fin 2)).comp (ContinuousLinearMap.fst ℝ Base ℝ)).smulRight (v ⨯₃ a)

lemma curveNormalLinear_apply (v a : Fin 3 → ℝ) (z : Base × ℝ) :
    curveNormalLinear v a z = z.2 • v+z.1 0 • a+z.1 1 • (v ⨯₃ a) := rfl

lemma curveNormalLinear_bijective {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) :
    Function.Bijective (curveNormalLinear v a) := by
  have hli := curve_transverse_vector_independent hv ha
  have hw := curve_transverse_cross_ne_zero hv ha
  have hwv : (v ⨯₃ a) ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact dot_self_cross v a
  have hwa : (v ⨯₃ a) ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact dot_cross_self v a
  have hww : (v ⨯₃ a) ⬝ᵥ (v ⨯₃ a) ≠ 0 := (dotProduct_self_eq_zero).not.mpr hw
  have hz : ∀ z : Base × ℝ, curveNormalLinear v a z = 0 → z = 0 := by
    intro z h
    have hd := congrArg (fun w => (v ⨯₃ a) ⬝ᵥ w) h
    rw [curveNormalLinear_apply] at hd
    simp only [dotProduct_add,dotProduct_smul,hwv,hwa,smul_eq_mul,mul_zero,zero_add,dotProduct_zero] at hd
    have hz1 : z.1 1 = 0 := (mul_eq_zero.mp hd).resolve_right hww
    have hsum : z.2 • v+z.1 0 • a = 0 := by
      simpa only [curveNormalLinear_apply,hz1,zero_smul,add_zero] using h
    obtain ⟨hz2,hz0⟩ := (LinearIndependent.pair_iff.mp hli) z.2 (z.1 0) hsum
    apply Prod.ext
    · ext i
      fin_cases i
      · exact hz0
      · exact hz1
    · exact hz2
  have hi : Function.Injective (curveNormalLinear v a) := by
    intro z w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,h,sub_self]
  refine ⟨hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (curveNormalLinear v a).toLinearMap) _).mp hi
  simp [Base]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
