import OAI.Geometry.CylinderCovering.Ruled.LocalDefinitions
import OAI.Geometry.CylinderCovering.Convexity.CompactEigenframes
import OAI.Geometry.CylinderCovering.Convexity.EigenframeBounds

namespace OAI

noncomputable section
open Set
namespace RuledApproximation

lemma positive_eigenvalue_eq_sqrt (A : Plane →L[ℝ] Plane)
    (htr : LinearMap.trace ℝ Plane A.toLinearMap = 0)
    (hdet : LinearMap.det A.toLinearMap < 0) {lam : ℝ} (hlam : 0 < lam)
    (heig : Module.End.HasEigenvalue A.toLinearMap lam) :
    lam = Real.sqrt (-LinearMap.det A.toLinearMap) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly, htr] at heig
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, zero_mul, sub_zero] at heig
  have hs := Real.sq_sqrt (show 0 ≤ -LinearMap.det A.toLinearMap by linarith)
  have hn := Real.sqrt_nonneg (-LinearMap.det A.toLinearMap)
  nlinarith

end RuledApproximation

namespace CylinderCovering.ProductLocal
open RuledApproximation

theorem exists_unit_eigenframe (A : Plane →L[ℝ] Plane)
    (htr : LinearMap.trace ℝ Plane A.toLinearMap = 0)
    (hdet : LinearMap.det A.toLinearMap < 0) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] Plane,
      IsUnitEigenframe A (Real.sqrt (-LinearMap.det A.toLinearMap)) L := by
  have hlam : 0 < Real.sqrt (-LinearMap.det A.toLinearMap) :=
    Real.sqrt_pos.mpr (neg_pos.mpr hdet)
  obtain ⟨hp, hm⟩ := plane_hyperbolic_eigenvalues A.toLinearMap htr hdet
  obtain ⟨M, v, w, hv, hw, hAv, hAw, hM, _, _⟩ := normalized_eigenframe A hlam hp hm
  let L : (ℝ × ℝ) ≃L[ℝ] Plane := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans M
  have hL0 : L (1,0) = v := by simp [L, hM]
  have hL1 : L (0,1) = w := by simp [L, hM]
  refine ⟨L, ?_⟩
  simp only [IsUnitEigenframe, hL0, hL1]
  exact ⟨hv, hw, hAv, hAw⟩

theorem compact_uniform_eigenframe_inverse {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : IsCompact D) {A : X → Plane →L[ℝ] Plane}
    (hA : ContinuousOn A D)
    (htr : ∀ p ∈ D, LinearMap.trace ℝ Plane (A p).toLinearMap = 0)
    (hdet : ∀ p ∈ D, LinearMap.det (A p).toLinearMap < 0) :
    ∃ N : ℝ, 0 < N ∧ ∀ p ∈ D, ∀ lam : ℝ, ∀ L : (ℝ × ℝ) ≃L[ℝ] Plane,
      0 < lam → IsUnitEigenframe (A p) lam L →
      ‖L.symm.toContinuousLinearMap‖ ≤ N ∧ ∀ z : Plane, ‖L.symm z‖ ≤ N * ‖z‖ := by
  obtain ⟨m, B, hm, hB, hbounds⟩ := compact_spectral_envelope hD hA htr hdet
  refine ⟨2*B/m, by positivity, ?_⟩
  intro p hp lam L hlam hL
  have hv0 : L (1,0) ≠ 0 := by
    intro hz
    have hn := hL.1
    rw [hz, norm_zero] at hn
    norm_num at hn
  have heig : Module.End.HasEigenvalue (A p).toLinearMap lam :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hL.2.2.1, hv0⟩
  have heq := positive_eigenvalue_eq_sqrt (A p) (htr p hp) (hdet p hp) hlam heig
  have hml : m ≤ lam := by rw [heq]; exact (hbounds p hp).1
  refine ⟨EigenframeBounds.pair_frame_inverse_opNorm (A p) L hm hml
    (hbounds p hp).2.2 hL.1 hL.2.1 hL.2.2.1 hL.2.2.2, ?_⟩
  exact EigenframeBounds.pair_frame_inverse_bound (A p) L hm hml
    (hbounds p hp).2.2 hL.1 hL.2.1 hL.2.2.1 hL.2.2.2

end CylinderCovering.ProductLocal

end

end OAI
