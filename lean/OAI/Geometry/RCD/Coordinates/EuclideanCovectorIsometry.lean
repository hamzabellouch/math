import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicModel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # Unit orthogonal covectors form Euclidean isometric coordinates -/

open InnerProductSpace
open scoped RealInnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_isometry_of_covector_norms {n : ℕ}
    (L : Fin n → Euclidean n →L[ℝ] ℝ)
    (hL : ∀ i, ‖L i‖^2 = 1)
    (hadd : ∀ i j, i ≠ j → ‖L i+L j‖^2 = 2) :
    ∃ T : Euclidean n ≃ₗᵢ[ℝ] Euclidean n, ∀ x i, T x i = L i x := by
  classical
  let a := fun i => (InnerProductSpace.toDual ℝ (Euclidean n)).symm (L i)
  have hnorm (i : Fin n) : ‖a i‖^2 = 1 := by
    simpa only [a,LinearIsometryEquiv.norm_map] using hL i
  have hsum (i j : Fin n) (hij : i ≠ j) : ‖a i+a j‖^2 = 2 := by
    simpa only [a,← map_add,LinearIsometryEquiv.norm_map] using hadd i j hij
  have horth : Orthonormal ℝ a := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i=j
    · subst j
      simpa only [ite_true,real_inner_self_eq_norm_sq] using hnorm i
    · rw [ite_eq_right_iff.mpr (fun h => (hij h).elim)]
      nlinarith [norm_add_sq_real (a i) (a j),hnorm i,hnorm j,hsum i j hij]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range a) := by
    rw [horth.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)]
  let b := OrthonormalBasis.mk horth hspan
  refine ⟨b.repr,?_⟩
  intro x i
  rw [b.repr_apply_apply]
  have hb : b i = a i := congrFun (OrthonormalBasis.coe_mk horth hspan) i
  rw [hb]
  exact InnerProductSpace.toDual_symm_apply

end RegularPointCoordinates

end

end OAI
