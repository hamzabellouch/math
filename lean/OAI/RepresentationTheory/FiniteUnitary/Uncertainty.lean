import Mathlib

namespace OAI

namespace CubeShuffle.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]
abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

noncomputable def act (p : Equiv.Perm X) : H X ≃ₗᵢ[ℂ] H X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p

@[simp] lemma act_apply (p : Equiv.Perm X) (v : H X) (x : X) :
    act p v x = v (p⁻¹ x) := rfl

lemma act_single [DecidableEq X] (p : Equiv.Perm X) (x : X) :
    act p (EuclideanSpace.single x (1:ℂ)) = EuclideanSpace.single (p x) 1 := by
  exact EuclideanSpace.piLpCongrLeft_single p x 1

lemma trace_projection (W : Submodule ℂ (H X)) :
    ∑ x, (W.starProjection (EuclideanSpace.single x (1:ℂ))) x = Module.finrank ℂ W := by
  classical
  have hp : LinearMap.IsProj W W.starProjection.toLinearMap := by
    constructor
    · intro x; exact (W.orthogonalProjectionOnto x).2
    · intro x hx; exact W.starProjection_eq_self_iff.mpr hx
  have ht := hp.trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun X ℂ).toBasis] at ht
  simpa only [Matrix.trace,Matrix.diag_apply,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,ContinuousLinearMap.coe_coe] using ht

lemma projection_diagonal (W : Submodule ℂ (H X)) (x : X) :
    (W.starProjection (EuclideanSpace.single x (1:ℂ))) x =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
  classical
  have hh := W.inner_starProjection_left_eq_right
    (EuclideanSpace.single x (1:ℂ)) (W.starProjection (EuclideanSpace.single x (1:ℂ)))
  have hf : W.starProjection (W.starProjection (EuclideanSpace.single x (1:ℂ))) =
      W.starProjection (EuclideanSpace.single x (1:ℂ)) :=
    W.starProjection_eq_self_iff.mpr (W.orthogonalProjectionOnto _).2
  rw [hf] at hh
  rw [inner_self_eq_norm_sq_to_K,EuclideanSpace.inner_single_left] at hh
  simpa using hh.symm

lemma projection_comm (W : Submodule ℂ (H X)) (p : Equiv.Perm X)
    (hW : W.map (act p).toLinearEquiv.toLinearMap = W) (v : H X) :
    act p (W.starProjection v) = W.starProjection (act p v) := by
  have hh := (act p).toLinearIsometry.map_starProjection W v
  change act p (W.starProjection v) =
    (W.map (act p).toLinearEquiv.toLinearMap).starProjection (act p v) at hh
  simpa only [hW] using hh

/-- A transitive invariant subspace has constant diagonal orthogonal projection. -/
lemma uniform_diagonal (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W) (x : X) :
    (Fintype.card X:ℝ) * ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 =
      Module.finrank ℂ W := by
  classical
  have hh (y : X) : (W.starProjection (EuclideanSpace.single y (1:ℂ))) y =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
    obtain ⟨p,hp,hW⟩ := htrans x y
    subst y
    rw [projection_diagonal,←act_single p x,←projection_comm W p hW,(act p).norm_map]
  have ht := trace_projection W
  simp_rw [hh] at ht
  have hhreal : (∑ _y : X, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2) =
      (Module.finrank ℂ W:ℝ) := by exact_mod_cast ht
  simpa using hhreal

/-- The uncertainty bound, with no assumption of irreducibility. -/
theorem uncertainty (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (v : H X) (hv : v ∈ W) (x : X) :
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤ (Module.finrank ℂ W:ℝ) * ‖v‖^2 := by
  classical
  have hh : inner ℂ (W.starProjection (EuclideanSpace.single x (1:ℂ))) v = v x := by
    rw [W.inner_starProjection_left_eq_right,W.starProjection_eq_self_iff.mpr hv,
      EuclideanSpace.inner_single_left]
    simp
  have hc := norm_inner_le_norm (𝕜 := ℂ) (W.starProjection (EuclideanSpace.single x (1:ℂ))) v
  rw [hh] at hc
  have hs : ‖v x‖^2 ≤ ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2 := by
    nlinarith [norm_nonneg (v x),norm_nonneg v,
      norm_nonneg (W.starProjection (EuclideanSpace.single x (1:ℂ)))]
  calc
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤
      (Fintype.card X:ℝ) * (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by rw [←mul_assoc,uniform_diagonal W htrans x]

end CubeShuffle.PermutationHilbert
namespace CubeShuffle.PermutationHilbert
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

lemma trace_projection_real (W : Submodule ℂ (H X)) :
    ∑ x, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 = (Module.finrank ℂ W:ℝ) := by
  have hh := trace_projection W
  simp_rw [projection_diagonal] at hh
  exact_mod_cast hh

/-- A coordinate footprint fixed by a subgroup supplies an unconditional
lower bound on invariant multiplicity. This is the trace form of the branching
estimate, valid for every transitive invariant submodule. -/
theorem footprint_dimension (W K : Submodule ℂ (H X)) (hKW : K ≤ W)
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (S : Finset X) (hS : ∀ x ∈ S, W.starProjection (EuclideanSpace.single x (1:ℂ)) ∈ K) :
    (S.card:ℝ) * (Module.finrank ℂ W:ℝ) ≤
      (Fintype.card X:ℝ) * (Module.finrank ℂ K:ℝ) := by
  have he (x : X) (hx : x ∈ S) :
      K.starProjection (EuclideanSpace.single x (1:ℂ)) =
        W.starProjection (EuclideanSpace.single x (1:ℂ)) := by
    apply K.eq_starProjection_of_mem_of_inner_eq_zero (hS x hx)
    intro v hv
    exact W.starProjection_inner_eq_zero _ v (hKW hv)
  have hs : ∑ x ∈ S, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 ≤
      (Module.finrank ℂ K:ℝ) := by
    rw [←trace_projection_real K]
    calc
      _ = ∑ x ∈ S, ‖K.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [he x hx]
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun x => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card X): (0:ℝ) ≤ _)
  rw [Finset.mul_sum] at hmul
  simp_rw [uniform_diagonal W htrans] at hmul
  simpa using hmul

end CubeShuffle.PermutationHilbert

end OAI
