import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LagrangianObjective
import OAI.Analysis.MatrixSigning.Potential.Coordinates

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

theorem normalized_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε*d ≤ 1) (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d))
    (hηI : η (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ∃ z ∈ feasible S η,objective ε z ≤ 100 ∧
      ∀ w ∈ feasible S η,objective ε z ≤ objective ε w := by
  have hlo' : -(100:ℝ) • (Hermitian.one : H d) ≤ S := by
    apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  have hhi' : S ≤ (100:ℝ) • (Hermitian.one : H d) := by
    apply hhi.trans
    simpa only [one_smul] using scalar_mono_psd one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)
  let z₀ : Point d := (1+(1/20:ℝ)⁻¹+384*(1/20),(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • (Hermitian.one : H d))
  have hz₀ : z₀ ∈ feasible S η :=
    scalar_feasible S η (s:=1) (b:=384) (a:=1/20)
      (by rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul]; exact hlo)
      (by simpa only [one_smul] using hhi) hηI (by norm_num)
  have hf : objective ε z₀ ≤ 100 := by
    dsimp [z₀]
    rw [scalar_objective]
    norm_num
    nlinarith
  exact exists_minimizer S η hη hε (by norm_num) hlo' hhi' z₀ hz₀ hf
end CurrentKS.Variational

namespace CurrentKS.PositiveMap
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eigenvalue_abs_le (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C)
    (hC : IsClosed (C : Set E)) (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : E →L[ℝ] E) (hT : ∀ x ∈ C, T x ∈ C)
    {p : E} (hp : p ∈ interior (C : Set E)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : c • p - T p ∈ C) {r : ℝ} {x : E} (hx : x ≠ 0)
    (heig : T x = r • x) : |r| ≤ c := by
  by_contra! hbad
  have hrpos : 0 < |r| := hc.trans_lt hbad
  have hrsq : 0 < r^2 := sq_pos_of_ne_zero (abs_pos.mp hrpos)
  have hcsq : c^2 < r^2 := by nlinarith [sq_abs r]
  let U : E →L[ℝ] E := (r^2)⁻¹ • (T.comp T)
  have hU : ∀ y ∈ C, U y ∈ C := by
    intro y hy
    exact cone_smul_nonneg C h0 (inv_pos.mpr hrsq).le (hT _ (hT y hy))
  have hcrit : (c^2/r^2) • p - U p ∈ C := by
    have hh := C.add_mem (hT _ hbound) (cone_smul_nonneg C h0 hc hbound)
    have he : T (c • p-T p) + c • (c • p-T p) = c^2 • p - T (T p) := by
      simp only [map_sub, map_smul]
      module
    rw [he] at hh
    have hs := cone_smul_nonneg C h0 (inv_pos.mpr hrsq).le hh
    convert hs using 1
    simp only [U, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      smul_sub, smul_smul, div_eq_mul_inv]
    rw [mul_comm (c^2) ((r^2)⁻¹)]
  have heU : U x = x := by
    change (r^2)⁻¹ • T (T x) = x
    simp only [heig, map_smul, smul_smul]
    rw [← pow_two, inv_mul_cancel₀ hrsq.ne', one_smul]
  have hxC : x ∈ C := mem_of_supersolution C h0 hC U hU hp
    (div_nonneg (sq_nonneg c) hrsq.le) ((div_lt_one hrsq).mpr hcsq) hcrit
    (by rw [heU, sub_self]; exact h0)
  have hnC : -x ∈ C := mem_of_supersolution C h0 hC U hU hp
    (div_nonneg (sq_nonneg c) hrsq.le) ((div_lt_one hrsq).mpr hcsq) hcrit
    (by rw [map_neg, heU, sub_self]; exact h0)
  exact hx (hpoint x hxC hnC)

theorem symmetric_norm_bound {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (C : ConvexCone ℝ F) (h0 : (0 : F) ∈ C) (hC : IsClosed (C : Set F))
    (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : F →L[ℝ] F) (hT : ∀ x ∈ C, T x ∈ C) (hsym : T.toLinearMap.IsSymmetric)
    {p : F} (hp : p ∈ interior (C : Set F)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : c • p - T p ∈ C) : ‖T‖ ≤ c := by
  let b := hsym.eigenvectorBasis rfl
  have heig (i : Fin (Module.finrank ℝ F)) : |hsym.eigenvalues rfl i| ≤ c := by
    exact eigenvalue_abs_le C h0 hC hpoint T hT hp hc hbound
      (hsym.hasEigenvector_eigenvectorBasis rfl i).2 (hsym.apply_eigenvectorBasis rfl i)
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hsq : ‖T x‖^2 ≤ c^2 * ‖x‖^2 := by
    rw [← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh : inner ℝ (b i) (T x) = hsym.eigenvalues rfl i * inner ℝ (b i) x := by
      calc
        inner ℝ (b i) (T x) = inner ℝ (T (b i)) x := (hsym (b i) x).symm
        _ = _ := by
          change inner ℝ (T.toLinearMap (hsym.eigenvectorBasis rfl i)) x = _
          rw [hsym.apply_eigenvectorBasis]
          simp [real_inner_smul_left, b]
    rw [hh, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (hsym.eigenvalues rfl i)) hc).mpr (heig i)
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hc (norm_nonneg x)]

end CurrentKS.PositiveMap

end

end OAI
