import Mathlib
import OAI.Analysis.Crouzeix.SteinMetric

namespace OAI

/-! Realization. -/

noncomputable section

open Set Filter

open scoped Topology InnerProductSpace

namespace CrouzeixHilbert.Realization

section Gram

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_isometryEquiv_of_norm_eq (A B : E →ₗ[ℂ] V)
    (h : ∀ x, ‖A x‖ = ‖B x‖) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, U (A x) = B x := by
  have hk : A.ker ≤ B.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [← h x, LinearMap.mem_ker.mp hx, norm_zero]
  let l : A.range →ₗ[ℂ] V := (A.ker.liftQ B hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hl (x : E) : l ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    simp [l]
  let L : A.range →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl]
        exact (h x).symm }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, ?_⟩
  intro x
  change L.extend (A x) = B x
  rw [show A x = (⟨A x, LinearMap.mem_range_self A x⟩ : A.range) from rfl,
    LinearIsometry.extend_apply]
  exact hl x

end Gram

section Pair

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev SumSpace (H : Type*) [NormedAddCommGroup H] := WithLp 2 (H × H)

def pairL (A B : E →L[ℂ] H) : E →L[ℂ] SumSpace H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp (A.prod B)

def rowL (A B : H →L[ℂ] E) : SumSpace H →L[ℂ] E :=
  A.comp (WithLp.fstL 2 ℂ H H) + B.comp (WithLp.sndL 2 ℂ H H)

@[simp] theorem pairL_apply (A B : E →L[ℂ] H) (x : E) :
    pairL A B x = WithLp.toLp 2 (A x, B x) := rfl

@[simp] theorem rowL_apply (A B : H →L[ℂ] E) (x : SumSpace H) :
    rowL A B x = A x.fst + B x.snd := rfl

variable [CompleteSpace E] [CompleteSpace H]

theorem adjoint_pairL (A B : E →L[ℂ] H) :
    ContinuousLinearMap.adjoint (pairL A B) =
      rowL (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.adjoint B) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro y x
  simp only [rowL_apply, pairL_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, WithLp.prod_inner_apply]
  rfl

end Pair

section Colligation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

theorem exists_colligation (D L X Y : H →L[ℂ] H)
    (h : L * star L + Y * star Y = (D * L) * star (D * L) + X * star X) :
    ∃ U : SumSpace H ≃ₗᵢ[ℂ] SumSpace H,
      ∀ v, rowL L Y v = rowL (D * L) X (U v) := by
  let A := pairL (star (D * L)) (star X)
  let B := pairL (star L) (star Y)
  have hg : (ContinuousLinearMap.adjoint A).comp A =
      (ContinuousLinearMap.adjoint B).comp B := by
    simp only [A, B, adjoint_pairL]
    ext x
    simpa only [ContinuousLinearMap.comp_apply, pairL_apply, WithLp.toLp_fst,
      WithLp.toLp_snd, rowL_apply, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.star_eq_adjoint, add_apply,
      mul_apply_eq_comp] using (DFunLike.congr_fun h x).symm
  obtain ⟨U, hU⟩ := exists_isometryEquiv_of_norm_eq A.toLinearMap B.toLinearMap (fun x => by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖A x‖ ^ 2 = ‖B x‖ ^ 2
    rw [A.apply_norm_sq_eq_inner_adjoint_left, B.apply_norm_sq_eq_inner_adjoint_left, hg])
  use U.symm
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap.comp A = B := by
    ext x
    exact hU x
  have he' := congrArg ContinuousLinearMap.adjoint he
  rw [ContinuousLinearMap.adjoint_comp, U.adjoint_eq_symm] at he'
  have he'' : (rowL (D * L) X).comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      rowL L Y := by
    simpa only [A, B, adjoint_pairL, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint] using he'
  intro v
  exact (DFunLike.congr_fun he'' v).symm

end Colligation

section Transfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Colligation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  unitary : SumSpace H ≃ₗᵢ[ℂ] SumSpace H

namespace Colligation

def a (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 1 0))

def b (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 0 1))

def c (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.sndL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 1 0))

def d (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.sndL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 0 1))

theorem apply_pair (C : Colligation H) (v e : H) :
    C.unitary (WithLp.toLp 2 (v,e)) =
      WithLp.toLp 2 (C.a v + C.b e, C.c v + C.d e) := by
  have he : WithLp.toLp 2 (v,e) = pairL (1 : H →L[ℂ] H) 0 v + pairL 0 1 e := by
    apply WithLp.equiv 2 (H × H) |>.injective
    simp only [pairL_apply, one_apply_eq_self, zero_apply, WithLp.equiv_apply,
      WithLp.ofLp_add]
    ext <;> simp
  rw [he, map_add]
  apply WithLp.equiv 2 (H × H) |>.injective
  rfl

theorem energy (C : Colligation H) (v e : H) :
    ‖C.a v + C.b e‖ ^ 2 + ‖C.c v + C.d e‖ ^ 2 = ‖v‖ ^ 2 + ‖e‖ ^ 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2) (C.unitary.norm_map (WithLp.toLp 2 (v,e)))
  rw [C.apply_pair, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2] at h
  exact h

theorem norm_a_le (C : Colligation H) : ‖C.a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := C.energy v 0
  simp only [map_zero, add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  simp only [one_mul]
  nlinarith [norm_nonneg v, norm_nonneg (C.a v), sq_nonneg ‖C.c v‖]

theorem norm_b_le (C : Colligation H) : ‖C.b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := C.energy 0 v
  simp only [map_zero, zero_add, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  simp only [one_mul]
  nlinarith [norm_nonneg v, norm_nonneg (C.b v), sq_nonneg ‖C.d v‖]

theorem norm_c_le (C : Colligation H) : ‖C.c‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := C.energy v 0
  simp only [map_zero, add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  simp only [one_mul]
  nlinarith [norm_nonneg v, norm_nonneg (C.c v), sq_nonneg ‖C.a v‖]

theorem norm_d_le (C : Colligation H) : ‖C.d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := C.energy 0 v
  simp only [map_zero, zero_add, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  simp only [one_mul]
  nlinarith [norm_nonneg v, norm_nonneg (C.d v), sq_nonneg ‖C.b v‖]

def transfer (C : Colligation H) (z : ℂ) : H →L[ℂ] H :=
  C.d + z • (C.c * Ring.inverse (1 - z • C.a) * C.b)

variable [CompleteSpace H]

theorem one_sub_isUnit (C : Colligation H) {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit (1 - z • C.a) := by
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left C.norm_a_le (norm_nonneg z)).trans_lt
    (by simpa only [mul_one] using hz)

theorem transfer_energy (C : Colligation H) {z : ℂ} (hz : ‖z‖ < 1) (e : H) :
    ‖e‖ ^ 2 - ‖C.transfer z e‖ ^ 2 = (1 - ‖z‖ ^ 2) *
      ‖Ring.inverse (1 - z • C.a) (C.b e)‖ ^ 2 := by
  let v := Ring.inverse (1 - z • C.a) (C.b e)
  have hv : v - z • C.a v = C.b e := by
    have h := DFunLike.congr_fun
      (Ring.mul_inverse_cancel (1 - z • C.a) (C.one_sub_isUnit hz)) (C.b e)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] using h
  have ht : C.c (z • v) + C.d e = C.transfer z e := by
    simp only [transfer, add_apply, smul_apply, mul_apply_eq_comp, map_smul, v, add_comm]
  have h := C.energy (z • v) e
  rw [ht, map_smul, show z • C.a v + C.b e = v by rw [← hv]; abel,
    norm_smul, mul_pow] at h
  nlinarith

theorem norm_transfer_le (C : Colligation H) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖C.transfer z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro e
  have h := C.transfer_energy hz e
  have hz' : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpos := mul_nonneg hz' (sq_nonneg ‖Ring.inverse (1 - z • C.a) (C.b e)‖)
  simp only [one_mul]
  nlinarith [norm_nonneg e, norm_nonneg (C.transfer z e)]

end Colligation

variable [FiniteDimensional ℂ H]

theorem exists_colligation_data (D L X Y : H →L[ℂ] H)
    (h : L * star L + Y * star Y = (D * L) * star (D * L) + X * star X) :
    ∃ C : Colligation H, L = D * L * C.a + X * C.c ∧
      Y = D * L * C.b + X * C.d := by
  obtain ⟨U, hU⟩ := exists_colligation D L X Y h
  refine ⟨⟨U⟩, ?_, ?_⟩
  · ext v
    have h := hU (WithLp.toLp 2 (v,0))
    simpa only [rowL_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      map_zero, add_zero, add_apply, mul_apply_eq_comp, Colligation.a, Colligation.c,
      ContinuousLinearMap.comp_apply, pairL_apply, one_apply_eq_self, zero_apply,
      WithLp.fstL_apply, WithLp.sndL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h
  · ext v
    have h := hU (WithLp.toLp 2 (0,v))
    simpa only [rowL_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      map_zero, zero_add, add_apply, mul_apply_eq_comp, Colligation.b, Colligation.d,
      ContinuousLinearMap.comp_apply, pairL_apply, one_apply_eq_self, zero_apply,
      WithLp.fstL_apply, WithLp.sndL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h

end Transfer

end CrouzeixHilbert.Realization

end

end OAI
