import Mathlib
import OAI.Analysis.Crouzeix.Endpoint
import OAI.Analysis.Crouzeix.Iteration
import OAI.Analysis.Crouzeix.Realization

namespace OAI

/-! Matrix Endpoint. -/

noncomputable section

open Set Filter

open scoped InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace CrouzeixHilbert.Endpoint

open Boundary

theorem eq_zero_of_trace_pair_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian)
    (h : ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), (X * J.val).trace.re = 0) : X = 0 := by
  have hh := h ⟨X, hX⟩
  change (X * X).trace.re = 0 at hh
  nth_rw 1 [← hX.eq] at hh
  rw [trace_conjTranspose_mul_re] at hh
  have hn : ‖toHS X‖ = 0 := (sq_eq_zero_iff).mp hh
  have hz := norm_eq_zero.mp hn
  exact congrArg ofHS hz

structure MatrixCertificate {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) where
  X : Matrix (Fin n) (Fin n) ℂ
  Y : Matrix (Fin n) (Fin n) ℂ
  Z : Matrix (Fin n) (Fin n) ℂ
  X_positive : X.PosSemidef
  Y_positive : Y.PosSemidef
  Z_positive : Z.PosSemidef
  X_trace : X.trace.re = 1
  Y_trace : Y.trace.re = τ
  balance : X - Y = Z - T * Z * Tᴴ
  Y_slack : (Y * (H - 1)).trace.re = 0
  X_slack : (X * (τ • 1 - H)).trace.re = 0
  Z_slack : (Z * (H - Tᴴ * H * T)).trace.re = 0

theorem exists_matrixCertificate {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : spectralRadius ℂ T < 1) {τ : ℝ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Metric.Feasible T τ H)
    (hmin : ∀ s J, Metric.Feasible T s J → τ ≤ s) :
    Nonempty (MatrixCertificate T τ H) := by
  obtain ⟨C⟩ := exists_dualCertificate T hT ⟨H, hH.selfAdjoint⟩ hH hmin
  obtain ⟨X, hX, hx⟩ := exists_positive_trace_representative C.X C.X_positive
  obtain ⟨Y, hY, hy⟩ := exists_positive_trace_representative C.Y C.Y_positive
  obtain ⟨Z, hZ, hz⟩ := exists_positive_trace_representative C.Z C.Z_positive
  refine ⟨⟨X,Y,Z,hX,hY,hZ,?_,?_,?_,?_,?_,?_⟩⟩
  · simpa only [hx, unit_val, mul_one] using C.X_unit
  · simpa only [hy, unit_val, mul_one] using C.Y_unit
  · apply sub_eq_zero.mp
    apply eq_zero_of_trace_pair_zero _
      ((hX.isHermitian.sub hY.isHermitian).sub
      (hZ.isHermitian.sub (hZ.mul_mul_conjTranspose_same T).isHermitian))
    intro J
    have h := C.balance J
    rw [hx, hy, hz, hz] at h
    change (X * J.val).trace.re - (Y * J.val).trace.re =
      (Z * J.val).trace.re - (Z * (Tᴴ * J.val * T)).trace.re at h
    have he : (Z * (Tᴴ * J.val * T)).trace = (T * Z * Tᴴ * J.val).trace := by
      rw [Matrix.trace_mul_cycle', ← mul_assoc, ← mul_assoc]
    rw [he] at h
    simp only [sub_mul, Matrix.trace_sub, Complex.sub_re]
    linarith
  · have h := C.Y_slack
    rw [hy] at h
    exact h
  · have h := C.X_slack
    rw [hx] at h
    exact h
  · have h := C.Z_slack
    rw [hz] at h
    exact h

theorem trace_mul_eq_norm_sqrt_sq {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (B * C).trace.re = ‖toHS (CFC.sqrt C * CFC.sqrt B)‖ ^ 2 := by
  have hBS : (CFC.sqrt B)ᴴ = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).isHermitian.eq
  have hCS : (CFC.sqrt C)ᴴ = CFC.sqrt C :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C)).isHermitian.eq
  rw [← trace_conjTranspose_mul_re, Matrix.conjTranspose_mul, hBS, hCS]
  have he : CFC.sqrt B * CFC.sqrt C * (CFC.sqrt C * CFC.sqrt B) =
      CFC.sqrt B * C * CFC.sqrt B := by
    calc
      _ = CFC.sqrt B * (CFC.sqrt C * CFC.sqrt C) * CFC.sqrt B := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [he, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self B hB.nonneg]

theorem mul_sqrt_eq_zero_of_trace_mul_eq_zero {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (h : (B * C).trace.re = 0) : C * CFC.sqrt B = 0 := by
  rw [trace_mul_eq_norm_sqrt_sq B C hB hC] at h
  have hz : CFC.sqrt C * CFC.sqrt B = 0 := by
    have hn : ‖toHS (CFC.sqrt C * CFC.sqrt B)‖ = 0 := sq_eq_zero_iff.mp h
    exact congrArg ofHS (norm_eq_zero.mp hn)
  rw [← CFC.sqrt_mul_sqrt_self C hC.nonneg, mul_assoc, hz, mul_zero]

theorem mul_eq_zero_of_trace_mul_eq_zero {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (h : (B * C).trace.re = 0) : C * B = 0 := by
  rw [← CFC.sqrt_mul_sqrt_self B hB.nonneg, ← mul_assoc,
    mul_sqrt_eq_zero_of_trace_mul_eq_zero B C hB hC h, zero_mul]

theorem sqrt_mul_eigen {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H X : A) (hH : 0 ≤ H) {t : ℝ} (ht : 0 < t) (hX : H * X = (t ^ 2) • X) :
    CFC.sqrt H * X = t • X := by
  have hu : IsUnit (CFC.sqrt H + t • (1 : A)) :=
    (IsStrictlyPositive.nonneg_add (CFC.sqrt_nonneg H)
      (IsStrictlyPositive.smul ht isStrictlyPositive_one)).isUnit
  have hz : (CFC.sqrt H + t • (1 : A)) * (CFC.sqrt H * X - t • X) = 0 := by
    calc
      _ = CFC.sqrt H * CFC.sqrt H * X - (t * t) • X := by
        simp only [add_mul, mul_sub, mul_smul_comm, smul_mul_assoc, one_mul, mul_assoc]
        module
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self H hH, ← sq, hX, sub_self]
  have he := congrArg (Ring.inverse (CFC.sqrt H + t • (1 : A)) * ·) hz
  rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul, mul_zero] at he
  exact sub_eq_zero.mp he

theorem gram_congruence {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) {t : ℝ} (hX : S * X = t • X) :
    S * (X * Xᴴ) * S = (t ^ 2) • (X * Xᴴ) := by
  have hXR : Xᴴ * S = t • Xᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial, hS.eq] using
      congrArg Matrix.conjTranspose hX
  calc
    _ = (S * X) * (Xᴴ * S) := by simp only [mul_assoc]
    _ = _ := by rw [hX, hXR, smul_mul_assoc, mul_smul_comm, smul_smul, sq]

structure EndpointFactors {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (κ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) where
  X : Matrix (Fin n) (Fin n) ℂ
  Y : Matrix (Fin n) (Fin n) ℂ
  Q : Matrix (Fin n) (Fin n) ℂ
  X_norm : ‖toHS X‖ = 1
  Y_norm : ‖toHS Y‖ = 1
  X_endpoint : CFC.sqrt H * X = κ • X
  Y_endpoint : CFC.sqrt H * Y = Y
  perpendicular : Xᴴ * Y = 0
  Q_positive : Q.PosSemidef
  balance : X * Xᴴ - Y * Yᴴ = Q -
    (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) * Q *
      (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))ᴴ

theorem exists_endpointFactors {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    {κ : ℝ} (hκ : 1 < κ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Metric.Feasible T (κ ^ 2) H) (C : MatrixCertificate T (κ ^ 2) H) :
    Nonempty (EndpointFactors T κ H) := by
  let S := CFC.sqrt H
  let R := Ring.inverse S
  let X := CFC.sqrt C.X
  let Y₀ := CFC.sqrt C.Y
  let Y := κ⁻¹ • Y₀
  let Q := (κ⁻¹ ^ 2) • (S * C.Z * S)
  have hk : 0 < κ := zero_lt_one.trans hκ
  have hS : S.IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg H)).isHermitian
  have hX : X.IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C.X)).isHermitian
  have hY : Y₀.IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C.Y)).isHermitian
  have hXX : X * Xᴴ = C.X := by rw [hX.eq]; exact CFC.sqrt_mul_sqrt_self _ C.X_positive.nonneg
  have hYY : Y₀ * Y₀ᴴ = C.Y := by rw [hY.eq]; exact CFC.sqrt_mul_sqrt_self _ C.Y_positive.nonneg
  have hHX : H * X = κ ^ 2 • X := by
    have hp : (κ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℂ) - H).PosSemidef := by
      apply Matrix.nonneg_iff_posSemidef.mp
      apply sub_nonneg.mpr
      simpa only [Algebra.algebraMap_eq_smul_one] using hH.upper
    have h := mul_sqrt_eq_zero_of_trace_mul_eq_zero _ _ C.X_positive hp C.X_slack
    rw [sub_mul, smul_mul_assoc, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hHY : H * Y₀ = Y₀ := by
    have hp : (H - 1).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hH.lower)
    have h := mul_sqrt_eq_zero_of_trace_mul_eq_zero _ _ C.Y_positive hp C.Y_slack
    rw [sub_mul, one_mul] at h
    exact sub_eq_zero.mp h
  have hSX : S * X = κ • X := sqrt_mul_eigen H X hH.nonneg hk hHX
  have hSY : S * Y₀ = Y₀ := by
    simpa only [one_smul] using sqrt_mul_eigen H Y₀ hH.nonneg zero_lt_one
      (by simpa only [one_pow, one_smul] using hHY)
  have hnormX : ‖toHS X‖ ^ 2 = 1 := by
    rw [← trace_conjTranspose_mul_re, hX.eq]
    nth_rw 2 [← hX.eq]
    rw [hXX, C.X_trace]
  have hnormY₀ : ‖toHS Y₀‖ ^ 2 = κ ^ 2 := by
    rw [← trace_conjTranspose_mul_re, hY.eq]
    nth_rw 2 [← hY.eq]
    rw [hYY, C.Y_trace]
  have hnormY : ‖toHS Y‖ ^ 2 = 1 := by
    change ‖hsEquiv n (κ⁻¹ • Y₀)‖ ^ 2 = 1
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le),
      mul_pow, hsEquiv_apply, hnormY₀]
    field_simp
  have hGramX : X * Xᴴ = (κ⁻¹ ^ 2) • (S * C.X * S) := by
    rw [← hXX, gram_congruence S X hS hSX, smul_smul]
    simp [hk.ne']
  have hGramY : Y * Yᴴ = (κ⁻¹ ^ 2) • (S * C.Y * S) := by
    have hs : S * (Y₀ * Y₀ᴴ) * S = Y₀ * Y₀ᴴ := by
      simpa only [one_smul, one_pow] using gram_congruence S Y₀ hS
        (show S * Y₀ = (1 : ℝ) • Y₀ by simpa only [one_smul])
    rw [← hYY, hs]
    simp only [Y, Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc,
      mul_smul_comm, smul_smul, sq]
  have hQ : Q.PosSemidef := by
    have hs := C.Z_positive.mul_mul_conjTranspose_same S
    rw [hS.eq] at hs
    exact Matrix.nonneg_iff_posSemidef.mp (smul_nonneg (sq_nonneg (κ⁻¹)) hs.nonneg)
  have hu : IsUnit S := hH.isStrictlyPositive.isUnit_cfcSqrt H
  have hRS : R * S = 1 := Ring.inverse_mul_cancel S hu
  have hSR : S * R = 1 := Ring.mul_inverse_cancel S hu
  have hR : R.IsHermitian := (IsSelfAdjoint.of_nonneg
    ((CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hu).mpr (CFC.sqrt_nonneg H))).isHermitian
  have hconj : (S * T * R) * (S * C.Z * S) * (S * T * R)ᴴ = S * (T * C.Z * Tᴴ) * S := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hR.eq]
    calc
      _ = (S * T) * (R * S) * C.Z * (S * R) * (Tᴴ * S) := by noncomm_ring
      _ = _ := by rw [hRS, hSR, mul_one, mul_one]; simp only [mul_assoc]
  refine ⟨⟨X,Y,Q,?_,?_,hSX,?_,?_,hQ,?_⟩⟩
  · nlinarith [norm_nonneg (toHS X)]
  · nlinarith [norm_nonneg (toHS Y)]
  · change S * Y = Y
    simp only [Y, mul_smul_comm, hSY]
  · have hXR : Xᴴ * S = κ • Xᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial, hS.eq] using
        congrArg Matrix.conjTranspose hSX
    have he : (κ - 1) • (Xᴴ * Y) = 0 := by
      rw [sub_smul, one_smul, ← smul_mul_assoc, ← hXR, mul_assoc]
      simp only [Y, mul_smul_comm, hSY, sub_self]
    exact (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hκ.ne')
  · change X * Xᴴ - Y * Yᴴ = Q - (S * T * R) * Q * (S * T * R)ᴴ
    rw [hGramX, hGramY, ← smul_sub, ← sub_mul, ← mul_sub, C.balance]
    simp only [mul_sub, sub_mul, smul_sub, Q, mul_smul_comm, smul_mul_assoc, hconj]

theorem endpointFactors_of_minimum {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : spectralRadius ℂ T < 1) {κ : ℝ} (hκ : 1 < κ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : Metric.Feasible T (κ ^ 2) H)
    (hmin : ∀ s J, Metric.Feasible T s J → κ ^ 2 ≤ s) :
    Nonempty (EndpointFactors T κ H) := by
  obtain ⟨C⟩ := exists_matrixCertificate T hT H hH hmin
  exact exists_endpointFactors T hκ H hH C

end CrouzeixHilbert.Endpoint

end

end OAI
