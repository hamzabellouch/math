import OAI.Combinatorics.HadwigerCounterexample.MatrixFactorization

namespace OAI

/-! # Flat Level Shifts -/

noncomputable section
namespace HadwigerCounterexample
open Matrix

variable {I J Q : Type} [Fintype I] [Fintype J] [Fintype Q]

/-- Shift a P row to an X t row. If the Gram comparisons obey Boolean
monomial identities, there are coordinate factors of H for which both the
left and the right row arrays diagonalize all these shifts. -/
theorem shift_factors [DecidableEq J] (P : Mat I J) (H : Mat J J)
    (hP : Function.Injective P.mulVec) (hH : Function.Injective H.mulVec)
    (X : Q → Mat I J)
    (h1 : ∀ a, X a * H * Pᵀ = P * H * (X a)ᵀ)
    (h2 : ∀ a b, X a * H * (X b)ᵀ = X b * H * (X a)ᵀ)
    (h3 : ∀ a, X a * H * (X a)ᵀ = X a * H * Pᵀ) :
    ∃ (K C : Mat J J) (f : Q → J → F), H = K * Cᵀ ∧
      ∀ a, X a * C = P * C * diagonal (f a) ∧ X a * K = P * K * diagonal (f a) := by
  classical
  obtain ⟨R,hR⟩ := mat_left_inv hP
  obtain ⟨L,hL⟩ := mat_left_inv hH
  have hh : H*L=1 := mul_eq_one_comm.mp hL
  have hr : Pᵀ*Rᵀ=1 := by rw [← Matrix.transpose_mul,hR,Matrix.transpose_one]
  have hp_cancel {A B : Mat J J} (h : P*A*Pᵀ=P*B*Pᵀ) : A=B := by
    have hx := matrix_cancel_left hP (A*Pᵀ) (B*Pᵀ)
      (by simpa only [Matrix.mul_assoc] using h)
    have hx := congrArg (fun A => A*Rᵀ) hx
    simpa only [Matrix.mul_assoc,hr,Matrix.mul_one] using hx
  have hr_cancel {W : Type} [Fintype W] (A B : Mat W J)
      (h : A*H=B*H) : A=B := by
    have he := congrArg (fun t : Mat W J => t*L) h
    simpa only [Matrix.mul_assoc,hh,Matrix.mul_one] using he
  let M := fun a => R*X a
  have he (a : Q) : X a = P*M a := by
    apply hr_cancel
    calc X a * H = X a * H * (Pᵀ*Rᵀ) := by rw [hr,Matrix.mul_one]
         _ = P * (H * ((X a)ᵀ * Rᵀ)) := by
           rw [← Matrix.mul_assoc, h1]
           simp only [Matrix.mul_assoc]
         _ = P * (R * (P * H * (X a)ᵀ) * Rᵀ) := by
           simp only [← Matrix.mul_assoc,hR,Matrix.mul_one]
         _ = P * M a * H := by
           rw [← h1]
           simp only [M,Matrix.mul_assoc,hr,Matrix.mul_one]
  have es a : M a*H=H*(M a)ᵀ := by
    apply hp_cancel
    have hh := h1 a
    rw [he] at hh
    simpa only [transpose_mul,Matrix.mul_assoc] using hh
  have ei (a b) :
      P*(M a*(M b*H))*Pᵀ=X a*H*(X b)ᵀ := by
    simp only [he,es b,transpose_mul,Matrix.mul_assoc]
  have hc (a b) : M a * M b=M b*M a := by
    apply hr_cancel
    apply hp_cancel
    rw [Matrix.mul_assoc (M a), ei, h2, Matrix.mul_assoc (M b),ei]
  have hi a : M a * M a=M a := by
    apply hr_cancel
    apply hp_cancel
    rw [Matrix.mul_assoc (M a), ei, h3, he]
    simp only [Matrix.mul_assoc]
  obtain ⟨C,D,hD,hc1,hc2,hc3⟩ := diagonalize M hc hi
  let K := H * Dᵀ
  refine ⟨K,C,hD,?_,fun a => ?_⟩
  · unfold K
    rw [Matrix.mul_assoc,←transpose_mul,hc2,transpose_one,Matrix.mul_one]
  have hv : D*M a=diagonal (hD a)*D := by
    calc D*M a = D*(M a*C)*D := by simp only [Matrix.mul_assoc,hc2,Matrix.mul_one]
         _ = diagonal (hD a)*D := by rw [hc3,←Matrix.mul_assoc,hc1,Matrix.one_mul]
  have hk : M a*K=K*diagonal (hD a) := by
    unfold K
    rw [←Matrix.mul_assoc,es a, Matrix.mul_assoc, ← transpose_mul,hv,transpose_mul,
      diagonal_transpose,Matrix.mul_assoc]
  rw [he]
  constructor
  · simp only [Matrix.mul_assoc,hc3]
  · simp only [Matrix.mul_assoc,hk]

end HadwigerCounterexample

end

end OAI
