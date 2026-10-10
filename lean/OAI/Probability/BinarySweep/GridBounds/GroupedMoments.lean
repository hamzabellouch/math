import Mathlib
import OAI.Probability.BinarySweep.GridBounds.BoardProduct
import OAI.Probability.BinarySweep.MatrixBounds.MatrixRegularize
import OAI.Probability.BinarySweep.MatrixBounds.SchattenBasic
import OAI.Probability.BinarySweep.GridBounds.GroupedTypes
import OAI.Probability.BinarySweep.FiniteLaws.ActiveTypes

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open scoped Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}

lemma action_unitary (p : A → Bool) (g : Equiv.Perm (Fin N)) :
    actionMatrix p g ∈ Matrix.unitaryGroup (Fin N → A) ℂ := by
  exact ⟨actionMatrix_star_mul p g,actionMatrix_unitary p g⟩

lemma matrixMoment_signedConj (p : A → Bool) (g : Equiv.Perm (Fin N))
    (q : ℕ) (M : Matrix (Fin N → A) (Fin N → A) ℂ) :
    matrixMoment q (signedConj p g M)=matrixMoment q M :=
  matrixMoment_unitary_conj q ⟨actionMatrix p g,action_unitary p g⟩ M

def groupedAverage (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :=
  signedConj p g (blockAverage e p w)

lemma groupedAverage_law (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    groupedAverage e g p w =
      ∑a : ∀i, Equiv.Perm (Fin (n i)),
        (∏i, w i (a i)) • actionMatrix p (g*blockPerm e a*g⁻¹) := by
  simp only [groupedAverage,signedConj,blockAverage,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,actionMatrix_mul,actionMatrix_inv]

variable {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

theorem grouped_projected_moment_le (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] (hρ : ∀i a v, ‖ρ i a v‖=‖v‖)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) {q : ℕ} (hq : 0<q) :
    matrixMoment q (groupedProjection e g p ρ*groupedAverage e g p w) ≤
      ∏i, (n i+1:ℝ)^((Fintype.card A)^2)*evenMoment q (groupAverage (ρ i) (w i)) := by
  rw [groupedProjection,groupedAverage,←signedConj_mul,matrixMoment_signedConj]
  exact block_projected_moment_le e p ρ hρ w hq

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_commutes_average (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    blockProjection e p ρ*blockAverage e p w=blockAverage e p w*blockProjection e p ρ := by
  rw [blockAverage_tensor,blockProjection,Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv,piTensorMatrices_mul,piTensorMatrices_mul]
  congr 2
  funext i
  exact isotypicProjection_commutes_average p (ρ i) (w i)

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_commutes_average (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    groupedProjection e g p ρ*groupedAverage e g p w=
      groupedAverage e g p w*groupedProjection e g p ρ := by
  rw [groupedProjection,groupedAverage,←signedConj_mul,←signedConj_mul,
    blockProjection_commutes_average]

omit [∀ i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_norm_le (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    ‖groupedProjection e g p ρ‖ ≤ 1 := by
  exact IsStarProjection.norm_le _ ⟨groupedProjection_idempotent e g p ρ,
    (groupedProjection_psd e g p ρ).isHermitian⟩

lemma blockActive_projection_sum (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool) :
    (∑a : ∀i, ActiveType p (n i),
      blockProjection e p (fun i => Young.partitionHilbertRep (a i).val))=1 := by
  unfold blockProjection
  rw [←submatrix_sum_eq]
  have hs := piTensorMatrices_sum (fun i (a : ActiveType p (n i)) =>
    isotypicProjection p (Young.partitionHilbertRep a.val))
  rw [←hs]
  have he : (fun i => ∑a : ActiveType p (n i),
      isotypicProjection p (Young.partitionHilbertRep a.val)) = (fun i => (1 : Matrix (Fin (n i) → A) (Fin (n i) → A) ℂ)) := by
    funext i
    exact active_typeProjection_sum p (n i)
  rw [he,piTensorMatrices_one,Matrix.submatrix_one_equiv]

lemma groupedActive_projection_sum (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool) :
    (∑a : ∀i, ActiveType p (n i),
      groupedProjection e g p (fun i => Young.partitionHilbertRep (a i).val))=1 := by
  unfold groupedProjection signedConj
  rw [←Finset.sum_mul,←Finset.mul_sum,blockActive_projection_sum,mul_one,actionMatrix_unitary]

lemma blockActive_card (p : A → Bool) :
    Fintype.card (∀i, ActiveType p (n i))≤∏i,(n i+1)^((Fintype.card A)^2) := by
  rw [Fintype.card_pi]
  exact Finset.prod_le_prod (fun i _ => activeType_card p (n i))

end BinaryCoordinateSweeps.Signed

end

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]

omit [Nonempty A] in
theorem whitened_board_budget {n : ℕ} (e : Fin n ↪ I × J)
    (r : I → Matrix A A ℂ) (v : J → Matrix A A ℂ) (C : Matrix A A ℂ)
    (hr : ∀ i, (r i).PosSemidef) (hv : ∀ j, (v j).PosSemidef)
    (htv : ∀ j, (v j).trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC : C.IsHermitian) (hCMC : C * regularizedMean r ε * C = 1) :
    (1-ε)^n * (tensorMatrices (fun t : Fin n => C * r (e t).1 * C) *
      tensorMatrices (fun t : Fin n => v (e t).2)).trace.re ≤
      Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
  let x : I → J → ℝ := fun i j => (C*r i*C*v j).trace.re
  have hp (i : I) : (C*r i*C).PosSemidef := by
    simpa only [hC.eq] using (hr i).mul_mul_conjTranspose_same C
  have hx (i : I) (j : J) : 0 ≤ x i j := trace_product_re_nonneg (hp i) (hv j)
  have hs (j : J) : ∑ i, (1-ε)*x i j ≤ Fintype.card I := by
    rw [← Finset.mul_sum]
    exact whitened_column_budget r (v j) C hr (hv j) (htv j) hε hC hCMC
  have he := rectangular_product_holes (Finset.univ.map e) (fun i j => (1-ε)*x i j)
    (fun i j => mul_nonneg (sub_nonneg.mpr hε1) (hx i j)) hs
  rw [Finset.prod_map,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,Finset.card_map,Finset.card_univ,Fintype.card_fin] at he
  rw [tensor_product_trace_re _ _ (fun t => hp (e t).1) (fun t => hv (e t).2)]
  exact he

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma matrix_norm_sq_le_trace (M : Matrix I I ℂ) : ‖M‖^2 ≤ (M.conjTranspose*M).trace.re := by
  have h := pow_le_pow_left₀ (norm_nonneg M) (TraceHolder.op_norm_le_schatten (q:=1) (by omega) M) 2
  have he := TraceHolder.schatten_pow (q:=1) (by omega) M
  simpa only [Nat.mul_one,he,TraceHolder.matrixMoment,pow_one,Matrix.star_eq_conjTranspose] using h

lemma projection_overlap_norm_trace (R Q P : Matrix I I ℂ)
    (hR : R.IsHermitian) (hQ : Q.IsHermitian) (hP : P.IsHermitian)
    (hRR : R*R=R) (hQQ : Q*Q=Q) (hPP : P*P=P) (hPQ : P*Q=Q*P) :
    ‖Q*P*R‖^2 ≤ (R*Q*P).trace.re := by
  have h := matrix_norm_sq_le_trace (Q*P*R)
  have he : ((Q*P*R).conjTranspose*(Q*P*R)).trace = (R*Q*P).trace := by
    simp only [Matrix.conjTranspose_mul,hR.eq,hQ.eq,hP.eq]
    calc
      _ = (R*(P*(Q*Q)*P)*R).trace := by congr 1; noncomm_ring
      _ = (R*(Q*P)*R).trace := by rw [hQQ,hPQ,mul_assoc Q P P,hPP]
      _ = (R*R*(Q*P)).trace := by rw [Matrix.trace_mul_cycle]
      _ = _ := by rw [hRR,mul_assoc]
  rw [he] at h
  exact h

omit [DecidableEq I] in
lemma commuting_projection_product_psd (P Q : Matrix I I ℂ)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q*Q=Q) (hPQ : P*Q=Q*P) :
    (Q*P).PosSemidef := by
  have h := hP.mul_mul_conjTranspose_same Q
  rw [hQ.eq,mul_assoc, hPQ,← mul_assoc,hQQ] at h
  exact h

omit [DecidableEq I] in
lemma compress_whitening_cap (P Q C : Matrix I I ℂ) (d : ℂ)
    (hQ : Q.IsHermitian) (hQQ : Q*Q=Q) (hPQ : P*Q=Q*P) (hCQ : C*Q=Q*C)
    (hc : (C*C-d•P).PosSemidef) : (C*Q*C-d•(Q*P)).PosSemidef := by
  have h := hc.mul_mul_conjTranspose_same Q
  rw [hQ.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at h
  have he1 : Q*(C*C)*Q = C*Q*C := by
    calc
      _ = (Q*C)*(C*Q) := by noncomm_ring
      _ = (C*Q)*(Q*C) := by rw [hCQ,← hCQ]
      _ = C*(Q*Q)*C := by noncomm_ring
      _ = _ := by rw [hQQ]
  have he2 : Q*P*Q = Q*P := by rw [mul_assoc,hPQ,← mul_assoc,hQQ]
  rwa [he1,he2] at h

end BinaryCoordinateSweeps.Density

end

end OAI
