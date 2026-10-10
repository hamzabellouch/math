import OAI.Combinatorics.ContingencyTables.Transport.FiniteRepairVariance

namespace OAI

/-! # The source polynomial coefficient for the repaired graph -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

lemma graph_poincare_coefficient (d U : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U) :
    ((1+2*(d:ℝ)^2)*4*(d:ℝ)^2*((U:ℝ)+1)^6+2) ≤ 770*(d:ℝ)^4*(U:ℝ)^6 := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hU' : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hd2 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hd4 : (1:ℝ) ≤ (d:ℝ)^4 := by nlinarith [sq_nonneg ((d:ℝ)^2-1)]
  have hU6 : (1:ℝ) ≤ (U:ℝ)^6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hU' 6
    simpa only [one_pow] using h
  have hbig : (1:ℝ) ≤ (d:ℝ)^4*(U:ℝ)^6 := by nlinarith
  have hplus : ((U:ℝ)+1)^6 ≤ (2*(U:ℝ))^6 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 6
  calc
    _ ≤ (3*(d:ℝ)^2)*4*(d:ℝ)^2*(2*(U:ℝ))^6+2 := by
      have hc : (1+2*(d:ℝ)^2)*4*(d:ℝ)^2 ≤ (3*(d:ℝ)^2)*4*(d:ℝ)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith :
          1+2*(d:ℝ)^2 ≤ 3*(d:ℝ)^2) (by norm_num)) (sq_nonneg _)
      exact add_le_add (mul_le_mul hc hplus (by positivity) (by positivity)) le_rfl
    _ = 768*(d:ℝ)^4*(U:ℝ)^6+2 := by ring
    _ ≤ _ := by nlinarith

theorem variance_repaired_graph_budget {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ) (R : D → B) (label : D → T)
    (hw : ∀ b,0 ≤ w b) (hv : ∀ d,0 ≤ v d) (hdom : ∀ d,v d ≤ w (R d))
    (hinj : Function.Injective (fun d => (label d,R d))) (d U : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U)
    (hT : Fintype.card T ≤ d^2) (E : ℝ) (hE : 0 ≤ E)
    (hvar : variance w H ≤ 4*(d:ℝ)^2*((U:ℝ)+1)^6*E)
    (hrepair : (∑ x,v x*(K x-H (R x))^2) ≤ E) :
    variance (Sum.elim w v) (Sum.elim H K) ≤ 770*(d:ℝ)^4*(U:ℝ)^6*E := by
  have hcoef : (1+2*(Fintype.card T:ℝ)) ≤ 1+2*(d:ℝ)^2 := by
    have hT' : (Fintype.card T:ℝ) ≤ (d:ℝ)^2 := by exact_mod_cast hT
    linarith
  have hvar0 : 0 ≤ variance w H := Finset.sum_nonneg (fun b _ => mul_nonneg (hw _) (sq_nonneg _))
  calc
    _ ≤ (1+2*(Fintype.card T:ℝ))*variance w H+2*∑ x,v x*(K x-H (R x))^2 :=
      variance_sum_repair w v H K R label hw hv hdom hinj
    _ ≤ (1+2*(d:ℝ)^2)*variance w H+2*E :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hvar0) (mul_le_mul_of_nonneg_left hrepair (by norm_num))
    _ ≤ (1+2*(d:ℝ)^2)*(4*(d:ℝ)^2*((U:ℝ)+1)^6*E)+2*E :=
      add_le_add (mul_le_mul_of_nonneg_left hvar (show 0 ≤ 1+2*(d:ℝ)^2 by positivity)) le_rfl
    _ = ((1+2*(d:ℝ)^2)*4*(d:ℝ)^2*((U:ℝ)+1)^6+2)*E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (graph_poincare_coefficient d U hd hU) hE

end ContingencyTables.FiniteExposureVariance

end OAI
