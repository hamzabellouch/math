import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorFormPolynomial

namespace OAI

/-! The K=5 spatial form has the coherent degrees used by its certificate. -/

open Polynomial Matrix
namespace DefocusingNLS.ExteriorCertificate
open BoundaryCertificate (stateMatrix polynomialStep)

theorem inputT_degree (n : ℕ) (b : ℝ) : (inputT n b).natDegree ≤ 0 := by
  change (C _).natDegree ≤ 0
  rw [natDegree_C]

theorem inputS_degree (z₀ : ℤ) : (inputS z₀).natDegree ≤ 1 := by
  change (C _+X*C _).natDegree ≤ 1
  apply natDegree_add_le_of_degree_le (by rw [natDegree_C]; omega)
  exact natDegree_mul_le.trans (by simp only [natDegree_X,natDegree_C,Nat.add_zero,le_refl])

theorem state_entry_succ_zero (z₀ : ℤ) (b : ℝ) (n : ℕ) (j : Fin 2) :
    stateMatrix (polynomialState z₀ b (n+1)) 0 j =
      inputT n b*stateMatrix (polynomialState z₀ b n) 0 j+
        inputS z₀*stateMatrix (polynomialState z₀ b n) 1 j := by
  fin_cases j <;> rfl

theorem state_entry_succ_one (z₀ : ℤ) (b : ℝ) (n : ℕ) (j : Fin 2) :
    stateMatrix (polynomialState z₀ b (n+1)) 1 j =
      (inputT n b-C (500000000 : ℂ))*stateMatrix (polynomialState z₀ b n) 1 j-
        stateMatrix (polynomialState z₀ b (n+1)) 0 j := by
  fin_cases j <;> rfl

theorem state_column_degree (z₀ : ℤ) (b : ℝ) (n : ℕ) (i j : Fin 2) :
    (stateMatrix (polynomialState z₀ b (n+1)) i j).natDegree ≤ n+j.val := by
  induction n generalizing i j with
  | zero =>
    have ht := inputT_degree 0 b
    have hs := inputS_degree z₀
    have hd : (inputT 0 b-C (500000000 : ℂ)-inputS z₀).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le
        ((natDegree_sub_le _ _).trans (max_le (ht.trans (by omega)) (by rw [natDegree_C]; omega))) hs)
    fin_cases i <;> fin_cases j
    · simpa [polynomialState,polynomialStep,stateMatrix] using ht
    · simpa [polynomialState,polynomialStep,stateMatrix] using hs
    · simpa [polynomialState,polynomialStep,stateMatrix] using ht
    · simpa [polynomialState,polynomialStep,stateMatrix] using hd
  | succ n ih =>
    let P := stateMatrix (polynomialState z₀ b (n+1))
    have ht := inputT_degree (n+1) b
    have hD : (inputT (n+1) b-C (500000000 : ℂ)).natDegree ≤ 0 :=
      (natDegree_sub_le _ _).trans (max_le ht (by rw [natDegree_C]))
    have hx : (inputT (n+1) b*P 0 j+inputS z₀*P 1 j).natDegree ≤ (n+1)+j.val := by
      apply natDegree_add_le_of_degree_le
      · exact natDegree_mul_le.trans ((add_le_add ht (ih 0 j)).trans (by omega))
      · exact natDegree_mul_le.trans ((add_le_add (inputS_degree z₀) (ih 1 j)).trans (by omega))
    have hy : ((inputT (n+1) b-C (500000000 : ℂ))*P 1 j-
        (inputT (n+1) b*P 0 j+inputS z₀*P 1 j)).natDegree ≤ (n+1)+j.val := by
      apply (natDegree_sub_le _ _).trans
      apply max_le _ hx
      exact natDegree_mul_le.trans ((add_le_add hD (ih 1 j)).trans (by omega))
    fin_cases i
    · convert! (congrArg Polynomial.natDegree
        (state_entry_succ_zero z₀ b (n+1) j)).le.trans hx using 1
    · have he := state_entry_succ_one z₀ b (n+1) j
      have he' := state_entry_succ_zero z₀ b (n+1) j
      have he'' := he.trans (congrArg (fun v =>
        (inputT (n+1) b-C (500000000 : ℂ))*P 1 j-v) he')
      convert! (congrArg Polynomial.natDegree he'').le.trans hy using 1

attribute [local irreducible] polynomialState

theorem form_last_row (z₀ : ℤ) (b : ℝ) (i j : Fin 2) :
    let T := stateMatrix (polynomialState z₀ b 5)
    let P := stateMatrix (polynomialState z₀ b 4)
    let d := inputT 4 b-C (500000000 : ℂ)
    formPolynomial z₀ b i j = C (500000000 : ℂ)*conjugatePolynomial (T 0 i)*T 0 j+
      inputS z₀*(d*conjugatePolynomial (T 0 i)*P 1 j-
        conjugatePolynomial d*conjugatePolynomial (P 1 i)*T 0 j) := by
  dsimp only
  have hy (k : Fin 2) : stateMatrix (polynomialState z₀ b 5) 1 k =
      (inputT 4 b-C (500000000 : ℂ))*stateMatrix (polynomialState z₀ b 4) 1 k-
        stateMatrix (polynomialState z₀ b 5) 0 k := by
    exact state_entry_succ_one z₀ b 4 k
  unfold formPolynomial
  dsimp only
  rw [hy i, hy j]
  simp only [conjugatePolynomial, Polynomial.map_sub, Polynomial.map_mul]
  ring

/-- In particular d has degree ≤10, and the lower off-diagonal entry degree ≤9. -/
theorem form_degree (z₀ : ℤ) (b : ℝ) (j : Fin 2) :
    (formPolynomial z₀ b 1 j).natDegree ≤ 9+j.val := by
  rw [form_last_row]
  have hT (i j : Fin 2) := state_column_degree z₀ b 4 i j
  have hP (i j : Fin 2) := state_column_degree z₀ b 3 i j
  have hd : (inputT 4 b-C (500000000 : ℂ)).natDegree ≤ 0 :=
    natDegree_sub_le_of_le (inputT_degree 4 b) (by simp)
  have hc (p : Polynomial ℂ) := conjugatePolynomial_degree p
  have hfirst : (C (500000000 : ℂ)*conjugatePolynomial
      (stateMatrix (polynomialState z₀ b 5) 0 1)*
      stateMatrix (polynomialState z₀ b 5) 0 j).natDegree ≤ 9+j.val := by
    exact natDegree_mul_le.trans
      ((add_le_add ((natDegree_C_mul_le _ _).trans ((hc _).trans (hT 0 1)))
        (hT 0 j)).trans (by omega))
  have ha : ((inputT 4 b-C (500000000 : ℂ))*
      conjugatePolynomial (stateMatrix (polynomialState z₀ b 5) 0 1)*
      stateMatrix (polynomialState z₀ b 4) 1 j).natDegree ≤ 8+j.val := by
    exact natDegree_mul_le.trans
      ((add_le_add (natDegree_mul_le.trans (add_le_add hd ((hc _).trans (hT 0 1))))
        (hP 1 j)).trans (by omega))
  have hb : (conjugatePolynomial (inputT 4 b-C (500000000 : ℂ))*
      conjugatePolynomial (stateMatrix (polynomialState z₀ b 4) 1 1)*
      stateMatrix (polynomialState z₀ b 5) 0 j).natDegree ≤ 8+j.val := by
    exact natDegree_mul_le.trans
      ((add_le_add (natDegree_mul_le.trans (add_le_add ((hc _).trans hd)
        ((hc _).trans (hP 1 1)))) (hT 0 j)).trans (by omega))
  apply natDegree_add_le_of_degree_le hfirst
  exact natDegree_mul_le.trans
    ((add_le_add (inputS_degree z₀) ((natDegree_sub_le _ _).trans (max_le ha hb))).trans
      (by omega))

end DefocusingNLS.ExteriorCertificate

end OAI
