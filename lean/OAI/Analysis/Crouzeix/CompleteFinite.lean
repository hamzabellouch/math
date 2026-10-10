import Mathlib
import OAI.Analysis.Crouzeix.MetricBoundary

namespace OAI

/-! Complete Finite. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

lemma entrywiseHolomorphic_matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (V : Set ℂ) : EntrywiseHolomorphic V (matrixPolynomial B) := by
  intro i j
  simp only [matrixPolynomial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply DifferentiableOn.fun_sum
  intro k _
  exact (differentiableOn_id.pow (k : ℕ)).mul_const _

lemma matrixHolomorphicEval_matrixPolynomial
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {V : Set ℂ} (hV : IsOpen V) (hKV : numericalClosure A ⊆ V)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    matrixHolomorphicEval A V (matrixPolynomial B) = polynomialEval A B := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hV hKV
  have he : matrixHolomorphicEval A V (matrixPolynomial B) =
      matrixContourEval A Γ.toSmoothContour (matrixPolynomial B) := by
    simp only [matrixHolomorphicEval, matrixContourEval,
      holomorphicEval_eq_contourEval A hV (entrywiseHolomorphic_matrixPolynomial B V _ _) Γ]
  rw [he, matrixContourEval_matrixPolynomial A Γ B]

lemma norm_tensorOperator_one_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator H) (m : ℕ) : ‖tensorOperator A (1 : Coeff m)‖ ≤ ‖A‖ := by
  have h1 : ‖(1 : Coeff m)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  exact (norm_tensorOperator_le A (1 : Coeff m)).trans
    ((mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq (mul_one _))

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {n : ℕ} (hn : 0 < n) (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U)

include C R hn hKU hU hc hb

lemma holomorphic_bound {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    ‖matrixHolomorphicEval A V F‖ ≤ 2 * supNorm (closure U) F := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨S,J,D,hJS,_,hcond,hN,hD,hI⟩ := C.exists_conformal_contraction R hn A hKU hU hc hb
  let Λ := C.operatorDensity R D hD
  let F₀ := C.matrixAnalyticTrace hUV F hF.continuousOn
  let L := ∫ t, tensorOperator (Λ t) (F₀ t) ∂circleMeasure
  have hs : tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      L * tensorOperator S (1 : Coeff m) :=
    C.physical_intertwines R hU hc A D S hKU hN hD hI hV hUV hF
  have hi : tensorOperator J (1 : Coeff m) * tensorOperator S (1 : Coeff m) = 1 := by
    rw [← tensorOperator_mul, hJS, one_mul, tensorOperator_one]
  have he : matrixHolomorphicEval A V F =
      tensorOperator J (1 : Coeff m) * L * tensorOperator S (1 : Coeff m) := by
    calc
      _ = (tensorOperator J (1 : Coeff m) * tensorOperator S (1 : Coeff m)) *
          matrixHolomorphicEval A V F := by rw [hi, one_mul]
      _ = _ := by rw [mul_assoc, hs, ← mul_assoc]
  have hsup := supNorm_bddAbove hb.isCompact_closure (hF.continuousOn.mono hUV)
  have hc0 := supNorm_nonneg hsup
  have hnL : ‖L‖ ≤ supNorm (closure U) F :=
    norm_integral_tensor_density_le Λ (C.operatorDensity_nonneg R D hD hN)
      (C.integral_operatorDensity R D hD hU hc) F₀ _ hc0
      (fun t => norm_le_supNorm hsup (C.boundaryMap_mem_frontier t).1)
  rw [he]
  calc
    ‖tensorOperator J (1 : Coeff m) * L * tensorOperator S (1 : Coeff m)‖ ≤
        (‖tensorOperator J (1 : Coeff m)‖ * ‖L‖) * ‖tensorOperator S (1 : Coeff m)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖J‖ * supNorm (closure U) F) * ‖S‖ :=
      mul_le_mul (mul_le_mul (norm_tensorOperator_one_le J m) hnL (norm_nonneg _) (norm_nonneg _))
        (norm_tensorOperator_one_le S m) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hc0)
    _ = (‖S‖ * ‖J‖) * supNorm (closure U) F := by ring
    _ ≤ 2 * supNorm (closure U) F := mul_le_mul_of_nonneg_right hcond hc0

lemma polynomial_bound {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (closure U) (matrixPolynomial B) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  rw [← matrixHolomorphicEval_matrixPolynomial A isOpen_univ (subset_univ _) B]
  exact C.holomorphic_bound R hn A hKU hU hc hb isOpen_univ (subset_univ _)
    (entrywiseHolomorphic_matrixPolynomial B univ)

end Conformal.ExteriorCollar

theorem finite_matrix_polynomial_bound : FiniteMatrixPolynomialBound := by
  intro n hn M m _ d B
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let A := Matrix.toEuclideanCLM (𝕜 := ℂ) M
  change ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)
  rw [(polynomial_sup_eq_max A B).1]
  let K := numericalClosure A
  let P := matrixPolynomial B
  have hK := isCompact_numericalClosure A
  have hc := convex_numericalClosure A
  have hne : K.Nonempty := numericalClosure_nonempty A
  have hsup := supNorm_bddAbove hK (continuous_matrixPolynomial B).continuousOn
  have hs0 := supNorm_nonneg hsup
  apply le_of_forall_pos_le_add
  intro ε hε
  let V := {z : ℂ | ‖P z‖ < supNorm K P + ε / 2}
  have hV : IsOpen V := isOpen_lt (continuous_matrixPolynomial B).norm continuous_const
  have hKV : K ⊆ V := fun z hz => (norm_le_supNorm hsup hz).trans_lt (by dsimp only [K,P]; linarith)
  obtain ⟨U,hU,hb,hcU,hKU,hUV,hchart⟩ := Conformal.exists_convex_analytic_neighborhood
    hK hc hne hV hKV
  obtain ⟨a,ha⟩ := hne
  obtain ⟨R⟩ := Conformal.exists_interiorCollar hU hb
    (Conformal.isSimplyConnected_of_convex hcU ⟨a,hKU ha⟩) ⟨a,hKU ha⟩ hchart
  obtain ⟨C⟩ := Conformal.exists_exteriorCollar hU hb hcU (hKU ha) hchart
  have hg := C.polynomial_bound R hn A hKU hU hcU hb B
  have hs : supNorm (closure U) P ≤ supNorm K P + ε / 2 :=
    supNorm_le (by dsimp only [K,P]; linarith) (fun z hz => (hUV hz).le)
  calc
    ‖polynomialEval A B‖ ≤ 2 * supNorm (closure U) P := hg
    _ ≤ 2 * (supNorm K P + ε / 2) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 2 * supNorm (numericalClosure A) (matrixPolynomial B) + ε := by dsimp only [K,P]; ring

end CrouzeixHilbert

end

end OAI
