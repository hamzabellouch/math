import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZPipeline

namespace OAI

/-! Explicit polynomial envelopes for the literal four- and seven-word gadgets.
Only the term count, input coefficient bound and unary precision enter these
envelopes.  No bound on the Hilbert-space dimension is used. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped BigOperators Classical

def weightEnvelope (R B : ℚ) : ℚ :=
  R^3+R^2*B+R^2+R*(1+B^2)+1+B^2

theorem weightEnvelope_nonneg {R B : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B) :
    0 ≤ weightEnvelope R B := by unfold weightEnvelope; positivity

theorem weightEnvelope_mono {R S B C : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hRS : R ≤ S) (hBC : B ≤ C) : weightEnvelope R B ≤ weightEnvelope S C := by
  have hS : 0 ≤ S := hR.trans hRS
  unfold weightEnvelope
  gcongr

private theorem input_square_bound {j B : ℚ} (_hB : 0 ≤ B) (hj : |j| ≤ B) :
    j^2 ≤ B^2 := by
  have h := abs_le.mp hj
  nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (by linarith : 0 ≤ B+j)]

private theorem middle_bound (B : ℚ) : B ≤ 1+B^2 := by
  nlinarith [sq_nonneg (B-1)]

theorem four_weight_bound {R j B : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hj : |j| ≤ B) (k : Fin 4) :
    |QuantumPolarizedSubdivision.weight R j k| ≤ weightEnvelope R B := by
  have hj2 := input_square_bound hB hj
  have hR3 : 0 ≤ R^3 := pow_nonneg hR _
  have hR2B : 0 ≤ R^2*B := mul_nonneg (sq_nonneg R) hB
  have hRB2 : 0 ≤ R*B^2 := mul_nonneg hR (sq_nonneg B)
  have hRB : R*|j| ≤ R*(1+B^2) :=
    mul_le_mul_of_nonneg_left (hj.trans (middle_bound B)) hR
  fin_cases k
  · change |R^2/2+1+(j/2)^2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R^2/2| ≤ _
    rw [neg_div]
    rw [abs_neg,abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R| ≤ _
    rw [abs_of_nonneg hR]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R*j/2| ≤ _
    rw [abs_div,abs_mul,abs_neg,abs_of_nonneg hR]
    norm_num only [abs_of_pos (by norm_num : (0:ℚ) < 2)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]

theorem seven_weight_bound {R j B : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hj : |j| ≤ B) (k : Fin 7) :
    |QuantumPolarizedThird.weight R j k| ≤ weightEnvelope R B := by
  have hj2 := input_square_bound hB hj
  have hR3 : 0 ≤ R^3 := pow_nonneg hR _
  have hR2B : 0 ≤ R^2*B := mul_nonneg (sq_nonneg R) hB
  have hRB2 : 0 ≤ R*B^2 := mul_nonneg hR (sq_nonneg B)
  have hRj2 : R*j^2 ≤ R*B^2 := mul_le_mul_of_nonneg_left hj2 hR
  have hRB : R*|j| ≤ R*(1+B^2) :=
    mul_le_mul_of_nonneg_left (hj.trans (middle_bound B)) hR
  have hR2j : R^2*|j| ≤ R^2*B := mul_le_mul_of_nonneg_left hj (sq_nonneg R)
  fin_cases k
  · change |R^3/2+R*(1+(j/2)^2)| ≤ _
    rw [abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R^3/2| ≤ _
    rw [neg_div]
    rw [abs_neg,abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R*j| ≤ _
    rw [abs_mul,abs_of_nonneg hR]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R^2/2-(1+(j/2)^2)| ≤ _
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R^2/2| ≤ _
    rw [neg_div]
    rw [abs_neg,abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg R)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R^2*j/2| ≤ _
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg R)]
    norm_num only [abs_of_pos (by norm_num : (0:ℚ) < 2)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]

def scaleEnvelope (m : ℕ) (B : ℚ) (N : ℕ) : ℚ :=
  8*(4*(1+(m:ℚ)*(1+B)^2))^4*N

def stepEnvelope (m : ℕ) (B : ℚ) (N : ℕ) : ℚ := weightEnvelope (scaleEnvelope m B N) B

theorem scaleEnvelope_nonneg (m : ℕ) {B : ℚ} (_hB : 0 ≤ B) (N : ℕ) :
    0 ≤ scaleEnvelope m B N := by unfold scaleEnvelope; positivity

theorem stepEnvelope_nonneg (m : ℕ) {B : ℚ} (hB : 0 ≤ B) (N : ℕ) :
    0 ≤ stepEnvelope m B N := weightEnvelope_nonneg (scaleEnvelope_nonneg m hB N) hB

variable {κ : Type} [Fintype κ]

theorem scale_le_envelope (J : κ → ℚ) {m : ℕ} {B : ℚ} (_hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) :
    QuantumOrderedSubdivision.scale J N ≤ scaleEnvelope m B N := by
  have hs : (∑ e, (1+|J e|)^2) ≤ (m:ℚ)*(1+B)^2 := calc
    _ ≤ ∑ _e : κ, (1+B)^2 := by
      apply Finset.sum_le_sum
      intro e _
      gcongr
      exact hJ e
    _ = (Fintype.card κ:ℚ)*(1+B)^2 := by simp
    _ ≤ (m:ℚ)*(1+B)^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (sq_nonneg _)
  unfold QuantumOrderedSubdivision.scale QuantumOrderedSubdivision.budget scaleEnvelope
  gcongr

theorem subdivision_coefficient_bound (J : κ → ℚ) {m : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) (p : κ × Fin 4) :
    |QuantumOrderedSubdivision.outputCoefficient J N p| ≤ stepEnvelope m B N := by
  have hR : 0 ≤ QuantumOrderedSubdivision.scale J N := by
    unfold QuantumOrderedSubdivision.scale QuantumOrderedSubdivision.budget
    positivity
  exact (four_weight_bound hR hB (hJ p.1) p.2).trans
    (weightEnvelope_mono hR hB (scale_le_envelope J hB hm hJ N) le_rfl)

theorem third_coefficient_bound (J : κ → ℚ) {m : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) (p : κ × Fin 7) :
    |QuantumOrderedThird.outputCoefficient J N p| ≤ stepEnvelope m B N := by
  have hR : 0 ≤ QuantumOrderedSubdivision.scale J N := by
    unfold QuantumOrderedSubdivision.scale QuantumOrderedSubdivision.budget
    positivity
  exact (seven_weight_bound hR hB (hJ p.1) p.2).trans
    (weightEnvelope_mono hR hB (scale_le_envelope J hB hm hJ N) le_rfl)

/-- A fixed fivefold composition of explicit polynomials. -/
def pipelineBound (m : ℕ) (B : ℚ) (N : ℕ) : ℕ → ℚ
  | 0 => B
  | k+1 => stepEnvelope (3136*m) (pipelineBound m B N k) N

theorem pipelineBound_nonneg (m : ℕ) {B : ℚ} (hB : 0 ≤ B) (N k : ℕ) :
    0 ≤ pipelineBound m B N k := by
  induction k with
  | zero => exact hB
  | succ k ih => exact stepEnvelope_nonneg _ ih _

theorem pipeline_coefficient_bound (J : κ → ℚ) {m : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) (p : OutputTerm κ) :
    |coefficient J N p| ≤ pipelineBound m B N 5 := by
  have hm0 : Fintype.card κ ≤ 3136*m := by omega
  have hm1 : Fintype.card (κ × Fin 4) ≤ 3136*m := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hm2 : Fintype.card (ThreeTerm κ) ≤ 3136*m := by
    simp only [ThreeTerm,Fintype.card_prod,Fintype.card_fin]
    omega
  have hm3 : Fintype.card (TwoTerm κ) ≤ 3136*m := by
    simp only [TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
    omega
  have hm4 : Fintype.card (XZThreeTerm κ) ≤ 3136*m := by
    simp only [XZThreeTerm,TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
    omega
  have h1 (e : κ × Fin 4) :
      |QuantumOrderedTwoStage.firstCoefficient J N e| ≤ pipelineBound m B N 1 :=
    subdivision_coefficient_bound J hB hm0 hJ N e
  have h2 (e : ThreeTerm κ) : |threeCoefficient J N e| ≤ pipelineBound m B N 2 :=
    subdivision_coefficient_bound (QuantumOrderedTwoStage.firstCoefficient J N)
      (pipelineBound_nonneg m hB N 1) hm1 h1 N e
  have h3 (e : TwoTerm κ) : |twoCoefficient J N e| ≤ pipelineBound m B N 3 :=
    third_coefficient_bound (threeCoefficient J N)
      (pipelineBound_nonneg m hB N 2) hm2 h2 N e
  have h4 (e : XZThreeTerm κ) : |xzThreeCoefficient J N e| ≤ pipelineBound m B N 4 :=
    subdivision_coefficient_bound (twoCoefficient J N)
      (pipelineBound_nonneg m hB N 3) hm3 h3 N e
  exact third_coefficient_bound (xzThreeCoefficient J N)
    (pipelineBound_nonneg m hB N 4) hm4 h4 N p

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
