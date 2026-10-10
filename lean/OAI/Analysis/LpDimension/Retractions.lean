import OAI.Analysis.LpDimension.ConvexSelection

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal
universe u uE uH uJ uV

namespace SubpolynomialLp

section WeightedProjection
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

def weightedProjection (A : Matrix E V ℝ) (σ : E → ℝ) : Matrix E E ℝ :=
  diagonal (fun e => (Real.sqrt (σ e))⁻¹) *
    gramProjection (diagonal (fun e => Real.sqrt (σ e)) * A) *
    diagonal (fun e => Real.sqrt (σ e))

def retractions (A : Matrix E V ℝ) : Set (Matrix E E ℝ) :=
  {P | P*A=A ∧ ∃ B : Matrix V E ℝ, P=A*B}

omit [DecidableEq E] [DecidableEq V] in
lemma retractions_convex (A : Matrix E V ℝ) : Convex ℝ (retractions A) := by
  intro P hP Q hQ a b ha hb hab
  rcases hP with ⟨hPA,B,rfl⟩
  rcases hQ with ⟨hQA,C,rfl⟩
  constructor
  · rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hPA, hQA,
      ← add_smul, hab, one_smul]
  · refine ⟨a • B+b • C, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]

omit [DecidableEq E] in
lemma gramProjection_factor (A : Matrix E V ℝ) :
    ∃ B : Matrix V E ℝ, gramProjection A = A*B := by
  refine ⟨((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) *
    diagonal (fun i => ((gramHermitian A).eigenvalues i)⁻¹) *
    (gramEigenMatrix A).transpose, ?_⟩
  simp only [gramProjection, gramEigenMatrix, Matrix.mul_assoc]

lemma sqrt_diagonal_inv (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) :
    diagonal (fun e => (Real.sqrt (σ e))⁻¹) * diagonal (fun e => Real.sqrt (σ e)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (Real.sqrt_pos.2 (hσ _)).ne']
  exact diagonal_one

lemma weightedProjection_mem (A : Matrix E V ℝ) (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) :
    weightedProjection A σ ∈ retractions A := by
  let D := diagonal (fun e => Real.sqrt (σ e))
  let Di := diagonal (fun e => (Real.sqrt (σ e))⁻¹)
  have hDi : Di*D=1 := sqrt_diagonal_inv σ hσ
  have hf := gramProjection_mul_self (D*A)
  constructor
  · change Di*gramProjection (D*A)*D*A=A
    calc
      _ = Di*(gramProjection (D*A)*(D*A)) := by simp only [Matrix.mul_assoc]
      _ = Di*(D*A) := by rw [hf]
      _ = A := by rw [← Matrix.mul_assoc, hDi, Matrix.one_mul]
  · obtain ⟨B,hB⟩ := gramProjection_factor (D*A)
    refine ⟨B*D, ?_⟩
    change Di*gramProjection (D*A)*D=A*(B*D)
    rw [hB]
    calc
      _ = (Di*D)*A*(B*D) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDi, Matrix.one_mul]

lemma hilbertMul_diagonal {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (d : E → ℝ) (x : E → H) (e : E) : hilbertMul (diagonal d) x e = d e • x e := by
  simp [hilbertMul, Matrix.diagonal_apply]

lemma weightedProjection_energy {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Matrix E V ℝ) (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) (x : E → H) :
    (∑ e, σ e * ‖hilbertMul (weightedProjection A σ) x e‖^2) ≤
      ∑ e, σ e * ‖x e‖^2 := by
  let D := diagonal (fun e => Real.sqrt (σ e))
  let Di := diagonal (fun e => (Real.sqrt (σ e))⁻¹)
  let Q := gramProjection (D*A)
  have hDD : D*Di=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (Real.sqrt_pos.2 (hσ _)).ne']
    exact diagonal_one
  have hP : D*weightedProjection A σ=Q*D := by
    change D*(Di*Q*D)=Q*D
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have hen (y : E → H) : (∑ e, ‖hilbertMul D y e‖^2) = ∑ e, σ e*‖y e‖^2 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [hilbertMul_diagonal, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (hσ e)), mul_pow, Real.sq_sqrt (hσ e).le]
  have hc := hilbertMul_contraction Q (gramProjection_symmetric _) (gramProjection_idempotent _)
    (hilbertMul D x)
  rw [← hilbertMul_mul, ← hP, hilbertMul_mul, hen, hen] at hc
  exact hc


def matrixRowNorm (P : Matrix E E ℝ) (e : E) : ℝ := ∑ f, |P e f|

omit [DecidableEq E] in
lemma matrixRowNorm_nonneg (P : Matrix E E ℝ) (e : E) : 0 ≤ matrixRowNorm P e := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [DecidableEq E] [DecidableEq V] in
lemma matrixRowNorm_convex (A : Matrix E V ℝ) (e : E) :
    ConvexOn ℝ (retractions A) (fun P => matrixRowNorm P e) := by
  refine ⟨retractions_convex A, ?_⟩
  intro P hP Q hQ a b ha hb hab
  change (∑ f, |a*P e f+b*Q e f|) ≤ a*(∑ f, |P e f|)+b*(∑ f, |Q e f|)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f _
  simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a*P e f) (b*Q e f)

omit [DecidableEq E] [DecidableEq V] in
lemma projectionEnergy_convex {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Matrix E V ℝ) (lam : E → ℝ) (hlam : ∀ e, 0 ≤ lam e) (x : E → H) :
    ConvexOn ℝ (retractions A) (fun P => ∑ e, lam e * ‖hilbertMul P x e‖^2) := by
  refine ⟨retractions_convex A, ?_⟩
  intro P hP Q hQ a b ha hb hab
  have hn := (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set H))).pow
    (fun _ _ => norm_nonneg _) 2
  simp only [hilbertMul_add, hilbertMul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have hh := hn.2 (Set.mem_univ (hilbertMul P x e)) (Set.mem_univ (hilbertMul Q x e)) ha hb hab
  change ‖a • hilbertMul P x e+b • hilbertMul Q x e‖^2 ≤
    a*‖hilbertMul P x e‖^2+b*‖hilbertMul Q x e‖^2 at hh
  calc
    _ ≤ lam e*(a*‖hilbertMul P x e‖^2+b*‖hilbertMul Q x e‖^2) :=
      mul_le_mul_of_nonneg_left hh (hlam e)
    _ = _ := by ring

def normalizedGradient (src dst : E → V) (δ : E → ℝ) : Matrix E V ℝ :=
  diagonal (fun e => (δ e)⁻¹) * incidence src dst

omit [Fintype V] in
lemma scaled_normalizedGradient (src dst : E → V) (δ σ : E → ℝ)
    (hδ : ∀ e, 0 < δ e) (hσ : ∀ e, 0 < σ e) :
    diagonal (fun e => Real.sqrt (σ e)) * normalizedGradient src dst δ =
      conductorMatrix src dst (fun e => σ e/(δ e)^2) := by
  unfold normalizedGradient conductorMatrix
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 1
  congr 1
  funext e
  rw [Real.sqrt_div (hσ e).le, Real.sqrt_sq (hδ e).le]
  rfl

lemma weightedProjection_rows (src dst : E → V) (δ σ : E → ℝ)
    (hδ : ∀ e, 0 < δ e) (hσ : ∀ e, 0 < σ e) (hsum : ∑ e, σ e = 1)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    (∑ e, σ e * (matrixRowNorm (weightedProjection (normalizedGradient src dst δ) σ) e)^2) ≤
      (2*Real.log (Fintype.card V : ℝ))^2 := by
  let A := normalizedGradient src dst δ
  let Q := gramProjection (conductorMatrix src dst (fun e => σ e/(δ e)^2))
  have hP (e f : E) : weightedProjection A σ e f =
      (Real.sqrt (σ e))⁻¹*Q e f*Real.sqrt (σ f) := by
    simp only [weightedProjection, A, scaled_normalizedGradient src dst δ σ hδ hσ,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Q]
  have hrow (e : E) : Real.sqrt (σ e)*matrixRowNorm (weightedProjection A σ) e =
      ∑ f, |Q e f| *Real.sqrt (σ f) := by
    unfold matrixRowNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [hP, abs_mul, abs_mul, abs_inv, abs_of_pos (Real.sqrt_pos.2 (hσ e)),
      abs_of_pos (Real.sqrt_pos.2 (hσ f))]
    field_simp [(Real.sqrt_pos.2 (hσ e)).ne']
  have hh := electrical_localization_complete src dst (fun e => σ e/(δ e)^2)
    (fun e => Real.sqrt (σ e)) (fun e => div_pos (hσ e) (sq_pos_of_pos (hδ e))) hinc hconn
  simp only [Real.sq_sqrt (hσ _).le, hsum, mul_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro e _
  rw [← hrow, mul_pow, Real.sq_sqrt (hσ e).le]


/-- A simultaneous retraction substitute for the fixed-point reweighting:
it supplies the exact row bound and all finitely many tensor-energy bounds
needed by the two constructions. -/
lemma controlled_retraction {J : Type uJ} {H : Type uH} [Fintype J] [Nonempty E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (x : J → E → H) (hx : ∀ j e, ‖x j e‖^2 ≤ 1) :
    ∃ P ∈ retractions (normalizedGradient src dst δ),
      (∀ e, matrixRowNorm P e ≤ 4*Real.log (Fintype.card V : ℝ)) ∧
      (∀ j, (∑ e, lam e * ‖hilbertMul P (x j) e‖^2) ≤ 4) := by
  let A := normalizedGradient src dst δ
  let L := 2*Real.log (Fintype.card V : ℝ)
  have hL : 0 < L := by
    have : (1:ℝ) < Fintype.card V := by exact_mod_cast (show 1 < Fintype.card V by omega)
    exact mul_pos (by norm_num) (Real.log_pos this)
  let r (e : E) (P : Matrix E E ℝ) := (matrixRowNorm P e)^2/L^2
  let q (j : J) (P : Matrix E E ℝ) := ∑ e, lam e*‖hilbertMul P (x j) e‖^2
  have hrc (e : E) : ConvexOn ℝ (retractions A) (r e) := by
    have hh := ((matrixRowNorm_convex A e).pow (fun P _ => matrixRowNorm_nonneg P e) 2).smul
      (show 0 ≤ (L^2)⁻¹ by positivity)
    simpa only [r, Pi.pow_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
  have hqc (j : J) : ConvexOn ℝ (retractions A) (q j) :=
    projectionEnergy_convex A lam (fun e => (hlam e).le) (x j)
  have hrn (e : E) (P : Matrix E E ℝ) (_hP : P ∈ retractions A) : 0 ≤ r e P := by
    dsimp [r]; positivity
  have hqn (j : J) (P : Matrix E E ℝ) (_hP : P ∈ retractions A) : 0 ≤ q j P := by
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (hlam e).le (sq_nonneg _))
  have htest : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ P ∈ retractions A, (∑ e, w e*r e P) ≤ 2 ∧ ∀ j, q j P ≤ 2 := by
    intro w hw hws
    let σ (e : E) := (lam e+w e)/2
    have hσ (e : E) : 0 < σ e := div_pos (add_pos (hlam e) (hw e)) (by norm_num)
    have hσs : ∑ e, σ e=1 := by simp only [σ, ← Finset.sum_div, Finset.sum_add_distrib, hls, hws]; norm_num
    have hlσ (e : E) : lam e ≤ 2*σ e := by dsimp [σ]; linarith [hw e]
    have hwσ (e : E) : w e ≤ 2*σ e := by dsimp [σ]; linarith [hlam e]
    let P := weightedProjection A σ
    refine ⟨P, weightedProjection_mem A σ hσ, ?_, ?_⟩
    · have hh := weightedProjection_rows src dst δ σ hδ hσ hσs hinc hconn
      change (∑ e, σ e*(matrixRowNorm P e)^2) ≤ L^2 at hh
      have hnum : (∑ e, w e*(matrixRowNorm P e)^2) ≤ 2*L^2 := by
        calc
          _ ≤ ∑ e, (2*σ e)*(matrixRowNorm P e)^2 := Finset.sum_le_sum (fun e _ =>
            mul_le_mul_of_nonneg_right (hwσ e) (sq_nonneg _))
          _ = 2*∑ e, σ e*(matrixRowNorm P e)^2 := by simp only [mul_assoc, Finset.mul_sum]
          _ ≤ 2*L^2 := by linarith
      have he : (∑ e, w e*r e P) = (∑ e, w e*(matrixRowNorm P e)^2)/L^2 := by
        simp only [r, mul_div_assoc, Finset.sum_div]
      rw [he]
      exact (div_le_iff₀ (sq_pos_of_pos hL)).2 hnum
    · intro j
      change (∑ e, lam e*‖hilbertMul P (x j) e‖^2) ≤ 2
      calc
        _ ≤ 2*∑ e, σ e*‖hilbertMul P (x j) e‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro e _
          nlinarith [mul_le_mul_of_nonneg_right (hlσ e) (sq_nonneg ‖hilbertMul P (x j) e‖)]
        _ ≤ 2*∑ e, σ e*‖x j e‖^2 := by
          exact mul_le_mul_of_nonneg_left (weightedProjection_energy A σ hσ (x j)) (by norm_num)
        _ ≤ 2*∑ e, σ e*1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hx j e) (hσ e).le)
        _ = 2 := by simp only [mul_one, hσs]
  obtain ⟨P,hP,hr,hq⟩ := simultaneous_convex_cost_selection (retractions_convex A)
    r q hrc hqc hrn hqn htest
  refine ⟨P,hP,fun e => ?_,fun j => (hq j).le⟩
  have hh := (div_lt_iff₀ (sq_pos_of_pos hL)).mp (hr e)
  have hn := matrixRowNorm_nonneg P e
  have hh' : matrixRowNorm P e ≤ 2*L := by nlinarith
  dsimp [L] at hh'
  linarith

end WeightedProjection

end SubpolynomialLp

end

end OAI
