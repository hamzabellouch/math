import OAI.Analysis.LiebThirring.Model

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
namespace SharpLiebThirring


/-! ## The matrix field and action -/

/-- The regularized primitive, including beta = 0 without a special convention. -/
def regularizedPrimitive (σ δ y : ℝ) : ℝ :=
  ∫ t in 0..y, (max t 0 + δ) ^ (σ - 3 / 2)

def fieldNormalization (σ : ℝ) : ℝ :=
  σ / ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)

def scalarMu (σ δ z : ℝ) : ℝ :=
  fieldNormalization σ * ∫ s : ℝ,
    regularizedPrimitive σ δ (s ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2)

section FieldDefinitions
variable {N : ℕ}

def matrixX (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i ↦ (k i) ^ 2) - (2 * s) • B + (s ^ 2) • 1

/-- The symmetric cutoff is part of the definition, not replaced
by a potentially non-absolutely-convergent whole-line Bochner integral. -/
def truncatedField (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ)
    (R : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fieldNormalization σ • ∫ s in (-R)..R,
    cfc (regularizedPrimitive σ δ) (matrixX k B s) -
      regularizedPrimitive σ δ (s ^ 2) • 1

/-- The symmetric-cutoff limit, whose convergence and local regularity are proved below. -/
def matrixField (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Filter.limUnder Filter.atTop (truncatedField σ δ k B)

def fieldPrimitive (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  -(∫ t in (0 : ℝ)..1, Matrix.trace (B * matrixField σ δ k (t • B)))

/-- The rank-one comparison for the symmetric-cutoff matrix field. -/
def RankOneClaim : Prop :=
  ∀ (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ),
    0 < σ → σ < 1 → 0 < δ → (∀ i, 0 < k i) → B.IsHermitian →
    matrixField σ δ k B = Matrix.vecMulVec a a →
    (∑ i, a i * ((Matrix.diagonal (fun i ↦ (k i) ^ 2) - B ^ 2) *ᵥ a) i) ≥
      (∑ i, (a i) ^ 2) ^ (1 + 1 / σ)
end FieldDefinitions

/-- The real continuous representative of H¹₀ on a bounded interval. -/
structure H10 (l r : ℝ) where
  val : ℝ → ℝ
  grad : ℝ → ℝ
  val_memLp : MemLp val 2 (volume.restrict (Set.Ioo l r))
  grad_memLp : MemLp grad 2 (volume.restrict (Set.Ioo l r))
  continuous_val : ContinuousOn val (Set.Icc l r)
  left_zero : val l = 0
  right_zero : val r = 0
  weak_derivative : ∀ φ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    Function.support φ ⊆ Set.Ioo l r →
    (∫ x in Set.Ioo l r, val x * deriv φ x) = -(∫ x in Set.Ioo l r, grad x * φ x)

def LowerTriangular {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, i < j → C i j = 0

def finiteIntervalAction {N : ℕ} {l r : ℝ}
    (σ : ℝ) (k : Fin N → ℝ) (u : Fin N → H10 l r)
    (C : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∫ x in Set.Ioo l r,
    (∑ i, (C *ᵥ (fun j ↦ (u j).grad x)) i ^ 2) +
      (∑ i, (k i) ^ 2 * (C *ᵥ (fun j ↦ (u j).val x)) i ^ 2) -
      (∑ i, (C *ᵥ (fun j ↦ (u j).val x)) i ^ 2) ^ (1 + 1 / σ)

/-- The action inequality, with an extended-real supremum so boundedness is not implicit. -/
def ActionClaim : Prop :=
  ∀ (N : ℕ) (l r σ : ℝ) (k : Fin N → ℝ) (u : Fin N → H10 l r),
    l < r → 0 < σ → σ < 1 → (∀ i, 0 < k i) →
    (∀ i j, (∫ x in Set.Ioo l r, (u i).val x * (u j).val x) =
      if i = j then 1 else 0) →
    (((∑ i, ∫ s in (-(k i))..(k i), ((k i) ^ 2 - s ^ 2) ^ σ) : ℝ) : EReal) ≤
      ⨆ (C : Matrix (Fin N) (Fin N) ℝ) (_ : LowerTriangular C),
        (finiteIntervalAction σ k u C : EReal)


open Matrix Unitary
namespace MatrixProof
variable {n : Type u1} [Fintype n] [DecidableEq n]

lemma monotone_sub_mul_nonneg {f : ℝ → ℝ} (hf : Monotone f) (x y : ℝ) :
    0 ≤ (f x - f y) * (x - y) := by
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr h)
  · exact mul_nonneg (sub_nonneg.mpr (hf h)) (sub_nonneg.mpr h)

omit [DecidableEq n] in
lemma trace_star_mul_sum (A B : Matrix n n ℂ) :
    (trace (star A * B)).re = ∑ i, ∑ j, (star (A i j) * B i j).re := by
  simp only [trace, diag, mul_apply, star_eq_conjTranspose, conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  exact Finset.sum_comm

lemma trace_star_mul_change (U V : unitary (Matrix n n ℂ)) (A B : Matrix n n ℂ) :
    trace (star (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) *
      (star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ))) = trace (star A * B) := by
  have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  have hv : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem V.property
  simp only [star_mul, star_star]
  calc
    _ = trace (star (V : Matrix n n ℂ) * (star A *
          ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ))) * B * (V : Matrix n n ℂ)) := by
      congr 1
      noncomm_ring
    _ = trace (star (V : Matrix n n ℂ) * (star A * B) * (V : Matrix n n ℂ)) := by simp [hu, mul_assoc]
    _ = trace ((V : Matrix n n ℂ) * star (V : Matrix n n ℂ) * (star A * B)) :=
      trace_mul_cycle _ _ _
    _ = trace (star A * B) := by rw [hv, one_mul]

lemma mixed_diagonal_sub (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ) =
      diagonal (fun i ↦ (a i : ℂ)) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
        (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) := by
  simp only [conjStarAlgAut_apply]
  calc
    _ = (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * diagonal (fun i ↦ (a i : ℂ)) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) *
          (star (V : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by noncomm_ring
    _ = _ := by simp only [Unitary.coe_star_mul_self, one_mul, mul_one]

lemma mixed_diagonal_sub_apply (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (i j : n) :
    (star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ)) i j =
      ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
  rw [mixed_diagonal_sub]
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, Complex.ofReal_sub]
  ring

lemma trace_functional_monotonicity {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f : ℝ → ℝ} (hf : Monotone f) :
    0 ≤ (trace ((hA.cfc f - hB.cfc f) * (A - B))).re := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  have hfab : (hA.cfc f - hB.cfc f).IsHermitian := by
    apply IsHermitian.sub
    · rw [← hA.cfc_eq]
      exact (cfc_predicate f A).isHermitian
    · rw [← hB.cfc_eq]
      exact (cfc_predicate f B).isHermitian
  have ha : A = conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) :=
    hA.spectral_theorem
  have hb : B = conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ))) :=
    hB.spectral_theorem
  have hfm (i j : n) :
      (star (U : Matrix n n ℂ) * (hA.cfc f - hB.cfc f) * (V : Matrix n n ℂ)) i j =
        ((f (a i) - f (b j) : ℝ) : ℂ) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    exact mixed_diagonal_sub_apply U V (f ∘ a) (f ∘ b) i j
  have hm (i j : n) :
      (star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ)) i j =
        ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    rw [ha, hb]
    exact mixed_diagonal_sub_apply U V a b i j
  rw [← hfab.star_eq, ← trace_star_mul_change U V, trace_star_mul_sum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  rw [hfm, hm]
  have heq (s t : ℝ) (z : ℂ) :
      (star ((s : ℂ) * z) * ((t : ℂ) * z)).re = (s * t) * Complex.normSq z := by
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  rw [heq]
  exact mul_nonneg (monotone_sub_mul_nonneg hf _ _) (Complex.normSq_nonneg _)


lemma trace_unitary_conjugate (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    trace (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = trace A := by
  simp only [conjStarAlgAut_apply]
  rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma trace_conjugate_pair (U : unitary (Matrix n n ℂ)) (F A : Matrix n n ℂ) :
    trace (conjStarAlgAut ℂ (Matrix n n ℂ) U F * A) =
      trace (F * conjStarAlgAut ℂ (Matrix n n ℂ) (star U) A) := by
  simp only [conjStarAlgAut_apply, Unitary.coe_star, star_star]
  calc
    _ = trace ((U : Matrix n n ℂ) * (F * (star (U : Matrix n n ℂ) * A))) := by
      congr 1
      noncomm_ring
    _ = trace ((F * (star (U : Matrix n n ℂ) * A)) * (U : Matrix n n ℂ)) :=
      trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

lemma trace_conjugate_difference (U : unitary (Matrix n n ℂ)) (F A : Matrix n n ℂ) :
    trace ((conjStarAlgAut ℂ (Matrix n n ℂ) U F - F) * (conjStarAlgAut ℂ (Matrix n n ℂ) U A - A)) =
      trace (F * (2 • A - conjStarAlgAut ℂ (Matrix n n ℂ) U A -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star U) A)) := by
  have h1 : trace (conjStarAlgAut ℂ (Matrix n n ℂ) U F * conjStarAlgAut ℂ (Matrix n n ℂ) U A) =
      trace (F * A) := by
    rw [← map_mul, trace_unitary_conjugate]
  simp only [mul_sub, sub_mul, trace_sub, h1, trace_conjugate_pair, two_smul,
    mul_add, trace_add]
  ring

lemma hermitian_unitary_conjugate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) : (conjStarAlgAut ℂ (Matrix n n ℂ) U A).IsHermitian := by
  change star (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = conjStarAlgAut ℂ (Matrix n n ℂ) U A
  rw [← map_star, hA.star_eq]

lemma functional_unitary_conjugate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) :
    (hermitian_unitary_conjugate hA U).cfc f = conjStarAlgAut ℂ (Matrix n n ℂ) U (hA.cfc f) := by
  rw [← IsHermitian.cfc_eq, ← hA.cfc_eq]
  symm
  exact StarAlgHomClass.map_cfc (conjStarAlgAut ℂ (Matrix n n ℂ) U) f A
    (A.finite_real_spectrum.continuousOn f) (by
      change Continuous (fun X : Matrix n n ℂ ↦ conjStarAlgAut ℂ (Matrix n n ℂ) U X)
      simp only [conjStarAlgAut_apply]
      fun_prop) hA
    (hermitian_unitary_conjugate hA U)

/-- The fixed-unitary trace comparison used before averaging. -/
lemma trace_unitary_comparison {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : Monotone f) (U : unitary (Matrix n n ℂ)) :
    0 ≤ (trace (hA.cfc f * (2 • A - conjStarAlgAut ℂ (Matrix n n ℂ) U A -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) A))).re := by
  have h := trace_functional_monotonicity (hermitian_unitary_conjugate hA U) hA hf
  rw [functional_unitary_conjugate, trace_conjugate_difference] at h
  exact h

/-- Removing any invariant part, such as (s I - B)^2, is an exact identity. -/
lemma conjugate_difference_sub_invariant (U : unitary (Matrix n n ℂ))
    (D Y : Matrix n n ℂ) (hY : conjStarAlgAut ℂ (Matrix n n ℂ) U Y = Y) :
    2 • (D + Y) - conjStarAlgAut ℂ (Matrix n n ℂ) U (D + Y) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star U) (D + Y) =
      2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D - conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D := by
  have hYs : conjStarAlgAut ℂ (Matrix n n ℂ) (star U) Y = Y := by
    calc
      _ = conjStarAlgAut ℂ (Matrix n n ℂ) (star U) (conjStarAlgAut ℂ (Matrix n n ℂ) U Y) := by rw [hY]
      _ = Y := by rw [← conjStarAlgAut_mul_apply]; simp
  rw [map_add, map_add, hY, hYs]
  simp only [two_smul]
  abel

lemma trace_unitary_comparison_sub_invariant {D Y : Matrix n n ℂ}
    (hA : (D + Y).IsHermitian) {f : ℝ → ℝ} (hf : Monotone f)
    (U : unitary (Matrix n n ℂ)) (hY : conjStarAlgAut ℂ (Matrix n n ℂ) U Y = Y) :
    0 ≤ (trace (hA.cfc f * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re := by
  have h := trace_unitary_comparison hA hf U
  rwa [conjugate_difference_sub_invariant U D Y hY] at h


/-- The squared Hilbert--Schmidt norm, without changing the ambient matrix norm. -/
def hsSquared (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

omit [DecidableEq n] in
lemma hsSquared_eq_trace (A : Matrix n n ℂ) :
    hsSquared A = (trace (star A * A)).re := by
  rw [trace_star_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma hsSquared_change (U V : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    hsSquared (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) = hsSquared A := by
  rw [hsSquared_eq_trace, trace_star_mul_change, hsSquared_eq_trace]

/-- The finite-dimensional Hilbert--Schmidt calculus estimate,
proved in mixed eigenbases. -/
lemma hsSquared_cfc_sub {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) :
    hsSquared (hA.cfc f - hB.cfc f) ≤ L ^ 2 * hsSquared (A - B) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  have ha : A = conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) :=
    hA.spectral_theorem
  have hb : B = conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ))) :=
    hB.spectral_theorem
  have hfm (i j : n) :
      (star (U : Matrix n n ℂ) * (hA.cfc f - hB.cfc f) * (V : Matrix n n ℂ)) i j =
        ((f (a i) - f (b j) : ℝ) : ℂ) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j :=
    mixed_diagonal_sub_apply U V (f ∘ a) (f ∘ b) i j
  have hm (i j : n) :
      (star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ)) i j =
        ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    rw [ha, hb]
    exact mixed_diagonal_sub_apply U V a b i j
  rw [← hsSquared_change U V (hA.cfc f - hB.cfc f),
    ← hsSquared_change U V (A - B)]
  simp only [hsSquared, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [hfm, hm, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  have hh := sq_le_sq₀ (abs_nonneg (f (a i) - f (b j)))
    (mul_nonneg hL (abs_nonneg (a i - b j))) |>.2 (hf i j)
  rw [sq_abs, mul_pow, sq_abs] at hh
  nlinarith [mul_le_mul_of_nonneg_right hh
    (Complex.normSq_nonneg ((star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j))]

open MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal

/-- Real trace pairing as a continuous linear functional. -/
def tracePairCLM (M : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  (Complex.reCLM).comp
    ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.comp
      ((LinearMap.mulLeft ℝ M).toContinuousLinearMap))

@[simp] lemma tracePairCLM_apply (M Z : Matrix n n ℂ) :
    tracePairCLM M Z = (trace (M * Z)).re := rfl

/-- Trace comparison commutes with limits in matrix norm. -/
lemma trace_unitary_comparison_limit {ι : Type u2} {l : Filter ι} [l.NeBot]
    {F : ι → Matrix n n ℂ} {M D : Matrix n n ℂ}
    (hlim : Filter.Tendsto F l (nhds M)) (U : unitary (Matrix n n ℂ))
    (hF : ∀ᶠ i in l, 0 ≤ (trace (F i * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re) :
    0 ≤ (trace (M * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re := by
  apply ge_of_tendsto ?_ hF
  have hc : Continuous (fun X : Matrix n n ℂ ↦
      (trace (X * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re) := by
    unfold trace diag
    fun_prop
  exact hc.continuousAt.tendsto.comp hlim

/-- The integration step in `trace-average`, for any symmetric probability
average. The symmetry needed is expressed by equality of the two integrals. -/
lemma trace_comparison_average {α : Type u3} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (U : α → unitary (Matrix n n ℂ))
    (M D : Matrix n n ℂ)
    (hU : Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D) ν)
    (hUs : Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D) ν)
    (hsym : (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D ∂ν) =
      ∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D ∂ν)
    (hpoint : ∀ᵐ t ∂ν, 0 ≤ (trace (M * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D))).re) :
    (trace (M * (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D ∂ν))).re ≤
      (trace (M * D)).re := by
  have hi : Integrable (fun t ↦ 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D) ν :=
    ((integrable_const (2 • D)).sub hU).sub hUs
  have hn := integral_nonneg_of_ae hpoint
  change 0 ≤ ∫ t, tracePairCLM M
    (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D - conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D) ∂ν at hn
  rw [(tracePairCLM M).integral_comp_comm hi,
    integral_sub (f := fun t ↦ 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D)
      ((integrable_const (2 • D)).sub hU) hUs,
    integral_sub (f := fun _ : α ↦ 2 • D) (integrable_const (2 • D)) hU, integral_const, probReal_univ,
    one_smul, hsym, map_sub, map_sub, map_nsmul] at hn
  norm_num only [tracePairCLM_apply, nsmul_eq_mul, Nat.cast_ofNat] at hn
  linarith


/-- In a fixed eigenbasis of B, the unitary exp(itB). -/
def phaseUnitary (z : n → ℝ) (t : ℝ) : unitary (Matrix n n ℂ) :=
  ⟨diagonal (fun i ↦ Complex.exp ((t * z i : ℝ) * Complex.I)), by
    constructor
    · simp only [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext i
      simp only [Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    · simp only [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext i
      simp only [Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp⟩

lemma phaseUnitary_conj_apply (z : n → ℝ) (t : ℝ) (D : Matrix n n ℂ) (i j : n) :
    conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D i j =
      Complex.exp (((z i - z j) * t : ℝ) * Complex.I) * D i j := by
  simp only [conjStarAlgAut_apply, phaseUnitary, star_eq_conjTranspose,
    diagonal_conjTranspose, diagonal_mul, mul_diagonal]
  simp only [Pi.star_apply]
  rw [Complex.star_def, ← Complex.exp_conj]
  calc _ = (Complex.exp (((t * z i : ℝ) : ℂ) * Complex.I) *
      Complex.exp (starRingEnd ℂ (((t * z j : ℝ) : ℂ) * Complex.I))) * D i j := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring

lemma phaseUnitary_star (z : n → ℝ) (t : ℝ) :
    star (phaseUnitary z t) = phaseUnitary z (-t) := by
  apply Subtype.ext
  simp only [Unitary.coe_star, phaseUnitary, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

lemma continuous_phase_conj (z : n → ℝ) (D : Matrix n n ℂ) :
    Continuous (fun t : ℝ ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [phaseUnitary_conj_apply]
  fun_prop

lemma integrable_phase_conj (z : n → ℝ) (D : Matrix n n ℂ) (ν : Measure ℝ)
    [IsFiniteMeasure ν] :
    Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D) ν := by
  apply Integrable.of_bound (continuous_phase_conj z D).aestronglyMeasurable ‖D‖
  filter_upwards [] with t
  change ‖(phaseUnitary z t : Matrix n n ℂ) * D *
    ((star (phaseUnitary z t) : unitary (Matrix n n ℂ)) : Matrix n n ℂ)‖ ≤ ‖D‖
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

/-- Entry evaluation is a continuous linear functional even for the operator norm. -/
def entryCLM (i j : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  ({ toFun := fun D ↦ D i j
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } : Matrix n n ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] lemma entryCLM_apply (i j : n) (D : Matrix n n ℂ) : entryCLM i j D = D i j := rfl

lemma gaussian_phase_average (z : n → ℝ) (D : Matrix n n ℂ) (v : ℝ≥0) (i j : n) :
    (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D ∂ProbabilityTheory.gaussianReal 0 v) i j =
      Complex.exp (-((v : ℝ) * (z i - z j) ^ 2 / 2 : ℝ)) * D i j := by
  have h := (entryCLM i j).integral_comp_comm
    (integrable_phase_conj z D (ProbabilityTheory.gaussianReal 0 v))
  simp only [entryCLM_apply] at h
  rw [← h]
  simp_rw [phaseUnitary_conj_apply]
  rw [integral_mul_const]
  simp only [Complex.ofReal_mul]
  rw [← charFun_apply_real, ProbabilityTheory.charFun_gaussianReal]
  congr 2
  push_cast
  ring

lemma gaussian_phase_star_average (z : n → ℝ) (D : Matrix n n ℂ) (v : ℝ≥0) :
    (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D
      ∂ProbabilityTheory.gaussianReal 0 v) =
      ∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D
        ∂ProbabilityTheory.gaussianReal 0 v := by
  simp_rw [phaseUnitary_star]
  have hm : (ProbabilityTheory.gaussianReal 0 v).map (fun x : ℝ ↦ -x) =
      ProbabilityTheory.gaussianReal 0 v := by
    simpa using (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := v))
  have he := integral_map (μ := ProbabilityTheory.gaussianReal 0 v)
    (φ := fun x : ℝ ↦ -x) (by fun_prop)
    ((continuous_phase_conj z D).aestronglyMeasurable
      (μ := (ProbabilityTheory.gaussianReal 0 v).map (fun x : ℝ ↦ -x)))
  rw [hm] at he
  exact he.symm

lemma integrable_gaussian_phase_star (z : n → ℝ) (D : Matrix n n ℂ) (v : ℝ≥0) :
    Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D)
      (ProbabilityTheory.gaussianReal 0 v) := by
  simp_rw [phaseUnitary_star]
  have hm : (ProbabilityTheory.gaussianReal 0 v).map (fun x : ℝ ↦ -x) =
      ProbabilityTheory.gaussianReal 0 v := by
    simpa using (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := v))
  have hi := integrable_phase_conj z D (ProbabilityTheory.gaussianReal 0 v)
  rw [← hm] at hi
  exact hi.comp_measurable (by fun_prop)

/-- The Gaussian stage of the even-unitary trace contraction. -/
lemma gaussian_trace_comparison (z : n → ℝ) (M D : Matrix n n ℂ) (v : ℝ≥0)
    (hpoint : ∀ t : ℝ, 0 ≤ (trace (M * (2 • D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D))).re) :
    (trace (M * (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D
      ∂ProbabilityTheory.gaussianReal 0 v))).re ≤ (trace (M * D)).re := by
  exact trace_comparison_average (ProbabilityTheory.gaussianReal 0 v)
    (phaseUnitary z) M D (integrable_phase_conj z D _)
    (integrable_gaussian_phase_star z D v) (gaussian_phase_star_average z D v)
    (Filter.Eventually.of_forall hpoint)

end MatrixProof

open MeasureTheory Set Filter
open scoped Topology
namespace ScalarProof

lemma derivative_continuous (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun t : ℝ ↦ (max t 0 + δ) ^ (σ - 3 / 2)) := by
  apply Continuous.rpow_const
  · fun_prop
  · intro t
    left
    positivity

lemma primitive_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (regularizedPrimitive σ δ) ((max y 0 + δ) ^ (σ - 3 / 2)) y := by
  have hc := derivative_continuous σ hδ
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma primitive_deriv (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    deriv (regularizedPrimitive σ δ) y = (max y 0 + δ) ^ (σ - 3 / 2) :=
  (primitive_hasDerivAt σ hδ y).deriv

lemma primitive_differentiable (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Differentiable ℝ (regularizedPrimitive σ δ) :=
  fun y ↦ (primitive_hasDerivAt σ hδ y).differentiableAt

lemma primitive_strictMono (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    StrictMono (regularizedPrimitive σ δ) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [primitive_deriv σ hδ]
  exact Real.rpow_pos_of_pos (by positivity) _

lemma primitive_concave {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    ConcaveOn ℝ univ (regularizedPrimitive σ δ) := by
  apply Antitone.concaveOn_univ_of_deriv (primitive_differentiable σ hδ)
  intro x y hxy
  rw [primitive_deriv σ hδ, primitive_deriv σ hδ]
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (add_le_add (max_le_max hxy le_rfl) le_rfl) (by linarith)

@[simp] lemma primitive_zero (σ δ : ℝ) : regularizedPrimitive σ δ 0 = 0 := by
  simp [regularizedPrimitive]

lemma primitive_nonneg (σ : ℝ) {δ y : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y) :
    0 ≤ regularizedPrimitive σ δ y := by
  simpa using (primitive_strictMono σ hδ).monotone hy

lemma normalization_integrable {σ : ℝ} (hσ : σ < 1) :
    Integrable (fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2)) := by
  have h : (Module.finrank ℝ ℝ : ℝ) < 3 - 2 * σ := by
    norm_num only [Module.finrank_self, Nat.cast_one]
    linarith
  have he := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) h
  convert he using 1
  ext s
  congr 1
  · simp
  · ring

lemma normalization_integral_pos {σ : ℝ} (hσ : σ < 1) :
    0 < ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2) := by
  apply integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (normalization_integrable hσ) |>.2
  have hs : Function.support (fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp

lemma normalization_pos {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    0 < fieldNormalization σ :=
  div_pos hσ₀ (normalization_integral_pos hσ₁)

@[simp] lemma mu_zero (σ δ : ℝ) : scalarMu σ δ 0 = 0 := by
  simp [scalarMu]


/-- A global comparison with the Japanese-bracket integrable majorant, including
negative shifts. It supplies all scalar dominated-convergence bounds. -/
lemma shifted_base_lower {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    (δ / (δ + |z| + 1)) * (1 + s ^ 2) ≤ max (s ^ 2 + z) 0 + δ := by
  have hd : 0 < δ + |z| + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  have hm : 0 ≤ max (s ^ 2 + z) 0 := le_max_right _ _
  have hh : s ^ 2 ≤ max (s ^ 2 + z) 0 + |z| := by
    have := le_max_left (s ^ 2 + z) 0
    have := neg_le_abs z
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hh hδ.le,
    mul_nonneg (abs_nonneg z) hm, mul_nonneg (abs_nonneg z) hδ.le]

lemma shifted_derivative_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) := by
  have ha : 0 < δ / (δ + |z| + 1) := by positivity
  refine ((normalization_integrable hσ).const_mul
    ((δ / (δ + |z| + 1)) ^ (σ - 3 / 2))).mono' ?_ ?_
  · exact ((derivative_continuous σ hδ).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [← Real.mul_rpow ha.le (by positivity : 0 ≤ 1 + s ^ 2)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (shifted_base_lower hδ z s) (by linarith)

lemma primitive_difference_bound {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z s : ℝ) :
    ‖regularizedPrimitive σ δ (s ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2)‖ ≤
      (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) * |z| := by
  have hd : ∀ y ∈ Ici (s ^ 2 - |z|),
      ‖(max y 0 + δ) ^ (σ - 3 / 2)‖ ≤
        (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max hy le_rfl) le_rfl) (by linarith)
  have hs : s ^ 2 ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := abs_nonneg z
    linarith
  have hsz : s ^ 2 + z ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := neg_le_abs z
    linarith
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
    (convex_Ici (s ^ 2 - |z|)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ ↦ (primitive_hasDerivAt σ hδ y).hasDerivWithinAt) hd hs hsz

lemma mu_integrand_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) := by
  have hi := (shifted_derivative_integrable hσ hδ (-|z|)).mul_const |z|
  refine hi.mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (((primitive_differentiable σ hδ).continuous.comp (by fun_prop)).sub
      ((primitive_differentiable σ hδ).continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro s
    simpa only [sub_eq_add_neg] using primitive_difference_bound hσ hδ z s

lemma mu_hasDerivAt_integral {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    HasDerivAt (scalarMu σ δ)
      (fieldNormalization σ * ∫ s : ℝ, (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) z := by
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Ioi (z - 1)) (x₀ := z)
    (F := fun y s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + y) -
      regularizedPrimitive σ δ (s ^ 2))
    (F' := fun y s : ℝ ↦ (max (s ^ 2 + y) 0 + δ) ^ (σ - 3 / 2))
    (bound := fun s : ℝ ↦ (max (s ^ 2 + (z - 1)) 0 + δ) ^ (σ - 3 / 2))
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall (fun y ↦ (mu_integrand_integrable hσ hδ y).aestronglyMeasurable))
    (mu_integrand_integrable hσ hδ z)
    (shifted_derivative_integrable hσ hδ z).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s y hy ↦ ?_))
    (shifted_derivative_integrable hσ hδ (z - 1))
    (Filter.Eventually.of_forall (fun s y _ ↦ ?_))
  · exact hh.2.const_mul (fieldNormalization σ)
  · change z - 1 < y at hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max (by linarith) le_rfl) le_rfl) (by linarith)
  · simpa using ((primitive_hasDerivAt σ hδ (s ^ 2 + y)).comp y
      ((hasDerivAt_id y).const_add (s ^ 2))).sub_const (regularizedPrimitive σ δ (s ^ 2))

lemma mu_strictMono {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    StrictMono (scalarMu σ δ) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(mu_hasDerivAt_integral hσ₁ hδ z).deriv]
  apply mul_pos (normalization_pos hσ₀ hσ₁)
  apply (integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (shifted_derivative_integrable hσ₁ hδ z)).2
  have hs : Function.support (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp

/-- The scaling integral used in the evaluation of the scalar field. -/
lemma quadratic_integral_scale (t : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ s : ℝ, (s ^ 2 + a) ^ t) =
      a ^ (t + 1 / 2) * ∫ s : ℝ, (1 + s ^ 2) ^ t := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have he (s : ℝ) : (s ^ 2 + a) ^ t =
      a ^ t * (1 + (s / Real.sqrt a) ^ 2) ^ t := by
    rw [← Real.mul_rpow ha.le (by positivity)]
    congr 1
    rw [div_pow, Real.sq_sqrt ha.le]
    field_simp
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_div (fun s : ℝ ↦ (1 + s ^ 2) ^ t),
    abs_of_pos hs, smul_eq_mul, ← mul_assoc, Real.sqrt_eq_rpow,
    ← Real.rpow_add ha]

lemma mu_hasDerivAt_nonneg {σ δ z : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hz : 0 ≤ z) :
    HasDerivAt (scalarMu σ δ) (σ * (z + δ) ^ (σ - 1)) z := by
  have hh := mu_hasDerivAt_integral hσ hδ z
  have he (s : ℝ) : (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2) =
      (s ^ 2 + (z + δ)) ^ (σ - 3 / 2) := by
    rw [max_eq_left (by positivity)]
    congr 1
    ring
  simp_rw [he] at hh
  rw [quadratic_integral_scale _ (by positivity : 0 < z + δ)] at hh
  have hp := (normalization_integral_pos hσ).ne'
  convert hh using 1
  unfold fieldNormalization
  rw [show σ - 3 / 2 + 1 / 2 = σ - 1 by ring]
  rw [mul_comm ((z + δ) ^ (σ - 1)), ← mul_assoc, div_mul_cancel₀ _ hp]

lemma mu_eq_nonneg {σ δ z : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hz : 0 ≤ z) :
    scalarMu σ δ z = (z + δ) ^ σ - δ ^ σ := by
  have hd (y : ℝ) (hy : 0 ≤ y) :
      HasDerivAt (fun x : ℝ ↦ (x + δ) ^ σ - δ ^ σ)
        (σ * (y + δ) ^ (σ - 1)) y := by
    convert! (((hasDerivAt_id y).add_const δ).rpow_const (p := σ)
      (Or.inl (by positivity : y + δ ≠ 0))).sub_const (δ ^ σ) using 1
    simp
  exact eq_of_has_deriv_right_eq
    (fun y hy ↦ (mu_hasDerivAt_nonneg hσ hδ hy.1).hasDerivWithinAt)
    (fun y hy ↦ (hd y hy.1).hasDerivWithinAt)
    (continuous_iff_continuousAt.mpr (fun y ↦
      (mu_hasDerivAt_integral hσ hδ y).continuousAt)).continuousOn
    (fun y hy ↦ (hd y hy.1).continuousAt.continuousWithinAt)
    (by simp) z ⟨hz, le_rfl⟩


/-- Normalized Gamma mixing density, used only on the positive half-line. -/
def gammaWeight (σ v : ℝ) : ℝ :=
  (Real.Gamma (1 - σ))⁻¹ * (v ^ (-σ) * Real.exp (-v))

lemma gammaWeight_nonneg {σ v : ℝ} (hσ : σ < 1) (hv : 0 ≤ v) :
    0 ≤ gammaWeight σ v := by
  unfold gammaWeight
  exact mul_nonneg (inv_nonneg.2 (Real.Gamma_pos_of_pos (by linarith)).le)
    (mul_nonneg (Real.rpow_nonneg hv _) (Real.exp_pos _).le)

lemma gammaWeight_integrable {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (gammaWeight σ) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -σ) (p := 1) (b := 1)
    (by linarith) zero_lt_one zero_lt_one
  simp only [Real.rpow_one, neg_one_mul] at hi
  exact hi.const_mul _

lemma gamma_mixture {σ h x : ℝ} (hσ : σ < 1) (hh : 0 ≤ h) :
    (∫ v in Ioi (0 : ℝ), gammaWeight σ v * Real.exp (-v * h * x ^ 2)) =
      (1 + h * x ^ 2) ^ (σ - 1) := by
  have hb : 0 < 1 + h * x ^ 2 := by positivity
  have hg : Real.Gamma (1 - σ) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have he (v : ℝ) : gammaWeight σ v * Real.exp (-v * h * x ^ 2) =
      (Real.Gamma (1 - σ))⁻¹ * (v ^ (-σ) * Real.exp (-(1 + h * x ^ 2) * v ^ (1 : ℝ))) := by
    unfold gammaWeight
    rw [mul_assoc, mul_assoc, ← Real.exp_add, Real.rpow_one]
    congr 3
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow zero_lt_one (by linarith) hb]
  simp only [div_one, mul_one]
  rw [show -σ + 1 = 1 - σ by ring, show -(1 - σ) = σ - 1 by ring]
  rw [← mul_assoc, mul_comm _ ((1 + h * x ^ 2) ^ (σ - 1)), mul_assoc,
    inv_mul_cancel₀ hg, mul_one]

lemma gammaWeight_integral {σ : ℝ} (hσ : σ < 1) :
    (∫ v in Ioi (0 : ℝ), gammaWeight σ v) = 1 := by
  simpa using gamma_mixture (h := 0) (x := 0) hσ le_rfl

/-- Integrability of the scalar kernel used in the matrix resolvent tangent formula. -/
lemma resolvent_kernel_integrable {β a : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (ha : 0 < a) : IntegrableOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioi 0) := by
    apply ContinuousOn.div
    · exact continuousOn_id.rpow_const (fun v hv ↦ Or.inl (ne_of_gt hv))
    · fun_prop
    · intro v hv
      exact pow_ne_zero _ (ne_of_gt (add_pos ha hv) : a + v ≠ 0)
  have hn : IntegrableOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioo 0 1) := by
    have hi : IntegrableOn (fun v : ℝ ↦ v ^ β * (a ^ 2)⁻¹) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hβ₀).mul_const _
    apply hi.mono' ((hc.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv.1.le _) (sq_nonneg _)),
      ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv.1.le _) (sq_pos_of_pos ha)
    nlinarith [hv.1, hv.2]
  have hf : IntegrableOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (show β - 2 < -1 by linarith) zero_lt_one).mono'
      ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv₀ : 0 < v := lt_trans zero_lt_one hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv₀.le _) (sq_nonneg _)),
      Real.rpow_sub hv₀, Real.rpow_two]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv₀.le _) (sq_pos_of_pos hv₀)
    nlinarith
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (hn.congr_set_ae Ioo_ae_eq_Ioc.symm).union hf

lemma resolvent_kernel_integral_scale (β : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ v in Ioi (0 : ℝ), v ^ β / (a + v) ^ 2) =
      a ^ (β - 1) * ∫ v in Ioi (0 : ℝ), v ^ β / (1 + v) ^ 2 := by
  have hs := integral_comp_mul_left_Ioi (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) 0 ha
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (fun v : ℝ ↦ (a * v) ^ β / (a + a * v) ^ 2) =ᵐ[volume.restrict (Ioi 0)]
      fun v ↦ (a ^ β / a ^ 2) * (v ^ β / (1 + v) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.mul_rpow ha.le hv.le, show a + a * v = a * (1 + v) by ring, mul_pow, mul_div_mul_comm]
  rw [integral_congr_ae he, integral_const_mul] at hs
  have he' : a ^ (β - 1) = a * (a ^ β / a ^ 2) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
    field_simp
  rw [he', mul_assoc, hs, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma resolvent_kernel_integral_pos {β a : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (ha : 0 < a) : 0 < ∫ v in Ioi (0 : ℝ), v ^ β / (a + v) ^ 2 := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun v ↦ v ^ β / (a + v) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact div_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn
    (resolvent_kernel_integrable hβ₀ hβ₁ ha)]
  have he : Function.support (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro v hv
    exact (div_pos (Real.rpow_pos_of_pos hv _) (sq_pos_of_pos (add_pos ha hv))).ne'
  rw [he]
  simp

/-- The scalar difference whose positive-matrix functional calculus is integrated. -/
def resolventDifference (β δ y v : ℝ) : ℝ :=
  v ^ β * ((δ + v)⁻¹ - (y + δ + v)⁻¹)

lemma resolvent_difference_eq (β : ℝ) {δ y v : ℝ}
    (hδv : δ + v ≠ 0) (hyδv : y + δ + v ≠ 0) :
    resolventDifference β δ y v = y * (v ^ β / ((δ + v) * (y + δ + v))) := by
  unfold resolventDifference
  field_simp
  ring

lemma resolvent_difference_integrable {β δ y : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (hδ : 0 < δ) (hy : -δ / 2 < y) :
    IntegrableOn (resolventDifference β δ y) (Ioi 0) := by
  have hc : ContinuousOn (resolventDifference β δ y) (Ioi 0) := by
    unfold resolventDifference
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun _ hv ↦ Or.inl (ne_of_gt hv))
    · apply ContinuousOn.sub
      · apply ContinuousOn.inv₀ (by fun_prop)
        intro v hv
        exact ne_of_gt (add_pos hδ hv)
      · apply ContinuousOn.inv₀ (by fun_prop)
        intro v hv
        have hv' : 0 < v := hv
        linarith
  apply ((resolvent_kernel_integrable hβ₀ hβ₁ (half_pos hδ)).const_mul |y|).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : 0 < v := hv
  have ha : 0 < δ + v := by linarith
  have hb : 0 < y + δ + v := by linarith
  have hm : 0 < δ / 2 + v := by linarith
  rw [resolvent_difference_eq β ha.ne' hb.ne', norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv'.le _) (mul_pos ha hb).le)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv'.le _) (sq_pos_of_pos hm)
  nlinarith [mul_nonneg (show 0 ≤ δ / 2 by linarith) (show 0 ≤ δ / 2 + v by linarith),
    mul_nonneg (show 0 ≤ y + δ / 2 by linarith) (show 0 ≤ δ + v by linarith)]

lemma resolvent_integral_hasDerivAt {β δ y : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (hδ : 0 < δ) (hy : 0 ≤ y) :
    HasDerivAt (fun x ↦ ∫ v in Ioi (0 : ℝ), resolventDifference β δ x v)
      (∫ v in Ioi (0 : ℝ), v ^ β / (y + δ + v) ^ 2) y := by
  have hi x (hx : -δ / 2 < x) := resolvent_difference_integrable hβ₀ hβ₁ hδ hx
  have hmeas : ∀ᶠ x in 𝓝 y, AEStronglyMeasurable (resolventDifference β δ x)
      (volume.restrict (Ioi 0)) := by
    filter_upwards [Ioi_mem_nhds (show -δ / 2 < y by linarith)] with x hx
    exact (hi x hx).aestronglyMeasurable
  have hdint : IntegrableOn (fun v : ℝ ↦ v ^ β / (y + δ + v) ^ 2) (Ioi 0) :=
    resolvent_kernel_integrable hβ₀ hβ₁ (by linarith)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := Ioi (-δ / 2))
    (F' := fun x v : ℝ ↦ v ^ β / (x + δ + v) ^ 2)
    (bound := fun v : ℝ ↦ v ^ β / (δ / 2 + v) ^ 2)
    (Ioi_mem_nhds (show -δ / 2 < y by linarith)) hmeas
    (hi y (by linarith)) hdint.aestronglyMeasurable ?_
    (resolvent_kernel_integrable hβ₀ hβ₁ (half_pos hδ)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro x hx
    have hv' : 0 < v := hv
    have hx' : -δ / 2 < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv'.le _) (sq_nonneg _))]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv'.le _)
      (sq_pos_of_pos (by linarith : 0 < δ / 2 + v))
    nlinarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro x hx
    have hv' : 0 < v := hv
    have hx' : -δ / 2 < x := hx
    have he := (((hasDerivAt_id x).add_const δ).add_const v).inv
      (by linarith : x + δ + v ≠ 0)
    convert! (he.const_sub ((δ + v)⁻¹)).const_mul (v ^ β) using 1
    simp [div_eq_mul_inv]


/-- The normalization constant for the resolvent representation. -/
def resolventNormalization (β : ℝ) : ℝ :=
  (∫ v in Ioi (0 : ℝ), v ^ β / (1 + v) ^ 2)⁻¹

lemma resolvent_normalization_pos {β : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1) :
    0 < resolventNormalization β :=
  inv_pos.2 (resolvent_kernel_integral_pos hβ₀ hβ₁ zero_lt_one)

/-- Resolvent representation of f, for every nonnegative scalar argument.
The exponent sigma-1/2 may be zero or negative. -/
lemma primitive_resolvent_representation {σ δ y : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hy : 0 ≤ y) :
    regularizedPrimitive σ δ y = resolventNormalization (σ - 1 / 2) *
      ∫ v in Ioi (0 : ℝ), resolventDifference (σ - 1 / 2) δ y v := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  have hJ := (resolvent_kernel_integral_pos hβ₀ hβ₁ zero_lt_one).ne'
  have hd (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun t ↦ resolventNormalization (σ - 1 / 2) *
        ∫ v in Ioi (0 : ℝ), resolventDifference (σ - 1 / 2) δ t v)
        ((x + δ) ^ (σ - 3 / 2)) x := by
    have hh := (resolvent_integral_hasDerivAt hβ₀ hβ₁ hδ hx).const_mul
      (resolventNormalization (σ - 1 / 2))
    rw [resolvent_kernel_integral_scale _ (by positivity : 0 < x + δ)] at hh
    convert! hh using 1
    unfold resolventNormalization
    rw [show σ - 1 / 2 - 1 = σ - 3 / 2 by ring,
      mul_comm ((x + δ) ^ (σ - 3 / 2)), ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]
  have hf (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (regularizedPrimitive σ δ) ((x + δ) ^ (σ - 3 / 2)) x := by
    simpa only [max_eq_left hx] using primitive_hasDerivAt σ hδ x
  exact eq_of_has_deriv_right_eq
    (fun x hx ↦ (hf x hx.1).hasDerivWithinAt)
    (fun x hx ↦ (hd x hx.1).hasDerivWithinAt)
    (primitive_differentiable σ hδ).continuous.continuousOn
    (fun x hx ↦ (hd x hx.1).continuousAt.continuousWithinAt)
    (by simp [resolventDifference]) y ⟨hy, le_rfl⟩

lemma inverse_mu_positive {σ δ m : ℝ} (hσ₀ : 0 < σ) (hδ : 0 < δ) (hm : 0 < m) :
    0 < (m + δ ^ σ) ^ (1 / σ) - δ := by
  have hbase : 0 < δ ^ σ := Real.rpow_pos_of_pos hδ _
  have hi : 0 < (1 : ℝ) / σ := one_div_pos.2 hσ₀
  have hc := Real.rpow_lt_rpow hbase.le (show δ ^ σ < m + δ ^ σ by linarith) hi
  rw [← Real.rpow_mul hδ.le, mul_one_div_cancel hσ₀.ne', Real.rpow_one] at hc
  linarith

lemma mu_inverse {σ δ m : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hm : 0 < m) :
    scalarMu σ δ ((m + δ ^ σ) ^ (1 / σ) - δ) = m := by
  rw [mu_eq_nonneg hσ₁ hδ (inverse_mu_positive hσ₀ hδ hm).le, sub_add_cancel,
    ← Real.rpow_mul (by positivity : 0 ≤ m + δ ^ σ),
    one_div_mul_cancel hσ₀.ne', Real.rpow_one]
  ring

lemma mu_le_rpow {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) : scalarMu σ δ d ≤ d ^ σ := by
  rw [mu_eq_nonneg hσ₁ hδ hd]
  have := Real.rpow_add_le_add_rpow hd hδ.le hσ₀.le hσ₁.le
  linarith

lemma rankone_scalar_power {σ δ m d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hm : 0 < m) (hd : 0 ≤ d) (he : scalarMu σ δ d = m) :
    m ^ (1 + 1 / σ) ≤ d * m := by
  have hmd : m ≤ d ^ σ := by rw [← he]; exact mu_le_rpow hσ₀ hσ₁ hδ hd
  have hp := Real.rpow_le_rpow hm.le hmd (le_of_lt (one_div_pos.2 hσ₀))
  rw [← Real.rpow_mul hd, mul_one_div_cancel hσ₀.ne', Real.rpow_one] at hp
  rw [Real.rpow_add hm, Real.rpow_one, mul_comm d]
  exact mul_le_mul_of_nonneg_left hp hm.le

end ScalarProof

open scoped MatrixOrder ComplexOrder
namespace MatrixProof
variable {n : Type u4} [Fintype n] [DecidableEq n]

/-- Exact resolvent remainder. All inverses are the ordinary finite-matrix
inverse; invertibility is provided by the positive-definiteness hypotheses. -/
lemma resolvent_remainder (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    -A⁻¹ + A⁻¹ * (B - A) * A⁻¹ - (-B⁻¹) =
      (A⁻¹ * (B - A)) * B⁻¹ * ((B - A) * A⁻¹) := by
  have hAA := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hAA' := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBB := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hBB' := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hb (C : Matrix n n ℂ) : B⁻¹ * (B * C) = C := by
    rw [← mul_assoc, hBB', one_mul]
  simp only [mul_sub, sub_mul, hAA, hAA', mul_one, one_mul]
  simp only [mul_assoc, hb, hBB, mul_one]
  noncomm_ring

/-- The resolvent tangent inequality before integration. -/
lemma resolvent_tangent {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    -B⁻¹ ≤ -A⁻¹ + A⁻¹ * (B - A) * A⁻¹ := by
  rw [← sub_nonneg, resolvent_remainder A B hA.isUnit hB.isUnit]
  have hp := hB.inv.posSemidef.conjTranspose_mul_mul_same ((B - A) * A⁻¹)
  have he : (((B - A) * A⁻¹)ᴴ) = A⁻¹ * (B - A) := by
    rw [conjTranspose_mul, hA.inv.isHermitian.eq, (hB.isHermitian.sub hA.isHermitian).eq]
  rw [he] at hp
  exact hp.nonneg


end MatrixProof

/-- The compact penalty lemma. No differentiability or
convergence of the selected paths is required. -/
lemma compact_penalty {X : Type u5} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg₀ : ∀ x ∈ K, 0 ≤ g x) (hzero : ∀ x ∈ K, g x = 0 → f x ≤ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ x ∈ K, f x - g x / t ≤ η := by
  let S := K ∩ {x | η ≤ f x}
  have hS : IsCompact S := hK.inter_right (isClosed_le continuous_const hf)
  by_cases hne : S.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨y, hy.1⟩ hf.continuousOn
    have hgy : 0 < g y := by
      apply lt_of_le_of_ne (hg₀ y hy.1)
      intro h
      have := hzero y hy.1 h.symm
      exact (not_le_of_gt hη) (le_trans hy.2 this)
    refine ⟨g y / (max (f z) 0 + 1), div_pos hgy (by positivity), ?_⟩
    intro t ht htt x hx
    by_cases hfx : η ≤ f x
    · have hxS : x ∈ S := ⟨hx, hfx⟩
      have hxg : g y ≤ g x := hmin hxS
      have hxf : f x ≤ f z := hmax hx
      have hc : 0 < max (f z) 0 + 1 := by positivity
      have htm : t * (max (f z) 0 + 1) ≤ g y := (le_div_iff₀ hc).1 htt
      have hgquot : max (f z) 0 + 1 ≤ g x / t :=
        (le_div_iff₀ ht).2 (by nlinarith)
      have := le_max_left (f z) 0
      linarith
    · have := div_nonneg (hg₀ x hx) ht.le
      linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht _ x hx
    have hfx : f x < η := by
      by_contra hn
      apply hne
      exact ⟨x, hx, le_of_not_gt hn⟩
    have := div_nonneg (hg₀ x hx) ht.le
    linarith


end SharpLiebThirring

end

end OAI
