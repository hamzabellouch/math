import OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    exponentVector a i = a i := by
  simp [exponentVector]

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

@[simp] theorem truncatedLog_coeff (T k : ℕ) :
    (truncatedLog T).coeff k =
      if k < T then
        if k = 0 then 0 else algebraMap ℚ ℂ ((-1 : ℚ) ^ (k + 1) / k)
      else 0 := by
  simp [truncatedLog, PowerSeries.coeff_trunc]

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

noncomputable def sectionImage {m : ℕ} {C : Type*} [Fintype C]
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : C → ℕ) (a : C → Fin m → ℕ) (x : C → ℂ) (j : ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  ∑ c, MvPolynomial.C (Polynomial.C (x c)) * monomialImage r G j (h c) (a c)

theorem sectionImage_coeff {m : ℕ} {C : Type*} [Fintype C]
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : C → ℕ) (a : C → Fin m → ℕ) (x : C → ℂ)
    (j s : ℕ) (b : Fin m → ℕ) :
    ((sectionImage r G h a x j).coeff (exponentVector b)).coeff s =
      ∑ c, entry r G j s b (h c) (a c) * x c := by
  classical
  simp only [sectionImage, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, entry]
  apply Finset.sum_congr rfl
  intro c hc
  exact mul_comm _ _

def columnWeights {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases w0 w

noncomputable def rowWeights {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases v0 (fun i => w i / θ)

abbrev Column {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  ↥(PiExponent.realWeightedSimplex (columnWeights w0 w) H)

abbrev Row {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  Fin K × ↥(PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H)

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by
  have hp : ∀ i, 0 < columnWeights w0 w i := by
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

theorem column_weight_le {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (c : Column w0 w H) :
    w0 * (c.1 0 : ℝ) + ∑ i, w i * (c.1 i.succ : ℝ) ≤ H :=
  (column_mem_iff hw0 hw c.1).mp c.2

theorem row_weight_lt {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (ρ : Row K v0 θ w H) :
    v0 * (ρ.2.1 0 : ℝ) + (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ < H :=
  (row_mem_iff hv0 hθ hw ρ.2.1).mp ρ.2.2

noncomputable def matrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  fun ρ c => entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
    (c.1 0) (fun i => c.1 i.succ)

noncomputable def linearEvaluation {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    (Column w0 w H → ℂ) →ₗ[ℂ] (Row K v0 θ w H → ℂ) :=
  (matrix K w0 v0 θ w H r G).mulVecLin

theorem linearEvaluation_apply {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : Column w0 w H → ℂ) (ρ : Row K v0 θ w H) :
    linearEvaluation K w0 v0 θ w H r G x ρ =
      ∑ c, entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
        (c.1 0) (fun i => c.1 i.succ) * x c := rfl

theorem linearEvaluation_eq_coeff {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : Column w0 w H → ℂ) (ρ : Row K v0 θ w H) :
    linearEvaluation K w0 v0 θ w H r G x ρ =
      ((sectionImage r G (fun c : Column w0 w H => c.1 0)
        (fun c i => c.1 i.succ) x ρ.1.val).coeff
          (exponentVector (fun i => ρ.2.1 i.succ))).coeff (ρ.2.1 0) := by
  rw [linearEvaluation_apply, sectionImage_coeff]

@[simp] theorem row_card {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) :
    Fintype.card (Row K v0 θ w H) =
      K * (PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H).card := by
  classical
  simp [Row]

theorem exists_full_row_minor_of_surjective
    {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]
    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, Function.Injective selection ∧
      (A.submatrix id selection).det ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hexp : (A * B).det =
      ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
    calc
      (A * B).det = ∑ p : R → C, ∑ σ : Equiv.Perm R,
          ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, A (σ i) (p i) * B (p i) i := by
        simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
          Finset.mul_sum, Fintype.piFinset_univ]
        rw [Finset.sum_comm]
      _ = ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
          Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul]
  have hsum : (∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i) ≠ 0 := by
    rw [← hexp, hB, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdet : (A.submatrix id p).det ≠ 0 := by
    intro h
    apply hp
    rw [h, zero_mul]
  refine ⟨p, ?_, hdet⟩
  intro i j hij
  by_contra hne
  exact hdet (Matrix.det_zero_of_column_eq hne (fun k => congrArg (A k) hij))

theorem interpolation_full_row_minor {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (hsurj : Function.Surjective (linearEvaluation K w0 v0 θ w H r G)) :
    ∃ selection : Row K v0 θ w H → Column w0 w H,
      Function.Injective selection ∧
        ((matrix K w0 v0 θ w H r G).submatrix id selection).det ≠ 0 := by
  classical
  exact exists_full_row_minor_of_surjective (matrix K w0 v0 θ w H r G) hsurj

noncomputable def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  matrix K w0 v0 θ w H r (fun i => truncatedLog (T i))

theorem truncatedLog_full_row_minor {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hsurj : Function.Surjective
      (linearEvaluation K w0 v0 θ w H r (fun i => truncatedLog (T i)))) :
    ∃ selection : Row K v0 θ w H → Column w0 w H,
      Function.Injective selection ∧
        ((truncatedLogMatrix K w0 v0 θ w H r T).submatrix id selection).det ≠ 0 := by
  exact interpolation_full_row_minor K w0 v0 θ w H r _ hsurj

end PiExponent.InterpolationMatrix

end OAI
