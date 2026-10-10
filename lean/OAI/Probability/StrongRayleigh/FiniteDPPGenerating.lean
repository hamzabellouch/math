import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem det_one_add_eq_sum_principal_minors {F : Type u_1} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) :
    Matrix.det (1 + K) = ∑ A : Finset F,
      Matrix.det (fun i j : A => K i.1 j.1) := by
  let D := (Matrix.detRowAlternating : (F → ℂ) [⋀^F]→ₗ[ℂ] ℂ)
  rw [add_comm]
  change D ((fun i => K i) + (fun i => (1 : Matrix F F ℂ) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro A hA
  exact Matrix.det_piecewise_one_eq_submatrix_det K A

theorem det_one_add_weighted_eq_sum_principal_minors {F : Type u_2} [Fintype F] [DecidableEq F]
    (K : Matrix F F ℂ) (w : F → ℂ) :
    Matrix.det ((1 : Matrix F F ℂ) + Matrix.of (fun i j => w i * K i j)) = ∑ A : Finset F,
      (∏ i ∈ A, w i) * Matrix.det (fun i j : A => K i.1 j.1) := by
  rw [det_one_add_eq_sum_principal_minors]
  apply Finset.sum_congr rfl
  intro A hA
  change Matrix.det (Matrix.of (fun i j : A => w i.1 * K i.1 j.1)) = _
  simpa only [Finset.prod_coe_sort] using
    Matrix.det_mul_column (fun i : A => w i.1) (fun i j : A => K i.1 j.1)

theorem binary_monomial_expansion {F : Type u_3} [Fintype F] [DecidableEq F]
    (x : F → Bool) (z : F → ℂ) :
    (∏ i : F, if x i = true then z i else 1) =
      ∑ A : Finset F, if ∀ i ∈ A, x i = true then ∏ i ∈ A, (z i - 1) else 0 := by
  calc
    _ = ∏ i : F, ((if x i = true then z i - 1 else 0) + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp
    _ = ∑ A : Finset F, ∏ i ∈ A, (if x i = true then z i - 1 else 0) := by
      simpa using Fintype.prod_add (fun i => if x i = true then z i - 1 else 0)
        (fun _ => (1 : ℂ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases hx : ∀ i ∈ A, x i = true
      · simp only [ite_eq_left hx]
        apply Finset.prod_congr rfl
        intro i hi
        exact ite_eq_left (hx i hi)
      · rw [ite_eq_right hx]
        push Not at hx
        obtain ⟨i, hi, hxi⟩ := hx
        exact Finset.prod_eq_zero hi (ite_eq_right hxi)

theorem sum_atom_mass_on {F : Type u_4} [Fintype F] [DecidableEq F]
    (μ : ProbabilityMeasure (F → Bool)) (P : (F → Bool) → Prop) [DecidablePred P] :
    (∑ x : F → Bool, if P x then ((μ : Measure (F → Bool)) {x}).toReal else 0) =
      ((μ : Measure (F → Bool)) {x | P x}).toReal := by
  simpa [Measure.real, Finset.sum_filter] using
    (sum_measureReal_singleton (μ := (μ : Measure (F → Bool)))
      (Finset.univ.filter P))

theorem finiteGeneratingValue_eq_inclusion_sum {F : Type u_5} [Fintype F] [DecidableEq F]
    (μ : ProbabilityMeasure (F → Bool)) (z : F → ℂ) :
    finiteGeneratingValue μ z = ∑ A : Finset F,
      (((μ : Measure (F → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) *
        ∏ i ∈ A, (z i - 1) := by
  unfold finiteGeneratingValue
  simp_rw [binary_monomial_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  calc
    _ = (∑ x : F → Bool, if ∀ i ∈ A, x i = true then
          (((μ : Measure (F → Bool)) {x}).toReal : ℂ) else 0) *
            ∏ i ∈ A, (z i - 1) := by
      rw [Finset.sum_mul]
      simp only [mul_ite, mul_zero, ite_mul, zero_mul]
      congr!
    _ = _ := by
      congr 1
      simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using congrArg (fun r : ℝ => (r : ℂ))
        (sum_atom_mass_on μ (fun x => ∀ i ∈ A, x i = true))

theorem finiteGeneratingValue_eq_det {F : Type u_6} [Fintype F] [DecidableEq F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ)
    (hμ : IsFiniteDeterminantalLaw μ K) (z : F → ℂ) :
    finiteGeneratingValue μ z =
      Matrix.det ((1 : Matrix F F ℂ) + Matrix.of (fun i j => (z i - 1) * K i j)) := by
  rw [finiteGeneratingValue_eq_inclusion_sum]
  refine Eq.trans ?_
    (det_one_add_weighted_eq_sum_principal_minors (Matrix.of K) (fun i => z i - 1)).symm
  apply Finset.sum_congr rfl
  intro A hA
  rw [hμ A, mul_comm]
  congr

end Problem336AdditiveD139

end

end OAI
