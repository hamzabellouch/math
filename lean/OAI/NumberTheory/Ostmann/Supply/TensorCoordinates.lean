import OAI.NumberTheory.Ostmann.Supply.CenteredProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)]

def tensorVector (v : ∀ i, EuclideanSpace ℂ (β i)) :
    EuclideanSpace ℂ (∀ i, β i) :=
  WithLp.toLp 2 (fun x => ∏ i, v i (x i))

omit [DecidableEq ι] [∀ i, Fintype (β i)] in
@[simp] theorem tensorVector_apply (v : ∀ i, EuclideanSpace ℂ (β i)) (x : ∀ i, β i) :
    tensorVector v x = ∏ i, v i (x i) := rfl

theorem tensorVector_inner (v w : ∀ i, EuclideanSpace ℂ (β i)) :
    inner ℂ (tensorVector v) (tensorVector w) = ∏ i, inner ℂ (v i) (w i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, tensorVector_apply, map_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => w i j * conj (v i j))).symm

variable {α : Type*}

def meanTensor (A : Finset α) (v : α → ∀ i, EuclideanSpace ℂ (β i)) :
    EuclideanSpace ℂ (∀ i, β i) :=
  (A.card : ℂ)⁻¹ • ∑ a ∈ A, tensorVector (v a)

def tensorEnergy (A : Finset α) (v : α → ∀ i, EuclideanSpace ℂ (β i)) : ℝ :=
  ‖meanTensor A v‖^2

theorem tensorEnergy_nonneg (A : Finset α) (v : α → ∀ i, EuclideanSpace ℂ (β i)) :
    0 ≤ tensorEnergy A v := sq_nonneg _

theorem tensorGram_sum (A : Finset α) (v : α → ∀ i, EuclideanSpace ℂ (β i)) :
    (∑ a ∈ A, ∑ b ∈ A, ∏ i, inner ℂ (v a i) (v b i)) =
      (‖∑ a ∈ A, tensorVector (v a)‖^2 : ℝ) := by
  simp_rw [← tensorVector_inner]
  simp_rw [← inner_sum]
  rw [← sum_inner]
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2]
  simp only [RCLike.inner_apply, Complex.mul_conj', Complex.ofReal_sum, Complex.ofReal_pow]

theorem tensorGram_nonneg (A : Finset α) (v : α → ∀ i, EuclideanSpace ℂ (β i)) :
    0 ≤ (∑ a ∈ A, ∑ b ∈ A, ∏ i, inner ℂ (v a i) (v b i)).re := by
  rw [tensorGram_sum]
  exact sq_nonneg _

theorem tensorEnergy_eq_gram (A : Finset α)
    (v : α → ∀ i, EuclideanSpace ℂ (β i)) :
    (tensorEnergy A v : ℂ) =
      (A.card : ℂ)⁻¹^2 * ∑ a ∈ A, ∑ b ∈ A, ∏ i, inner ℂ (v a i) (v b i) := by
  rw [tensorGram_sum]
  simp only [tensorEnergy, meanTensor, norm_smul, mul_pow, norm_inv,
    Complex.norm_natCast, inv_pow, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_natCast]

end Ostmann.Supply

end

end OAI
