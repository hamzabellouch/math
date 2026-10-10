import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.TemplateWeightedHilbert
open Construction
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def vector (μ : FinitePrior Ω) (f : Ω → R → ℂ) : EuclideanSpace ℂ (Ω × R) :=
  WithLp.toLp 2 (fun x => (Real.sqrt (μ.mass x.1) : ℂ) * f x.1 x.2)

omit [Fintype R] in
@[simp] theorem vector_apply [Fintype R] (μ : FinitePrior Ω) (f : Ω → R → ℂ) (ω : Ω) (r : R) :
    vector μ f (ω, r) = (Real.sqrt (μ.mass ω) : ℂ) * f ω r := rfl

def reference (μ : FinitePrior Ω) : EuclideanSpace ℂ (Ω × R) :=
  vector μ (fun _ _ => 1)

omit [Fintype R] in
@[simp] theorem reference_apply [Fintype R] (μ : FinitePrior Ω) (ω : Ω) (r : R) :
    reference μ (ω, r) = (Real.sqrt (μ.mass ω) : ℂ) := by
  simp [reference]

theorem vector_norm_sq (μ : FinitePrior Ω) (f : Ω → R → ℂ) :
    ‖vector μ f‖ ^ 2 = μ.mean (fun ω => ∑ r, ‖f ω r‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [vector_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (μ.mass_nonneg _), FinitePrior.mean, Finset.mul_sum]

theorem vector_inner (μ : FinitePrior Ω) (f g : Ω → R → ℂ) :
    inner ℂ (vector μ f) (vector μ g) =
      μ.cmean (fun ω => ∑ r, conj (f ω r) * g ω r) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [FinitePrior.cmean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro r hr
  simp only [RCLike.inner_apply, vector_apply, map_mul, Complex.conj_ofReal]
  have hs : (Real.sqrt (μ.mass ω) : ℂ) ^ 2 = (μ.mass ω : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (μ.mass_nonneg ω)]
  calc
    _ = (Real.sqrt (μ.mass ω) : ℂ) ^ 2 * (conj (f ω r) * g ω r) := by ring
    _ = _ := by rw [hs]

theorem reference_inner (μ : FinitePrior Ω) (f : Ω → R → ℂ) :
    inner ℂ (reference μ) (vector μ f) = μ.cmean (fun ω => ∑ r, f ω r) := by
  simp [reference, vector_inner]

theorem reference_norm_sq (μ : FinitePrior Ω) :
    ‖(reference μ : EuclideanSpace ℂ (Ω × R))‖ ^ 2 = (Fintype.card R : ℝ) := by
  simp [reference, vector_norm_sq, FinitePrior.mean_const]

theorem vector_norm_sq_le (μ : FinitePrior Ω) (f : Ω → R → ℂ) (B : Ω → ℝ)
    (hB : ∀ ω, ∑ r, ‖f ω r‖ ^ 2 ≤ B ω) :
    ‖vector μ f‖ ^ 2 ≤ μ.mean B := by
  rw [vector_norm_sq]
  exact μ.mean_mono hB

end Ostmann.Characters.TemplateWeightedHilbert

end

end OAI
