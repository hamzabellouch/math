import OAI.NumberTheory.Ostmann.QuadraticSieveMellin

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

noncomputable def mellinScale (σ r x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(σ + r * Complex.I))

theorem mellinScale_continuous (σ x : ℝ) (hx : 0 < x) :
    Continuous (fun r => mellinScale σ r x) := by
  exact (show Continuous (fun r : ℝ => -((σ : ℂ) + r * Complex.I)) by fun_prop).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

theorem norm_mellinScale (σ r x : ℝ) (hx : 0 < x) :
    ‖mellinScale σ r x‖ = x ^ (-σ) := by
  rw [mellinScale, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem mellinScale_mul (σ r x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    mellinScale σ r (x * y) = mellinScale σ r x * mellinScale σ r y := by
  exact_mod_cast Complex.mul_cpow_ofReal_nonneg hx.le hy.le (-((σ : ℂ) + r * Complex.I))

theorem mellinScale_mul_mellin_integrable (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun r : ℝ => mellinScale σ r x * mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)) := by
  exact (Ostmann.schwartz_mellin_vertical_integrable ρ σ hσ).bdd_mul
    (mellinScale_continuous σ x hx).aestronglyMeasurable
    (ae_of_all _ (fun r => (norm_mellinScale σ r x hx).le))

theorem finite_mellin_inversion {ι : Type*} (S : Finset ι) (ρ : 𝓢(ℝ, ℂ))
    (σ : ℝ) (hσ : 0 < σ) (K : ι → ℂ) (x : ι → ℝ) (hx : ∀ i ∈ S, 0 < x i) :
    (∑ i ∈ S, K i * ρ (x i)) = (1 / (2 * Real.pi) : ℝ) •
      (∫ r : ℝ, ∑ i ∈ S, K i *
        (mellinScale σ r (x i) * mellin (ρ : ℝ → ℂ) (σ + r * Complex.I))) := by
  rw [integral_finsetSum S (fun i hi =>
    (mellinScale_mul_mellin_integrable ρ σ hσ (x i) (hx i hi)).const_mul (K i))]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, ← mul_smul_comm]
  rw [show (fun r : ℝ => mellinScale σ r (x i) * mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)) =
    (fun r : ℝ => (x i : ℂ) ^ (-(σ + r * Complex.I)) *
      mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)) from rfl,
    Ostmann.schwartz_mellin_inversion_integral ρ σ hσ (hx i hi)]

end Ostmann.QuadraticSieve

end OAI
