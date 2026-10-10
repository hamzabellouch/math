import OAI.NumberTheory.Ostmann.Arithmetic.RootMeshIntegral

namespace OAI

/-! # Joint transport of the two original giant coordinates -/

namespace Ostmann
open scoped BigOperators
open MeasureTheory

/-- Slice comparisons combine against the original outer prior and the
ideal inner measure. This introduces neither conditional sampling nor a
count of real partition boxes. -/
theorem two_giant_integral_transport {A B X Y : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace X] [MeasurableSpace Y]
    (α : A → ℝ) (β : B → ℝ) (x : A → X) (y : B → Y)
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) (H : X → Y → ℂ)
    (hβ : ∀ b, 0 ≤ β b) (δ ε : ℝ)
    (hH : ∀ b, Integrable (fun z => H z (y b)) μ)
    (hI : Integrable (fun z => ∫ t, H z t ∂ν) μ)
    (hleft : ∀ b, ‖(∑ a, (α a : ℂ) * H (x a) (y b)) - ∫ z, H z (y b) ∂μ‖ ≤ δ)
    (hright : ∀ᵐ z ∂μ, ‖(∑ b, (β b : ℂ) * H z (y b)) - ∫ t, H z t ∂ν‖ ≤ ε) :
    ‖(∑ b, (β b : ℂ) * ∑ a, (α a : ℂ) * H (x a) (y b)) -
      ∫ z, ∫ t, H z t ∂ν ∂μ‖ ≤ δ * (∑ b, β b) + ε * μ.real Set.univ := by
  let Z := ∑ b, (β b : ℂ) * ∫ z, H z (y b) ∂μ
  have h1 : ‖(∑ b, (β b : ℂ) * ∑ a, (α a : ℂ) * H (x a) (y b)) - Z‖ ≤
      δ * (∑ b, β b) := by
    dsimp only [Z]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ b, ‖(β b : ℂ) * ((∑ a, (α a : ℂ) * H (x a) (y b)) -
          ∫ z, H z (y b) ∂μ)‖ := norm_sum_le _ _
      _ ≤ ∑ b, β b * δ := by
        apply Finset.sum_le_sum
        intro b _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ b)]
        exact mul_le_mul_of_nonneg_left (hleft b) (hβ b)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hint : Integrable (fun z => ∑ b, (β b : ℂ) * H z (y b)) μ :=
    integrable_finsetSum _ (fun b _ => (hH b).const_mul _)
  have hZ : Z = ∫ z, ∑ b, (β b : ℂ) * H z (y b) ∂μ := by
    rw [integral_finsetSum _ (fun b _ => (hH b).const_mul _)]
    simp only [integral_const_mul, Z]
  have h2 : ‖Z - ∫ z, ∫ t, H z t ∂ν ∂μ‖ ≤ ε * μ.real Set.univ := by
    rw [hZ, ← integral_sub hint hI]
    exact norm_integral_le_of_norm_le_const hright
  exact (norm_sub_le_norm_sub_add_norm_sub _ Z _).trans (add_le_add h1 h2)

end Ostmann

end OAI
