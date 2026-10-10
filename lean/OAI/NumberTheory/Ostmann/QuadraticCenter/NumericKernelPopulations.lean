import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericKernelPopulationsFinite
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericKernelPopulationsGrowth

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_numericKernel_populations (c η : ℝ)
    (hc : 0 < c) (hη : 0 < η) (hηu : η ≤ 1/10) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℤ) (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ X^(η/10) → IsCoprime h (m : ℤ) →
      (∀ x ∈ S, (m : ℤ)*x-h ≠ 0) →
      (∀ x ∈ S, ∀ y ∈ S, |(x : ℝ)-(y : ℝ)| ≤ X) →
      c*Real.sqrt X/(Real.log X)^3 ≤ S.card →
      ((canonicalKernelImage S m h).card : ℝ) ≤ X^(η/10) →
      ∃ u ∈ canonicalKernelImage S m h,
        0 < |(u : ℝ)| ∧ |(u : ℝ)| ≤ X^η ∧ Squarefree u ∧
        (canonicalKernelRoots S m h u).Nonempty ∧
        X^(1/2-3*η) ≤ (canonicalKernelRoots S m h u).card ∧
        ∀ r ∈ canonicalKernelRoots S m h u, ∀ s ∈ canonicalKernelRoots S m h u,
          |(r : ℝ)-(s : ℝ)| ≤ X^(1/2+η) := by
  filter_upwards [eventually_numericKernel_population_budget c η hc hη hηu]
    with X hb
  intro S m h hm hmX hcop hnz hdiam hmass hK
  have hXp : 0 < X := by linarith [hb.1]
  have hsmall : ((canonicalKernelImage S m h).card : ℝ)*
      (4*Real.sqrt (X/X^η)+8*Real.sqrt (m : ℝ))+
      X^(η/10)*X^(1/2-3*η) ≤ S.card := by
    apply le_trans _ (hb.2.2.trans hmass)
    apply add_le_add _ le_rfl
    apply mul_le_mul hK _ (by positivity) (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmX) (by norm_num))
  have hpositive : 0 < X^(η/10)*X^(1/2-3*η) := by positivity
  have hsurvive : ((canonicalKernelImage S m h).card : ℝ)*
      (4*Real.sqrt (X/X^η)+8*Real.sqrt (m : ℝ)) < S.card := by linarith
  obtain ⟨u,hu,hup,hub,husf,hr,hcount⟩ := exists_large_small_canonicalKernelRoots
    hm hcop hnz hXp.le (Real.rpow_pos_of_pos hXp η) hdiam hsurvive
  have hroot : X^(1/2-3*η) ≤ (canonicalKernelRoots S m h u).card := by
    have hKroot := mul_le_mul_of_nonneg_right hK
      (Nat.cast_nonneg (canonicalKernelRoots S m h u).card : (0 : ℝ) ≤ _)
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hXp (η/10))).mp
    linarith
  refine ⟨u,hu,hup,hub.le,husf,hr,hroot,?_⟩
  have huz : u ≠ 0 := by
    intro he
    simp only [he, Int.cast_zero, abs_zero] at hup
    linarith
  have hmη : (m : ℝ) ≤ X^η := hmX.trans
    (Real.rpow_le_rpow_of_exponent_le hb.1 (by linarith : η/10 ≤ η))
  exact canonicalKernelRoots_diameter_scale huz hb.1 hη.le hmη hdiam

end Ostmann.QuadraticCenter

end

end OAI
