import OAI.NumberTheory.JointDickman.Counting.BilinearEnergy
import OAI.NumberTheory.JointDickman.Amplification.FiniteAdditiveOrthogonality

namespace OAI

/-! # Triangular smoothing of finite bilinear sums -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

/-- Every point of an interval occurs at least Y times in the convolution
of the two intervals of length 2Y. -/
lemma interval_energy_le_convolution (F : ℤ → ℂ) (a : ℤ) (Y : ℕ) :
    (Y : ℝ) * (∑ n ∈ Ico a (a+Y), ‖F n‖^2) ≤
      ∑ u ∈ Ico (0:ℤ) (2*Y), ∑ v ∈ Ico (0:ℤ) (2*Y),
        ‖F (a-Y+u+v)‖^2 := by
  have hrow (u : ℤ) (hu : u ∈ Ico (0:ℤ) Y) :
      (∑ n ∈ Ico a (a+Y), ‖F n‖^2) ≤
        ∑ v ∈ Ico (0:ℤ) (2*Y), ‖F (a-Y+u+v)‖^2 := by
    have hshift := sum_Ico_add (fun n : ℤ => ‖F n‖^2) 0 (2*Y) (a-Y+u)
    rw [hshift]
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ico] at hu hn ⊢
      omega
    · intro n _ _
      exact sq_nonneg _
  calc
    _ = ∑ _u ∈ Ico (0:ℤ) Y, ∑ n ∈ Ico a (a+Y), ‖F n‖^2 := by simp
    _ ≤ ∑ u ∈ Ico (0:ℤ) Y, ∑ v ∈ Ico (0:ℤ) (2*Y),
        ‖F (a-Y+u+v)‖^2 := sum_le_sum hrow
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro u hu
        simp only [mem_Ico] at hu ⊢
        omega
      · intro u _ _
        exact sum_nonneg (fun v _ => sq_nonneg _)

lemma additivePhase_mul_conj (x y : ℝ) :
    additivePhase x * conj (additivePhase y) = additivePhase (x-y) := by
  rw [additivePhase_conj, ←additivePhase_add, sub_eq_add_neg]

/-- The smoothed correlation is a squared geometric sum. -/
lemma convolution_phase_norm (s : Finset ℤ) (a : ℤ) (t : ℝ) :
    ‖∑ u ∈ s, ∑ v ∈ s, additivePhase (t*(a+u+v))‖ =
      ‖∑ u ∈ s, additivePhase (t*u)‖^2 := by
  have he : (∑ u ∈ s, ∑ v ∈ s, additivePhase (t*(a+u+v))) =
      additivePhase (t*a) * (∑ u ∈ s, additivePhase (t*u))^2 := by
    simp only [pow_two, mul_sum, sum_mul]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    rw [←additivePhase_add, ←additivePhase_add]
    congr 1
    ring
  rw [he,norm_mul,norm_pow]
  have hn : ‖additivePhase (t*a)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [hn,one_mul]

/-- Squared interval energy is controlled by the smoothed prime correlations. -/
theorem smoothed_bilinear_energy (P : Finset ℕ) (b : ℕ → ℂ)
    (θ : ℝ) (a : ℤ) (Y : ℕ) :
    (Y : ℝ) * (∑ n ∈ Ico a (a+Y),
      ‖∑ p ∈ P, b p * additivePhase (θ*p*n)‖^2) ≤
      ∑ p ∈ P, ∑ r ∈ P, ‖b p‖*‖b r‖*
        ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2 := by
  let s := Ico (0:ℤ) (2*Y)
  have henergy := BilinearEnergy.energy_le_correlations (s ×ˢ s) P b
    (fun uv p => additivePhase (θ*p*(a-Y+uv.1+uv.2)))
  simp only [sum_product] at henergy
  have hinterval := interval_energy_le_convolution
    (fun n => ∑ p ∈ P, b p * additivePhase (θ*p*n)) a Y
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast] at hinterval
  refine hinterval.trans (henergy.trans_eq ?_)
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro r hr
  congr 1
  have he : (∑ u ∈ s, ∑ v ∈ s,
      additivePhase (θ*p*(a-Y+u+v)) *
        (starRingEnd ℂ) (additivePhase (θ*r*(a-Y+u+v)))) =
      ∑ u ∈ s, ∑ v ∈ s, additivePhase ((θ*((p:ℝ)-r))*((a-Y)+u+v)) := by
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    rw [show (starRingEnd ℂ) = conj by rfl,additivePhase_mul_conj]
    congr 1
    ring
  rw [he]
  simpa only [Int.cast_sub,Int.cast_natCast] using
    convolution_phase_norm s (a-Y) (θ*((p:ℝ)-r))

/-- Cauchy--Schwarz and triangular smoothing for a bounded integer coefficient. -/
theorem smoothed_bilinear_bound (P : Finset ℕ) (b : ℕ → ℂ)
    (c : ℤ → ℂ) (θ : ℝ) (a : ℤ) (Y : ℕ)
    (hc : ∀ n ∈ Ico a (a+Y), ‖c n‖ ≤ 1) :
    ‖∑ n ∈ Ico a (a+Y), c n *
      ∑ p ∈ P, b p * additivePhase (θ*p*n)‖^2 ≤
      ∑ p ∈ P, ∑ r ∈ P, ‖b p‖*‖b r‖*
        ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2 := by
  let F := fun n : ℤ => ∑ p ∈ P, b p * additivePhase (θ*p*n)
  have hnorm : ‖∑ n ∈ Ico a (a+Y), c n * F n‖ ≤
      ∑ n ∈ Ico a (a+Y), ‖F n‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc n hn) (norm_nonneg (F n))
  have hCS : (∑ n ∈ Ico a (a+Y), ‖F n‖)^2 ≤
      (Y:ℝ) * ∑ n ∈ Ico a (a+Y), ‖F n‖^2 := by
    simpa using sum_mul_sq_le_sq_mul_sq (Ico a (a+Y)) (fun _ => (1:ℝ)) (fun n => ‖F n‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (hCS.trans (smoothed_bilinear_energy P b θ a Y))

end JointDickman

end OAI
