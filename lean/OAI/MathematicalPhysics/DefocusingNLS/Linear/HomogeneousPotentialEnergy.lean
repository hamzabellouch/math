import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPrincipalCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDerivativeEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeEnergy

namespace OAI

/-! # The actual potential pairing in the homogeneous energy

Only the principal L² norm appears in the high-order coefficient. All
remaining terms are exactly the compact error previously constructed.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLinearized_energy_pairing_bound (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q u : HomogeneousY a ((N + 1 : ℕ) : ℝ))
    (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M) :
    inner ℝ u (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) ≤
      ((2 * ((m + 1 : ℕ) : ℝ) + 1) * M) *
        ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖ ^ 2 +
      ‖u‖ * (‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk
        (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u)‖ +
        Real.sqrt (∑ j : Fin (N + 1) → Fin 12,
          ‖homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u‖ ^ 2)) := by
  let V := homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q
  let D := homogeneousPhysicalDerivative a (N + 1) ha ha1 hk
  let K := fun j => homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u
  let P := homogeneousPrincipalPotential (m + 1)
    (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q)
    (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q).continuous M hM hQB
  let B := (2 * ((m + 1 : ℕ) : ℝ) + 1) * M
  have hD (j : Fin (N + 1) → Fin 12) : D j (V u) = P (D j u) + K j := by
    have h := homogeneousLinearized_derivative_commutator a N ha ha1 hk j m q u M hM hQB
    change D j (V u) - P (D j u) = K j at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  have hhigh : inner ℝ (homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u)
      (homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk (V u)) ≤
      B * ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖ ^ 2 +
        ‖u‖ * Real.sqrt (∑ j : Fin (N + 1) → Fin 12, ‖K j‖ ^ 2) := by
    rw [← homogeneousPhysicalDerivative_inner a (N + 1) ha ha1 hk]
    have hterm (j : Fin (N + 1) → Fin 12) :
        inner ℝ (D j u) (D j (V u)) ≤ B * ‖D j u‖ ^ 2 + ‖D j u‖ * ‖K j‖ := by
      rw [hD, inner_add_right]
      exact add_le_add (homogeneousPrincipalPotential_energy_le (m + 1)
        (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q)
        (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q).continuous M hM hQB (D j u))
        (real_inner_le_norm _ _)
    calc
      _ ≤ ∑ j : Fin (N + 1) → Fin 12, (B * ‖D j u‖ ^ 2 + ‖D j u‖ * ‖K j‖) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      _ = B * ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖ ^ 2 +
          ∑ j : Fin (N + 1) → Fin 12, ‖D j u‖ * ‖K j‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 2
        exact homogeneousPhysicalDerivative_energy a (N + 1) ha ha1 hk u
      _ ≤ B * ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖ ^ 2 +
          Real.sqrt (∑ j : Fin (N + 1) → Fin 12, ‖D j u‖ ^ 2) *
            Real.sqrt (∑ j : Fin (N + 1) → Fin 12, ‖K j‖ ^ 2) :=
        add_le_add le_rfl (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun j => ‖D j u‖) (fun j => ‖K j‖))
      _ ≤ _ := by
        rw [homogeneousPhysicalDerivative_energy a (N + 1) ha ha1 hk,
          Real.sqrt_sq (norm_nonneg _)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (homogeneousHighEnergy_norm_le a ((N + 1 : ℕ) : ℝ) ha1 hk u)
          (Real.sqrt_nonneg _))
  rw [homogeneousEnergy_inner a ((N + 1 : ℕ) : ℝ) ha1 hk]
  have hlow : inner ℝ (homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u)
      (homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk (V u)) ≤
      ‖u‖ * ‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk (V u)‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (homogeneousLowEnergy_norm_le a ((N + 1 : ℕ) : ℝ) ha1 hk u) (norm_nonneg _))
  change _ ≤ B * _ + ‖u‖ * (_ + Real.sqrt (∑ j, ‖K j‖ ^ 2))
  nlinarith

theorem homogeneousLinearized_energy_observation (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M)
    (hgap : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 -
      2 * ((2 * ((m + 1 : ℕ) : ℝ) + 1) * M)) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : HomogeneousY a ((N + 1 : ℕ) : ℝ),
        -a * ‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖ ^ 2 +
          (6 - 2 * a - ((N + 1 : ℕ) : ℝ)) *
            ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖ ^ 2 +
          2 * inner ℝ u
            (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) ≤
          -c * ‖u‖ ^ 2 + C *
            ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk u‖ ^ 2 := by
  let B := (2 * ((m + 1 : ℕ) : ℝ) + 1) * M
  let g := ((N + 1 : ℕ) : ℝ) + 2 * a - 6 - 2 * B
  let γ := min a g
  have hγ : 0 < γ := lt_min ha hgap
  let ε := γ / 8
  have hε : 0 < ε := div_pos hγ (by norm_num)
  obtain ⟨R, hR, C, hC, herror⟩ := homogeneousLinearized_compact_errors a ε N ha ha1 hk m q hε
  refine ⟨γ / 2, half_pos hγ, R, hR, 4 * C ^ 2 / γ, by positivity, fun u => ?_⟩
  let x := ‖u‖
  let y := ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk u‖
  let L := ‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖
  let H := ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk u‖
  have hnorm : x ^ 2 = L ^ 2 + H ^ 2 := homogeneousEnergy_norm_sq a ((N + 1 : ℕ) : ℝ) ha1 hk u
  have hbase : -a * L ^ 2 - g * H ^ 2 ≤ -γ * x ^ 2 := by
    have h₁ := mul_nonneg (sub_nonneg.mpr (min_le_left a g)) (sq_nonneg L)
    have h₂ := mul_nonneg (sub_nonneg.mpr (min_le_right a g)) (sq_nonneg H)
    change 0 ≤ (a - γ) * L ^ 2 at h₁
    change 0 ≤ (g - γ) * H ^ 2 at h₂
    nlinarith
  have hpair : inner ℝ u
      (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) ≤
      B * H ^ 2 + x * (ε * x + C * y) := by
    exact (homogeneousLinearized_energy_pairing_bound a N ha ha1 hk m q u M hM hQB).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (herror u) (norm_nonneg u)))
  have hcross : 2 * C * x * y ≤ γ / 4 * x ^ 2 + (4 * C ^ 2 / γ) * y ^ 2 := by
    apply (mul_le_mul_iff_right₀ hγ).mp
    have hdiv : (4 * C ^ 2 / γ) * y ^ 2 * γ = 4 * C ^ 2 * y ^ 2 := by
      rw [mul_right_comm, div_mul_cancel₀ _ hγ.ne']
    nlinarith [sq_nonneg (γ * x - 4 * C * y)]
  change -a * L ^ 2 + (6 - 2 * a - ((N + 1 : ℕ) : ℝ)) * H ^ 2 +
    2 * inner ℝ u (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) ≤
      -(γ / 2) * x ^ 2 + (4 * C ^ 2 / γ) * y ^ 2
  dsimp only [g] at hbase
  dsimp only [ε] at hpair
  nlinarith

end DefocusingNLS

end OAI
