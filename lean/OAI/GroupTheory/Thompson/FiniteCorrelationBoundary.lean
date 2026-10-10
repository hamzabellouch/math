import OAI.GroupTheory.Thompson.DisplacementEstimate
import OAI.GroupTheory.Thompson.CorrelationVariance
import OAI.GroupTheory.Thompson.BoundaryAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-!
# From the actual recursive vectors and correlations to a boundary bound

This finite analytic bridge averages the pointwise displacement estimate and
uses the exact correlation variance theorem. Its intermediate hypotheses are
later supplied by the actual dyadic coloring and affine transports.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe uG uE

namespace ThompsonNonamenability

variable {G : Type uG} {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

theorem finite_energy_of_variance (A : Finset G) (hA : A.Nonempty) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (L δ V : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ u v, ‖(f u : E) - f v‖ ≤ L * ‖(u : E) - v‖)
    (hDisp : ∀ u, δ ≤ ‖(f u : E) - u‖)
    (x z : G → Fin D → UnitBall E)
    (hrec : ∀ g ∈ A, ∀ i, x g i = f (z g i))
    (hvar : ∀ i, realAvg A
      (fun g => ‖(z g i : E) - (ballMean hD (x g) : E)‖ ^ 2) ≤ V) :
    δ ^ 2 ≤ L ^ 2 * V := by
  have havg := const_le_realAvg A hA (fun g hg =>
    displacement_le_mean_energy hD f L δ hL hδ hLip hDisp (x g) (z g) (hrec g hg))
  rw [realAvg_const_mul, realAvg_sum_univ] at havg
  have hsum : (∑ i, realAvg A
      (fun g => ‖(z g i : E) - (ballMean hD (x g) : E)‖ ^ 2)) ≤ (D : ℝ) * V := by
    calc
      _ ≤ ∑ _i : Fin D, V := Finset.sum_le_sum (fun i _ => hvar i)
      _ = (D : ℝ) * V := by simp [nsmul_eq_mul]
  have hfactor : 0 ≤ L ^ 2 * (D : ℝ)⁻¹ :=
    mul_nonneg (sq_nonneg L) (inv_nonneg.mpr (Nat.cast_nonneg D))
  have hDn : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  calc
    δ ^ 2 ≤ (L ^ 2 * (D : ℝ)⁻¹) * ∑ i, realAvg A
        (fun g => ‖(z g i : E) - (ballMean hD (x g) : E)‖ ^ 2) := havg
    _ ≤ (L ^ 2 * (D : ℝ)⁻¹) * ((D : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = L ^ 2 * V := by
      field_simp [hDn]

theorem boundaryConstant_le_of_correlations (A : Finset G) (hA : A.Nonempty)
    (hD : 2 ≤ D) (f : UnitBall E → UnitBall E) (L δ α η : ℝ)
    (hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ u v, ‖(f u : E) - f v‖ ≤ L * ‖(u : E) - v‖)
    (hDisp : ∀ u, δ ≤ ‖(f u : E) - u‖)
    (x : G → Fin D → UnitBall E) (y : G → Fin D → Fin D → UnitBall E)
    (hrec : ∀ g ∈ A, ∀ i,
      x g i = f (ballMean (lt_of_lt_of_le (by decide : 0 < 2) hD) (y g i)))
    (hparent : ∀ j k, j ≠ k →
      |corr A (fun g => (x g j : E)) (fun g => (x g k : E)) - α| ≤ η)
    (hchild : ∀ i j k, j ≠ k →
      |corr A (fun g => (y g i j : E)) (fun g => (y g i k : E)) - α| ≤ η)
    (hmixed : ∀ i j k, k ≠ i →
      |corr A (fun g => (y g i j : E)) (fun g => (x g k : E)) - α| ≤ η) :
    boundaryConstant L δ D ≤ η := by
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) hD
  have hvar := finite_variance_bound A hA hDpos
    (fun g i => (x g i : E)) (fun g i j => (y g i j : E)) α η
    (fun g _ i => (x g i).property) (fun g _ i j => (y g i j).property)
    hparent hchild hmixed
  have henergy := finite_energy_of_variance A hA hDpos f L δ
    (4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η) hL hδ hLip hDisp x
    (fun g i => ballMean hDpos (y g i)) hrec (by
      intro i
      simpa only [coe_ballMean] using hvar i)
  exact boundaryConstant_le_of_energy hL hD henergy

end ThompsonNonamenability

end

end OAI
