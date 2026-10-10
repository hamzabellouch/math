import OAI.Analysis.KadisonKastler.MinimalSpatialImplementer
import OAI.Analysis.KadisonKastler.AbelianDerivationAveraging

namespace OAI

/-! # The convex family of minimum-distance spatial residuals

For a minimizing pair, the residuals with no larger norm form a convex
set invariant under the unitaries of the commutant. Every member has
exactly the minimum norm. A strict norm decrease inside this set is
therefore impossible.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundedSpatialResiduals (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) : Set (H →L[ℂ] H) :=
  {C | IsSelfAdjoint C ∧ ‖C‖ ≤ r ∧ ‖X - C‖ ≤ ‖T‖ ∧ X - C - T ∈ M.commutant}

theorem boundedSpatialResiduals_convex (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) : Convex ℝ (boundedSpatialResiduals M T X r) := by
  intro C hC D hD a b ha hb hab
  have he : X - (a • C + b • D) = a • (X - C) + b • (X - D) := by
    calc
      _ = (a + b) • X - (a • C + b • D) := by rw [hab, one_smul]
      _ = _ := by module
  have heT : X - (a • C + b • D) - T =
      a • (X - C - T) + b • (X - D - T) := by
    rw [he]
    calc
      _ = a • (X - C) + b • (X - D) - (a + b) • T := by rw [hab, one_smul]
      _ = _ := by module
  refine ⟨?_, ?_, ?_, ?_⟩
  · change star (a • C + b • D) = a • C + b • D
    simp only [star_add, star_smul, star_trivial, hC.1.star_eq, hD.1.star_eq]
  · have hc := (convex_closedBall (0 : H →L[ℂ] H) r)
      (show C ∈ Metric.closedBall 0 r by simpa only [Metric.mem_closedBall, dist_zero_right] using hC.2.1)
      (show D ∈ Metric.closedBall 0 r by simpa only [Metric.mem_closedBall, dist_zero_right] using hD.2.1) ha hb hab
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  · rw [he]
    have hc := (convex_closedBall (0 : H →L[ℂ] H) ‖T‖)
      (show X - C ∈ Metric.closedBall 0 ‖T‖ by simpa only [Metric.mem_closedBall, dist_zero_right] using hC.2.2.1)
      (show X - D ∈ Metric.closedBall 0 ‖T‖ by simpa only [Metric.mem_closedBall, dist_zero_right] using hD.2.2.1) ha hb hab
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  · rw [heT]
    exact M.commutant.add_mem
      ((M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem hC.2.2.2 a)
      ((M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem hD.2.2.2 b)

theorem boundedSpatialResiduals_conjugate (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) (hX : X ∈ M)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M.commutant)
    (C : H →L[ℂ] H) (hC : C ∈ boundedSpatialResiduals M T X r) :
    unitaryConj u C ∈ boundedSpatialResiduals M T X r := by
  have hXu : X * (u : H →L[ℂ] H) = (u : H →L[ℂ] H) * X :=
    VonNeumannAlgebra.mem_commutant_iff.mp hu X hX
  have hfix : unitaryConj u X = X := by
    change (u : H →L[ℂ] H) * X * star (u : H →L[ℂ] H) = X
    rw [← hXu, mul_assoc, u.property.2, mul_one]
  have he : X - unitaryConj u C = unitaryConj u (X - C) := by
    rw [unitaryConj_sub, hfix]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change star ((u : H →L[ℂ] H) * C * star (u : H →L[ℂ] H)) = _
    simp only [star_mul, star_star, hC.1.star_eq, unitaryConj, mul_assoc]
  · simpa only [norm_unitaryConj] using hC.2.1
  · rw [he, norm_unitaryConj]
    exact hC.2.2.1
  · have hd := unitaryConj_sub_mem_commutant_of_preserves M T hT u hu
    have hm : unitaryConj u (X - C - T) ∈ M.commutant :=
      M.commutant.mul_mem (M.commutant.mul_mem hu hC.2.2.2)
        (M.commutant.toStarSubalgebra.star_mem' hu)
    have hh : X - unitaryConj u C - T =
        unitaryConj u (X - C - T) + (unitaryConj u T - T) := by
      rw [he]
      simp only [unitaryConj_sub]
      abel
    rw [hh]
    exact M.commutant.add_mem hm hd

theorem boundedSpatialResiduals_norm_eq (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) (hX : IsSelfAdjoint X)
    (hmin : ∀ V : H →L[ℂ] H, IsSelfAdjoint V → ‖V‖ ≤ ‖T‖ →
      V - T ∈ M.commutant → r ≤ ‖X - V‖)
    (C : H →L[ℂ] H) (hC : C ∈ boundedSpatialResiduals M T X r) : ‖C‖ = r := by
  apply le_antisymm hC.2.1
  have hh := hmin (X - C) (hX.sub hC.1) hC.2.2.1 hC.2.2.2
  simpa only [sub_sub_cancel] using hh

end

end KadisonKastler

end OAI
