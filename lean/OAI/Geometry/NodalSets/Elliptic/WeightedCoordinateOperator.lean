import OAI.Geometry.NodalSets.Waves.SmoothWaveOperator

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def densityDrift (W : Coord → ℂ) (a : Fin 4 → Fin 4 → Coord → ℂ)
    (j : Fin 4) (x : Coord) : ℂ :=
  (W x)⁻¹ * ∑ i, coordPartial i (fun z ↦ W z * a i j z) x

def weightedCoordinateOperator (W : Coord → ℂ) (a : Fin 4 → Fin 4 → Coord → ℂ)
    (u : Coord → ℂ) (x : Coord) : ℂ :=
  (W x)⁻¹ * ∑ i, ∑ j,
    coordPartial i (fun z ↦ (W z * a i j z) * coordPartial j u z) x

lemma coordPartial_mul_at (f u : Coord → ℂ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (i : Fin 4) :
    coordPartial i (fun z ↦ f z * u z) x =
      coordPartial i f x * u x + f x * coordPartial i u x := by
  unfold coordPartial
  rw [fderiv_fun_mul hf hu]
  simp [smul_eq_mul]
  ring

theorem weightedCoordinateOperator_eq (W : Coord → ℂ)
    (a : Fin 4 → Fin 4 → Coord → ℂ) (u : Coord → ℂ) (x : Coord)
    (hW : W x ≠ 0)
    (hflux : ∀ i j, DifferentiableAt ℝ (fun z ↦ W z * a i j z) x)
    (hu : ∀ j, DifferentiableAt ℝ (coordPartial j u) x) :
    weightedCoordinateOperator W a u x = smoothSecondOrder a (densityDrift W a) u x := by
  unfold weightedCoordinateOperator
  simp_rw [coordPartial_mul_at _ _ x (hflux _ _) (hu _)]
  simp only [Finset.sum_add_distrib, mul_add]
  have hfirst : (W x)⁻¹ * (∑ i, ∑ j,
      coordPartial i (fun z ↦ W z * a i j z) x * coordPartial j u x) =
      ∑ j, densityDrift W a j x * coordPartial j u x := by
    rw [Finset.sum_comm]
    simp only [densityDrift, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hsecond : (W x)⁻¹ * (∑ i, ∑ j,
      W x * a i j x * coordPartial i (coordPartial j u) x) =
      ∑ i, ∑ j, a i j x * coordPartial i (coordPartial j u) x := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hfirst,hsecond]
  simp only [smoothSecondOrder]
  ring

end
end Yau.Jets

end OAI
