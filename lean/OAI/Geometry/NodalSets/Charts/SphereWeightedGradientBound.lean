import OAI.Geometry.NodalSets.Charts.SphereChartUniformH1Bounds

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
noncomputable section

theorem sphere_weighted_gradient_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ (z : SphereEnergyHilbert d) (theta : Yau.Jets.Coord → ℝ),
      Continuous theta → tsupport theta ⊆ realFinCube 4 →
      (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) →
      (∀ j : Fin 4, MemLp (fun x ↦ theta x*(sphereChartDerivativeMap d p j z) x) 2 volume) ∧
      (∑ j : Fin 4, ∫ x, (theta x*(sphereChartDerivativeMap d p j z) x)^2) ≤ C*‖z‖^2 := by
  obtain ⟨C,hC,hb⟩ := sphere_chart_uniform_gradient_bound d p
  refine ⟨C,hC,fun z theta ht hs hθ ↦ ?_⟩
  have hj (j : Fin 4) := Yau.real_compact_localL2_product (realFinCube_isCompact 4)
    theta (sphereChartDerivativeMap d p j z) ht hs (Lp.memLp _)
  refine ⟨hj,le_trans (Finset.sum_le_sum (fun j _ ↦ ?_)) (hb z)⟩
  have he : (∫ x, (theta x*(sphereChartDerivativeMap d p j z) x)^2) =
      ∫ x in realFinCube 4, (theta x*(sphereChartDerivativeMap d p j z) x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),zero_mul,zero_pow (by decide)]
  rw [he]
  apply integral_mono (hj j).integrable_sq.integrableOn (Lp.memLp _).integrable_sq
  intro x
  have hsq : (theta x)^2 ≤ 1 := by nlinarith [(hθ x).1,(hθ x).2]
  dsimp only
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

end
end Yau.Target

end OAI
