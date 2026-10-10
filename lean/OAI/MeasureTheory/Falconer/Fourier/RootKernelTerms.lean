import OAI.MeasureTheory.Falconer.Shells.RootEndpointTerms
import OAI.MeasureTheory.Falconer.Shells.HighShellKernelTerms

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

 theorem root_inverse_angular_kernel_terms (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (j : ℕ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (r : ℝ) (z : Plane × Plane) :
    (∫ dir, sourcePlaneWave r dir (z.1-z.2) *
      (ψ dir * inverseCircleOperator j (rootPairSymbol d e N sig z) dir) ∂sourceArcLength) =
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
        b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
          sourceDistanceKernel ψ (rootLeftSymbol d N sig b.2)
            (rootRightSymbol e N sig b.2) r z.1 z.2))).sum := by
  let L := inverseLeibnizTerms j (rootMaskIndices d e)
  let f := fun (b : ℂ × (RootMaskIndex → ℕ)) (dir : UnitCircle) =>
    b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
      (sourcePlaneWave r dir (z.1-z.2) * (ψ dir * rootLeftSymbol d N sig b.2 z.1 dir *
        conj (rootRightSymbol e N sig b.2 z.2 dir))))
  have heq (dir : UnitCircle) : sourcePlaneWave r dir (z.1-z.2) *
      (ψ dir * inverseCircleOperator j (rootPairSymbol d e N sig z) dir) = (L.map (fun b => f b dir)).sum := by
    rw [root_inverseCircleOperator_terms d e hd he N sig]
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    dsimp [f]
    ring
  have hi : ∀ b ∈ L, Integrable (f b) sourceArcLength := by
    intro b hb
    have hm₁ : Measurable (fun dir => rootLeftSymbol d N sig b.2 z.1 dir) :=
      (rootLeftSymbol_measurable d N sig b.2).comp
        (f := fun dir : UnitCircle => (z.1,dir)) (measurable_const.prodMk measurable_id)
    have hm₂ : Measurable (fun dir => rootRightSymbol e N sig b.2 z.2 dir) :=
      (rootRightSymbol_measurable e N sig b.2).comp
        (f := fun dir : UnitCircle => (z.2,dir)) (measurable_const.prodMk measurable_id)
    apply Integrable.const_mul
    apply Integrable.const_mul
    refine Integrable.of_bound ?_
      (P*(symbolDerivativeConstant (2*j)^(2*j))*(symbolDerivativeConstant (2*j)^(2*j))) ?_
    · apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · unfold sourcePlaneWave; fun_prop
      · exact (hψ.mul hm₁).mul (Complex.continuous_conj.measurable.comp hm₂)
    · filter_upwards with dir
      exact distance_integrand_norm_le ψ _ _ hP
        (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
        (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _) hp
        (rootLeftSymbol_norm d e hd N j sig hb) (rootRightSymbol_norm d e he N j sig hb) r dir z.1 z.2
  simp_rw [heq]
  rw [integral_list_sum sourceArcLength L f hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [f, integral_const_mul, sourceDistanceKernel]

 theorem root_inverseCircleIntegral_kernel_terms (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (n : ℕ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (r : ℝ) (z : Plane × Plane) :
    sourceInverseCircleIntegral n r (z.1-z.2) ψ (rootPairSymbol d e N sig z) =
      (((r*dist z.1 z.2)^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        (((r*dist z.1 z.2)⁻¹:ℝ):ℂ)^j *
          ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
            b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
              sourceDistanceKernel ψ (rootLeftSymbol d N sig b.2)
                (rootRightSymbol e N sig b.2) r z.1 z.2))).sum := by
  unfold sourceInverseCircleIntegral
  simp only [← dist_eq_norm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact root_inverse_angular_kernel_terms d e hd he N sig j ψ hψ hP hp r z

end PlanarFalconer

end OAI
