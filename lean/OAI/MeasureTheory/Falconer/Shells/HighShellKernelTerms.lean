import OAI.MeasureTheory.Falconer.Shells.HighShellEndpointTerms
import OAI.MeasureTheory.Falconer.Fourier.DistanceKernelSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

 theorem integrable_list_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : List ι) (f : ι → α → ℂ) (hf : ∀ i ∈ L, Integrable (f i) μ) :
    Integrable (fun x => (L.map (fun i => f i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hf i (by simp)).add (ih (fun a ha => hf a (by simp [ha])))

 theorem integral_list_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : List ι) (f : ι → α → ℂ) (hf : ∀ i ∈ L, Integrable (f i) μ) :
    (∫ x, (L.map (fun i => f i x)).sum ∂μ) = (L.map (fun i => ∫ x, f i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hf i (by simp)) (integrable_list_sum μ L f (fun a ha => hf a (by simp [ha]))),
      ih (fun a ha => hf a (by simp [ha]))]

namespace PositiveDistanceData

 theorem inverse_angular_kernel_terms (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (j : ℕ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (r : ℝ) (z : Plane × Plane) :
    (∫ dir, sourcePlaneWave r dir (z.1-z.2) *
      (ψ dir * inverseCircleOperator j (d.pairMaskSymbol z) dir) ∂sourceArcLength) =
      ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
        b.1 * ((assignmentScale d.inverseDescriptorList d.N d.sig b.2:ℂ) *
          sourceDistanceKernel ψ (d.inverseEndpointSymbol b.2 0)
            (d.inverseEndpointSymbol b.2 1) r z.1 z.2))).sum := by
  let L := inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)
  let f := fun (b : ℂ × (PairMaskIndex → ℕ)) (dir : UnitCircle) =>
    b.1 * ((assignmentScale d.inverseDescriptorList d.N d.sig b.2:ℂ) *
      (sourcePlaneWave r dir (z.1-z.2) * (ψ dir * d.inverseEndpointSymbol b.2 0 z.1 dir *
        conj (d.inverseEndpointSymbol b.2 1 z.2 dir))))
  have he (dir : UnitCircle) : sourcePlaneWave r dir (z.1-z.2) *
      (ψ dir * inverseCircleOperator j (d.pairMaskSymbol z) dir) = (L.map (fun b => f b dir)).sum := by
    rw [d.inverseCircleOperator_pair_terms hQ]
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    dsimp [f]
    ring
  have hi : ∀ b ∈ L, Integrable (f b) sourceArcLength := by
    intro b hb
    have hm₁ : Measurable (fun dir => d.inverseEndpointSymbol b.2 0 z.1 dir) :=
      (d.inverseEndpointSymbol_measurable b.2 0).comp
        (f := fun dir : UnitCircle => (z.1,dir)) (measurable_const.prodMk measurable_id)
    have hm₂ : Measurable (fun dir => d.inverseEndpointSymbol b.2 1 z.2 dir) :=
      (d.inverseEndpointSymbol_measurable b.2 1).comp
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
        (d.inverseEndpointSymbol_norm hQ j hb 0) (d.inverseEndpointSymbol_norm hQ j hb 1) r dir z.1 z.2
  simp_rw [he]
  rw [integral_list_sum sourceArcLength L f hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [f, integral_const_mul, sourceDistanceKernel]

 theorem inverseCircleIntegral_kernel_terms (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (n : ℕ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (r : ℝ) (z : Plane × Plane) :
    sourceInverseCircleIntegral n r (z.1-z.2) ψ (d.pairMaskSymbol z) =
      (((r*dist z.1 z.2)^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        (((r*dist z.1 z.2)⁻¹:ℝ):ℂ)^j *
          ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
            b.1 * ((assignmentScale d.inverseDescriptorList d.N d.sig b.2:ℂ) *
              sourceDistanceKernel ψ (d.inverseEndpointSymbol b.2 0)
                (d.inverseEndpointSymbol b.2 1) r z.1 z.2))).sum := by
  unfold sourceInverseCircleIntegral
  simp only [← dist_eq_norm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact d.inverse_angular_kernel_terms hQ j ψ hψ hP hp r z

end PositiveDistanceData

end PlanarFalconer

end OAI
