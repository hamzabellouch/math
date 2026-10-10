import OAI.MeasureTheory.Falconer.Estimates.DistanceFormFubini

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem measurable_sourceDistanceKernel (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (fun z : ℝ × (Plane × Plane) => sourceDistanceKernel ψ b₁ b₂ z.1 z.2.1 z.2.2) := by
  have hf : Measurable (fun z : (ℝ × (Plane × Plane)) × UnitCircle =>
      sourcePlaneWave z.1.1 z.2 (z.1.2.1-z.1.2.2) *
        (ψ z.2 * b₁ z.1.2.1 z.2 * conj (b₂ z.1.2.2 z.2))) := by
    apply Measurable.mul
    · unfold sourcePlaneWave
      fun_prop
    · exact (((hψ.comp measurable_snd).mul
        (h₁.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))).mul
        (Complex.continuous_conj.measurable.comp
          (h₂.comp ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem sourceDistanceKernel_norm_le (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {P B₁ B₂ : ℝ}
    (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) (x y : Plane) :
    ‖sourceDistanceKernel ψ b₁ b₂ r x y‖ ≤ P*B₁*B₂*sourceArcLength.real univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun dir =>
    distance_integrand_norm_le ψ b₁ b₂ hP hB₁ hB₂ hp hb₁ hb₂ r dir x y))

theorem DyadicSquare.pair_integral_split_occupied
    (P Q : DyadicSquare) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ)
    (F : Plane → Plane → ℂ) (hF : Measurable (fun z : Plane × Plane => F z.1 z.2))
    (C : ℝ) (hC : ∀ x y, ‖F x y‖ ≤ C) :
    (∫ x in P.carrier, ∫ y in Q.carrier, F x y ∂ν ∂ρ) =
      ∑ A ∈ occupiedAnchorPaths P ρ n, ∑ B ∈ occupiedAnchorPaths Q ν m,
        ∫ x in (P.descendant A).carrier, ∫ y in (Q.descendant B).carrier, F x y ∂ν ∂ρ := by
  have hi (X Y : Set Plane) : Integrable (fun z : Plane × Plane => F z.1 z.2)
      ((ρ.restrict X).prod (ν.restrict Y)) :=
    (integrable_const C).mono hF.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => (hC z.1 z.2).trans (le_abs_self C)))
  have hy (x : Plane) : IntegrableOn (F x) Q.carrier ν :=
    (integrable_const C).mono
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => (hC x y).trans (le_abs_self C)))
  rw [P.integral_split_occupied hP ρ n _ (hi _ _).integral_prod_left]
  apply Finset.sum_congr rfl
  intro A _
  simp_rw [Q.integral_split_occupied hQ ν m _ (hy _)]
  apply integral_finsetSum
  intro B _
  exact (hi _ _).integral_prod_left

theorem sourceDistanceF_split (P Q : DyadicSquare) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ)
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {W B₁ B₂ : ℝ} (hW : 0 ≤ W) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hw : ∀ dir, ‖ψ dir‖ ≤ W) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ (fun z => sourceAngularTransform ρ P.carrier Ma₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Q.carrier Ma₂ b₂ z.1 z.2) r =
      ((Mp₁/Ma₁)*(Mp₂/Ma₂)) •
        ∑ A ∈ occupiedAnchorPaths P ρ n, ∑ B ∈ occupiedAnchorPaths Q ν m,
          sourceDistanceF ψ
            (fun z => sourceAngularTransform ρ (P.descendant A).carrier Mp₁ b₁ z.1 z.2)
            (fun z => sourceAngularTransform ν (Q.descendant B).carrier Mp₂ b₂ z.1 z.2) r := by
  simp_rw [sourceDistanceF_endpoint_integral ρ ν _ _ _ _ ψ b₁ b₂ hψ h₁ h₂ hW hB₁ hB₂ hw hb₁ hb₂]
  rw [P.pair_integral_split_occupied Q hP hQ ρ ν n m _
    ((measurable_sourceDistanceKernel ψ b₁ b₂ hψ h₁ h₂).comp (measurable_const.prodMk measurable_id))
    (W*B₁*B₂*sourceArcLength.real univ)
    (sourceDistanceKernel_norm_le ψ b₁ b₂ hW hB₁ hB₂ hw hb₁ hb₂ r)]
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  field_simp

end PlanarFalconer

end OAI
