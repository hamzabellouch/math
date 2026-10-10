import OAI.MeasureTheory.Falconer.Estimates.DistanceFormRemoval

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceCellwiseDistanceF (P Q : DyadicSquare)
    (ρ ν : Measure Plane) (n m : ℕ) (M₁ M₂ : ℝ)
    (ψ : CellPath → CellPath → UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) : ℂ :=
  ∑ A ∈ occupiedAnchorPaths P ρ n, ∑ B ∈ occupiedAnchorPaths Q ν m,
    sourceDistanceF (ψ A B)
      (fun z => sourceAngularTransform ρ (P.descendant A).carrier M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν (Q.descendant B).carrier M₂ b₂ z.1 z.2) r

theorem measurable_sourceCellwiseDistanceF (P Q : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n m : ℕ) (M₁ M₂ : ℝ) (ψ : CellPath → CellPath → UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : ∀ A B, Measurable (ψ A B))
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (sourceCellwiseDistanceF P Q ρ ν n m M₁ M₂ ψ b₁ b₂) := by
  unfold sourceCellwiseDistanceF
  apply Finset.measurable_sum
  intro A _
  apply Finset.measurable_sum
  intro B _
  exact measurable_sourceDistanceF _ _ _ (hψ A B)
    (measurable_sourceAngularTransform ρ _ M₁ b₁ h₁)
    (measurable_sourceAngularTransform ν _ M₂ b₂ h₂)

theorem sourceCellwiseDistanceF_profile_ratios (P Q : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n m : ℕ) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (ψ : CellPath → CellPath → UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hψ : ∀ A B, Measurable (ψ A B))
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {W B₁ B₂ : ℝ} (hW : 0 ≤ W) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hw : ∀ A B dir, ‖ψ A B dir‖ ≤ W) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceCellwiseDistanceF P Q ρ ν n m Ma₁ Ma₂ ψ b₁ b₂ r =
      ((Mp₁/Ma₁)*(Mp₂/Ma₂)) • sourceCellwiseDistanceF P Q ρ ν n m Mp₁ Mp₂ ψ b₁ b₂ r := by
  unfold sourceCellwiseDistanceF
  simp_rw [sourceDistanceF_endpoint_integral ρ ν _ _ _ _ _ b₁ b₂ (hψ _ _) h₁ h₂
    hW hB₁ hB₂ (hw _ _) hb₁ hb₂]
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  field_simp

theorem sourceCellwiseDistanceF_constant (P Q : DyadicSquare) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {W B₁ B₂ : ℝ} (hW : 0 ≤ W) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hw : ∀ dir, ‖ψ dir‖ ≤ W) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceCellwiseDistanceF P Q ρ ν n m M₁ M₂ (fun _ _ => ψ) b₁ b₂ r =
      sourceDistanceF ψ (fun z => sourceAngularTransform ρ P.carrier M₁ b₁ z.1 z.2)
        (fun z => sourceAngularTransform ν Q.carrier M₂ b₂ z.1 z.2) r := by
  have hh := sourceDistanceF_split P Q hP hQ ρ ν n m M₁ M₂ M₁ M₂ hM₁.ne' hM₂.ne'
    ψ b₁ b₂ hψ h₁ h₂ hW hB₁ hB₂ hw hb₁ hb₂ r
  simpa only [sourceCellwiseDistanceF, div_self hM₁.ne', div_self hM₂.ne', one_mul, one_smul] using hh.symm

theorem sourceCellwiseDistanceF_kernel_bound (P Q : DyadicSquare) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (ψ : CellPath → CellPath → UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hψ : ∀ A B, Measurable (ψ A B))
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {W B₁ B₂ ε : ℝ} (hW : 0 ≤ W) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hw : ∀ A B dir, ‖ψ A B dir‖ ≤ W) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ)
    (he : ∀ A ∈ occupiedAnchorPaths P ρ n, ∀ B ∈ occupiedAnchorPaths Q ν m,
      ∀ x ∈ (P.descendant A).carrier, ∀ y ∈ (Q.descendant B).carrier,
      ‖sourceDistanceKernel (ψ A B) b₁ b₂ r x y‖ ≤ ε) :
    ‖sourceCellwiseDistanceF P Q ρ ν n m M₁ M₂ ψ b₁ b₂ r‖ ≤
      ε*((ρ P.carrier).toReal/M₁)*((ν Q.carrier).toReal/M₂) := by
  unfold sourceCellwiseDistanceF
  simp_rw [sourceDistanceF_endpoint_integral ρ ν _ _ _ _ _ b₁ b₂ (hψ _ _) h₁ h₂
    hW hB₁ hB₂ (hw _ _) hb₁ hb₂]
  exact occupied_pair_error_sum_le P Q hP hQ ρ ν n m hM₁ hM₂ _ he

theorem sourceCellwiseDistanceF_partition (P Q : DyadicSquare) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (ψ : UnitCircle → ℂ) (χ : CellPath → CellPath → UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ) (hχ : ∀ A B, Measurable (χ A B))
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {W B₁ B₂ : ℝ} (hW : 0 ≤ W) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hw : ∀ dir, ‖ψ dir‖ ≤ W) (hc : ∀ A B dir, ‖χ A B dir‖ ≤ 1)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ (fun z => sourceAngularTransform ρ P.carrier M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Q.carrier M₂ b₂ z.1 z.2) r =
      sourceCellwiseDistanceF P Q ρ ν n m M₁ M₂ (fun A B dir => ψ dir*(1-χ A B dir)) b₁ b₂ r +
      sourceCellwiseDistanceF P Q ρ ν n m M₁ M₂ (fun A B dir => ψ dir*χ A B dir) b₁ b₂ r := by
  rw [← sourceCellwiseDistanceF_constant P Q hP hQ ρ ν n m hM₁ hM₂ ψ b₁ b₂ hψ h₁ h₂
    hW hB₁ hB₂ hw hb₁ hb₂ r]
  unfold sourceCellwiseDistanceF
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B _
  exact sourceDistanceF_retained_add_discarded ψ (χ A B) _ _ r hψ (hχ A B)
    ((measurable_sourceAngularTransform ρ _ M₁ b₁ h₁).comp (measurable_const.prodMk measurable_id))
    ((measurable_sourceAngularTransform ν _ M₂ b₂ h₂).comp (measurable_const.prodMk measurable_id))
    hW (by positivity) hw (hc A B)
    (sourceAngularTransform_norm_le ρ _ M₁ hM₁ b₁ B₁ (fun x _ => hb₁ x) r)
    (sourceAngularTransform_norm_le ν _ M₂ hM₂ b₂ B₂ (fun y _ => hb₂ y) r)

end PlanarFalconer

end OAI
