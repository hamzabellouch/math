import OAI.Analysis.IrrationalRotation.Model.ColumnOperator
import OAI.Analysis.IrrationalRotation.Analysis.StrongFieldMeasurability
import Mathlib.Topology.Instances.Rat

namespace OAI

namespace Invariant233.Fields

open MeasureTheory

variable {ι H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem denseRange_basis_linearCombination (b : HilbertBasis ι ℂ H) :
    DenseRange (Finsupp.linearCombination ℂ b) := by
  change Dense (LinearMap.range (Finsupp.linearCombination ℂ b) : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Finsupp.range_linearCombination]
  exact b.dense_span

theorem columnOperator_linearCombination (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ}
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (z : ι →₀ ℂ) :
    columnOperator b c (Finsupp.linearCombination ℂ b z) =
      Finsupp.linearCombination ℂ c z := by
  exact LinearMap.extendOfNorm_eq (denseRange_basis_linearCombination b) ⟨C, hbound⟩ z

theorem columnOperator_apply_basis (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ}
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (i : ι) : columnOperator b c (b i) = c i := by
  classical
  simpa using columnOperator_linearCombination b c hbound (Finsupp.single i 1)

theorem norm_columnOperator_le (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖) :
    ‖columnOperator b c‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_basis_linearCombination b) hC hbound

theorem columnOperator_unique (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ}
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (T : H →L[ℂ] F) (hT : ∀ i, T (b i) = c i) : columnOperator b c = T := by
  apply LinearMap.extendOfNorm_unique (denseRange_basis_linearCombination b) C hbound T
  ext i
  simp [hT]

theorem denseRange_rationalComplex : DenseRange rationalComplex := by
  have hq := Rat.isDenseEmbedding_coe_real.dense
  have hprod := hq.prodMap hq
  have h := Complex.equivRealProdCLM.symm.surjective.denseRange.comp hprod
    Complex.equivRealProdCLM.symm.continuous
  change DenseRange (fun q : ℚ × ℚ =>
    Complex.equivRealProdCLM.symm ((q.1 : ℝ), (q.2 : ℝ)))
  simpa only [Function.comp_def, Prod.map] using h

omit [CompleteSpace F] in

theorem finite_combination_bound_of_rational
    (b : HilbertBasis ι ℂ H) (c : ι → F) {C : ℝ}
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ,
      ‖∑ i : s, rationalComplex (q i) • c i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖) :
    ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖ := by
  classical
  intro z
  have hd : DenseRange (fun q : z.support → ℚ × ℚ =>
      fun i : z.support => rationalComplex (q i)) :=
    DenseRange.piMap (fun _ => denseRange_rationalComplex)
  have h : ‖∑ i : z.support, z i • c i‖ ≤ C * ‖∑ i : z.support, z i • b i‖ := by
    exact hd.induction_on
      (p := fun a : z.support → ℂ =>
        ‖∑ i : z.support, a i • c i‖ ≤ C * ‖∑ i : z.support, a i • b i‖)
      (fun i : z.support => z i)
      (isClosed_le (by fun_prop) (by fun_prop)) (hbound z.support)
  rw [z.support.sum_coe_sort (fun i => z i • c i),
    z.support.sum_coe_sort (fun i => z i • b i)] at h
  exact h

variable {X : Type*} [MeasurableSpace X] [Countable ι]

theorem stronglyMeasurable_columnOperator_apply
    (b : HilbertBasis ι ℂ H) (c : X → ι → F) {C : ℝ}
    (hbound : ∀ x, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (c x) z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (hc : ∀ i, StronglyMeasurable fun x => c x i)
    {v : X → H} (hv : StronglyMeasurable v) :
    StronglyMeasurable fun x => columnOperator b (c x) (v x) := by
  apply StrongField.stronglyMeasurable_apply_of_columns b
  · intro i
    simpa only [columnOperator_apply_basis b _ (hbound _)] using hc i
  · exact hv

theorem aestronglyMeasurable_columnOperator_apply
    (b : HilbertBasis ι ℂ H) (c : X → ι → F) {C : ℝ} {μ : Measure X}
    (hbound : ∀ᵐ x ∂μ, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (c x) z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (hc : ∀ i, AEStronglyMeasurable (fun x => c x i) μ)
    {v : X → H} (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => columnOperator b (c x) (v x)) μ := by
  apply StrongField.aestronglyMeasurable_apply_of_columns b
  · intro i
    apply (hc i).congr
    filter_upwards [hbound] with x hx
    exact (columnOperator_apply_basis b (c x) hx i).symm
  · exact hv

omit [CompleteSpace F] in

theorem ae_finite_combination_bound_of_rational
    (b : HilbertBasis ι ℂ H) (c : X → ι → F) {C : ℝ} {μ : Measure X}
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖) :
    ∀ᵐ x ∂μ, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (c x) z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖ := by
  have hs : ∀ s : Finset ι, ∀ᵐ x ∂μ, ∀ q : s → ℚ × ℚ,
      ‖∑ i : s, rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖ := by
    intro s
    exact ae_all_iff.mpr (hbound s)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact finite_combination_bound_of_rational b (c x) hx

theorem exists_bounded_field_of_rational_column_tests
    (b : HilbertBasis ι ℂ H) (c : X → ι → F) {C : ℝ} {μ : Measure X}
    (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖)
    (hc : ∀ i, AEStronglyMeasurable (fun x => c x i) μ) :
    ∃ A : X → H →L[ℂ] F,
      (∀ᵐ x ∂μ, ‖A x‖ ≤ C ∧ ∀ i, A x (b i) = c x i) ∧
      (∀ v : H, AEStronglyMeasurable (fun x => A x v) μ) := by
  have hb := ae_finite_combination_bound_of_rational b c hbound
  refine ⟨fun x => columnOperator b (c x), ?_, ?_⟩
  · filter_upwards [hb] with x hx
    exact ⟨norm_columnOperator_le b (c x) hC hx,
      columnOperator_apply_basis b (c x) hx⟩
  · intro v
    exact aestronglyMeasurable_columnOperator_apply b c hb hc aestronglyMeasurable_const

end Invariant233.Fields

end OAI
