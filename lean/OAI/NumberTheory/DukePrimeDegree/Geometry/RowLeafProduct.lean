import OAI.NumberTheory.DukePrimeDegree.Geometry.RowSingleMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.RowLeafConstancy
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafNormalizationInjectivity

namespace OAI

/-!
# Product disintegration in actual row boxes

Neutral holonomy removes dependence of a normalized one-root leaf on
the other row coordinates. Nested disintegration then gives the
one-coordinate product step in a cubical row box.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rowBox_ae_nested_of_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    {P : RootSlice i j k × ℝ → Prop}
    (h : ∀ᵐ z ∂(B.singleRootBox hij hR hT).coordinateMeasure μ, P z) :
    ∀ᵐ s ∂(rowSplitMeasure hij (B.coordinateMeasure μ)).fst,
      ∀ᵐ w ∂((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).fst,
        ∀ᵐ t ∂((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).condKernel w,
          P ((rowReducedHomeomorph hij k).symm (s, w), t) := by
  let σ := rowSplitMeasure hij (B.coordinateMeasure μ)
  have he : (B.singleRootBox hij hR hT).coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map
        (Prod.map (rowReducedHomeomorph hij k).symm id) := by
    exact (singleRootBox_coordinateMeasure hij B hR hT μ).trans
      (rowSingleMeasure_eq_map hij (B.coordinateMeasure μ)).symm
  rw [he] at h
  have h₁ := ae_of_ae_map (by fun_prop : AEMeasurable
    (Prod.map (rowReducedHomeomorph hij k).symm id) (σ.map MeasurableEquiv.prodAssoc.symm)) h
  have h₂ := ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable h₁
  have hmap (z : RowRootSlice i k × (RowRemainingTime i j × ℝ)) :
      Prod.map (rowReducedHomeomorph hij k).symm id (MeasurableEquiv.prodAssoc.symm z) =
        ((rowReducedHomeomorph hij k).symm (z.1, z.2.1), z.2.2) := rfl
  have h₃ : ∀ᵐ s ∂σ.fst, ∀ᵐ z ∂σ.condKernel s,
      P ((rowReducedHomeomorph hij k).symm (s, z.1), z.2) := by
    have H : ∀ᵐ z ∂σ.fst ⊗ₘ σ.condKernel,
        P ((rowReducedHomeomorph hij k).symm (z.1, z.2.1), z.2.2) := by
      simpa only [Measure.disintegrate, hmap] using h₂
    exact Measure.ae_ae_of_ae_compProd H
  filter_upwards [h₃] with s hs
  have H : ∀ᵐ z ∂(σ.condKernel s).fst ⊗ₘ (σ.condKernel s).condKernel,
      P ((rowReducedHomeomorph hij k).symm (s, z.1), z.2) := by
    simpa only [Measure.disintegrate] using hs
  exact Measure.ae_ae_of_ae_compProd H

/-- In a cubical row box, the selected real coordinate is independent of
the other row coordinates, conditional on the transverse coordinate. -/
theorem rowBox_ae_real_conditionals_constant
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j) {k : Fin (d + 1)}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ s ∂(rowSplitMeasure hij (B.coordinateMeasure μ)).fst,
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ᵐ w ∂((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).fst,
          ((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).condKernel w = ν := by
  let A := B.singleRootBox hij hR hT
  let σ := rowSplitMeasure hij (B.coordinateMeasure μ)
  have hAR : A.time ⊆ rootLeafWindow R 0 := by
    change Ioo (-R) R ⊆ rootLeafWindow R 0
    simp only [rootLeafWindow, Nat.cast_zero, add_zero, subset_refl]
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨N, _hN, hN0, hhol⟩ := exists_nullset_row_leaf_holonomy d hij μ hA
  have havoid : ∀ᵐ x ∂μ, x ∉ N := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hN0
  let F := A.leafMeasure R μ
  let P : RootSlice i j k × ℝ → Prop := fun z =>
    A.IsNormalizedRootLeaf R μ z.1 (F z.1) ∧
    0 < F z.1 (Metric.ball z.2 1) ∧
    intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = basedRealMeasure (F z.1) z.2 ∧
    rootQuotientParametrization hij z ∉ N
  have hP : ∀ᵐ z ∂A.coordinateMeasure μ, P z := by
    have hspec := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
    filter_upwards [hspec, A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
      A.ae_coordinate_of_ambient μ havoid] with z hs hp hb hn
    exact ⟨hs, hp 1 zero_lt_one, hb, hn⟩
  have hnested := rowBox_ae_nested_of_single hij B hR hT μ hP
  filter_upwards [hnested, rowBox_root_conditional_compatibility hij B hR hT μ] with s hs hc
  have hgood : ∀ᵐ w ∂(σ.condKernel s).fst,
      (∀ᵐ t ∂(σ.condKernel s).condKernel w,
        P ((rowReducedHomeomorph hij k).symm (s, w), t)) ∧
      A.conditionalKernel μ ((rowReducedHomeomorph hij k).symm (s, w)) =
        (σ.condKernel s).condKernel w := hs.and hc
  obtain ⟨w₀, hw₀, hc₀⟩ := hgood.exists
  obtain ⟨t₀, ht₀⟩ := hw₀.exists
  refine ⟨(σ.condKernel s).condKernel w₀, inferInstance, ?_⟩
  filter_upwards [hgood] with w hw
  obtain ⟨t, ht⟩ := hw.1.exists
  let s₀ := (rowReducedHomeomorph hij k).symm (s, w₀)
  let s₁ := (rowReducedHomeomorph hij k).symm (s, w)
  let : IsLocallyFiniteMeasure (F s₀) := ht₀.1.1
  let : IsLocallyFiniteMeasure (F s₁) := ht.1.1
  have hleaf : F s₀ = F s₁ := by
    apply eq_of_rebasedRealMeasure_eq (F s₀) (F s₁) A.time ht₀.1.2.1 ht.1.2.1
      t₀ t ht₀.2.1 ht.2.1
    rw [← ht₀.2.2.1, ← ht.2.2.1]
    have hpoint (v : RowRemainingTime i j) (u : ℝ) :
        rootQuotientParametrization hij ((rowReducedHomeomorph hij k).symm (s, v), u) =
          rightAction (rowQuotientParametrization i k (s, 0))
            (rowRoot i (v.val + u • rowUnit hij)) := by
      rw [row_one_root_parametrization, ← rowQuotientParametrization_add, zero_add]
    have h₀ := ht₀.2.2.2
    have h₁ := ht.2.2.2
    simp only [hpoint] at h₀ h₁ ⊢
    have H := hhol (rowQuotientParametrization i k (s, 0))
      (w₀.val + t₀ • rowUnit hij) (w.val + t • rowUnit hij) h₀ h₁
    simpa only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, rowRemainingTime_self, rowUnit_apply_self, mul_one, zero_add] using H
  have hrestr := congrArg (fun η : Measure ℝ => η.restrict A.time) hleaf
  rw [ht₀.1.2.2.1, ht.1.2.2.1, hc₀, hw.2] at hrestr
  exact hrestr.symm

/-- The actual conditional row measure splits into its marginal on the
remaining coordinates and its marginal on the selected coordinate. -/
theorem rowBox_ae_conditional_eq_prod
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j) {k : Fin (d + 1)}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ s ∂(rowSplitMeasure hij (B.coordinateMeasure μ)).fst,
      (rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s =
        ((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).fst.prod
          ((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).snd := by
  filter_upwards [rowBox_ae_real_conditionals_constant d hij B hR hT μ hA] with s hs
  obtain ⟨ν, hνprob, hν⟩ := hs
  let := hνprob
  have he := eq_prod_of_constant_real_conditionals _ ν hν
  have hm := congrArg (fun ρ : Measure (RowRemainingTime i j × ℝ) => ρ.snd) he
  rw [Measure.snd_prod] at hm
  simpa only [hm] using he

end DukePrimeDegree

end

end OAI
