import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCompact
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteConjugateTiling

namespace OAI

/-! # Finite tilings of actual ideal boxes with exact volume bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set
open scoped Manifold ENNReal Pointwise

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
/-- Uniformly bounded-radius enlarged boxes suffice for the maximal-packing
construction, even after a Haar-preserving automorphism of the small box.
The hypothesis on its image is the strict-width inclusion proved separately. -/
theorem exists_coneIdeal_tiling_radius (dynkin : NilpotentDynkinExpansionInput E G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (s₁ s₂ : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s₁ β →
      M.IsMaximizingConeIdealBasis C b₀ s₂ β → ∀ r : ℝ, 0 ≤ r →
      ∀ (μ : Measure G), μ.IsHaarMeasure →
      ∀ F : G ≃ₜ* G, MeasurePreserving F μ μ →
      F '' M.coneIdealBox C (Exp ∘ e) s₂ β r 1 ⊆
        M.coneIdealBox C (Exp ∘ e) s₁ β r 1 →
      μ (M.coneIdealBox C (Exp ∘ e) s₂ β r 1) ≠ 0 →
      ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
        (∀ i, anchor i ∈ M.coneIdealBox C (Exp ∘ e) s₁ β r 1) ∧
        (∀ i, MeasurableSet (tile i)) ∧
        Pairwise (fun i j => Disjoint (tile i) (tile j)) ∧
        (⋃ i, tile i) = M.coneIdealBox C (Exp ∘ e) s₁ β r 1 ∧
        (∀ i, tile i ⊆ anchor i • (F '' M.coneIdealBox C (Exp ∘ e) s₂ β r R)) ∧
        (n : ℝ≥0∞) * μ (M.coneIdealBox C (Exp ∘ e) s₂ β r 1) ≤
          μ (M.coneIdealBox C (Exp ∘ e) s₁ β r R) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨K, _hK, hprod⟩ := M.exists_coneIdealBox_product_bound C e Exp hExp dynkin b₀
  let R := max 1 (K * (1 + (2 : ℝ)) ^ M.coneIdealWordBound C *
    (1 + (1 : ℝ)) ^ M.coneIdealWordBound C)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmul (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
      (hβ : M.IsMaximizingConeIdealBasis C b₀ s β) (r : ℝ) (hr : 0 ≤ r)
      {a b : G} (ha : a ∈ M.coneIdealBox C (Exp ∘ e) s β r 1)
      (hb : b ∈ M.coneIdealBox C (Exp ∘ e) s β r 1) :
      a * b ∈ M.coneIdealBox C (Exp ∘ e) s β r R := by
    have hh := hprod s β hβ r hr 2 1 zero_le_one ![a, b] (by
      intro i
      fin_cases i
      · exact ha
      · exact hb)
    simp only [List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at hh
    obtain ⟨v, hv, hnorm⟩ := hh
    exact ⟨v, hv, hnorm.trans (le_max_right _ _)⟩
  refine ⟨R, hR, ?_⟩
  intro s₁ s₂ β hβ₁ hβ₂ r hr μ hμ F hF hsmall hpos
  let : μ.IsHaarMeasure := hμ
  have hcompact (s : Fin M.letterCount → ℝ) (R' : ℝ) (hR' : 0 ≤ R') :
      IsCompact (M.coneIdealBox C (Exp ∘ e) s β r R') :=
    isCompact_exponentialCoordinateBox e.toLinearEquiv Exp chart hchart
      (M.coneIdealBoxBasis C s β r) R' hR'
  apply finite_conjugate_tiling μ F hF
    (M.coneIdealBox C (Exp ∘ e) s₁ β r 1)
    (M.coneIdealBox C (Exp ∘ e) s₂ β r 1)
    (M.coneIdealBox C (Exp ∘ e) s₂ β r R)
    (M.coneIdealBox C (Exp ∘ e) s₁ β r R)
    (hcompact s₁ 1 zero_le_one).isClosed.measurableSet
    (hcompact s₂ 1 zero_le_one) (hcompact s₂ R hR.le) hpos
    (ne_of_lt (hcompact s₂ 1 zero_le_one).measure_lt_top)
    (ne_of_lt (hcompact s₁ R hR.le).measure_lt_top)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hmul s₁ β hβ₁ r hr ha (hsmall hb)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    apply hmul s₂ β hβ₂ r hr ha
    simpa only [inv_inv] using M.coneIdealBox_inv_mem C e Exp hExp s₂ β r 1
      (Set.mem_inv.mp hb)

end PolycyclicRecognition.CartanWordModel

end

end OAI
