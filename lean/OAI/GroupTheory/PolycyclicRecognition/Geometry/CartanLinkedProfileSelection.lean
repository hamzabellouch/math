import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedProfileMeasurable
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProductProbeSelection

namespace OAI

/-! # Select all actual linked prefixes from the original product law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

theorem select_actual_linked_profiles
    {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    (scale : ℕ → ℝ) (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ℕ → cartanRootIdeal H) (η : ℕ → ℝ)
    (D : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P
      (fun n _ => origin n) (fun n _ => base n) η)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (x : ℕ → G)
    (r : ℕ → ℝ)
    (bN : ℕ → Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : ℕ → Basis (Fin (finrank ℝ H)) ℝ H)
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (μ : ProbabilityMeasure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (ν : ∀ n, ProbabilityMeasure (Y n)) [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (carrying : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hcarrying : MeasurableSet carrying) (hfull : (μ : Measure _) carryingᶜ = 0)
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (q : Z → W) (A : W →ₗ[ℝ] W) (b : Bool → W)
    (f : C(Z, W) × C(Z, W)) (hf : f ∈ (limitLaw : Measure _).support)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    (hlim :
      let profile := fun n y =>
        ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
          (origin n)).restrict Z,
         (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
          (base n)).restrict Z)
      Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    (hconcentration : ∀ k j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure _).prod (ν n : Measure (Y n))
        {p | ε ≤ dist
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) p.1
            (D.vertex k n p.2 j)).restrict Z)
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) p.1
            (D.vertex k n p.2 0)).restrict Z)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (good n)) ∧
      ∀ᶠ n in atTop, sample n ∈ carrying ∧
        (∀ (s : Bool) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (if s then base n else origin n) z - (A (q z) + b s)‖ < ε n) ∧
        ∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (D.vertex k n y j) z - (A (q z) + b (k != 0))‖ < 2 * ε n := by
  let cp : ∀ k n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × Y n) →
      Fin ((P k).length + 1) → C(Z, W) := fun k n p j => (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n)
    (bN n) (bD n) p.1 (D.vertex k n p.2 j)).restrict Z
  let sp := fun n y =>
    ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
      (origin n)).restrict Z,
     (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
      (base n)).restrict Z)
  have hcp (k n j) : Measurable (fun p => cp k n p j) :=
    (ContinuousMap.continuous_restrict Z).measurable.comp
      (F.measurable_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) b₀ (bN n)
        (bD n) (D.vertex k n · j) (D.measurable k n j))
  have hsp (n) : Measurable (sp n) :=
    (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n)
      (bN n) (bD n) (origin n) Z).prodMk
    (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n)
      (bN n) (bD n) (base n) Z)
  have hs₂ (n p) : cp 2 n p 0 = cp 1 n p (Fin.last (P 1).length) := by
    simp only [cp, D.third_start]
  obtain ⟨ε, sample, good, hε0, hε, hg, he⟩ :=
    exists_supported_three_product_affine_probe_sequence μ ν carrying hcarrying hfull
      sp hsp limitLaw hlim hf q A b haffine (cp 0) (cp 1) (cp 2)
      (hcp 0) (hcp 1) (hcp 2) hs₂
      (by simpa only [cp, sp, D.first_start] using hconcentration 0)
      (by simpa only [cp, sp, D.second_start] using hconcentration 1) (hconcentration 2)
  refine ⟨ε, sample, good, hε0, hε, hg, he.mono ?_⟩
  intro n hn
  refine ⟨hn.1, ?_, ?_⟩
  · intro s z
    cases s
    · simpa [sp] using hn.2.1 false z
    · simpa [sp] using hn.2.1 true z
  · intro y hy k j z
    fin_cases k
    · exact hn.2.2.1 y hy j z
    · exact hn.2.2.2.1 y hy j z
    · exact hn.2.2.2.2 y hy j z

end PolycyclicRecognition.CartanWordModel

end

end OAI
