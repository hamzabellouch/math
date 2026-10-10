import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootIntervalSlack
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRecurrenceBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSupports

namespace OAI

/-! # A fixed recurrence denominator for the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The compact support of every original interval law fits into one fixed
translated enlarged box. Its exact Haar-volume ratio is independent of scale. -/
theorem exists_interval_recurrence_denominator
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    {m : ℕ} (letters : Fin m → Fin M.letterCount) :
    ∃ D : ℝ, 1 ≤ D ∧
      let μ := MeasureTheory.Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm)
        MeasureTheory.volume
      ∀ᶠ r in atTop,
        let k₀ := F.ExpN (F.N.equiv (k r))
        let Q := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
        let Q' := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r D
        (∀ j : Fin m, ∀ x ∈ Q,
          ∀ u ∈ rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter q r R j.val,
            x * u ∈ Q') ∧
        μ Q' = ENNReal.ofReal (D ^ finrank ℝ (cartanRootIdeal H)) * μ Q := by
  have hnilN : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)
      (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier) M.bound = ⊥ := by
    rw [← LieIdeal.lowerCentralSeries_map_eq M.bound F.N.equiv.surjective, M.bound_zero]
    simp
  obtain ⟨aN, _, hprod⟩ := dynkinN F.ExpN F.isExpN M.bound hnilN 2
  have hm (x y : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier) :
      F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y := by
    simpa [List.ofFn_succ] using (hprod ![x, y]).symm
  have hslack := M.root_interval_slack_of_published_realization T F hunimod eW
    hExpG realize haarN b₀ E β q hβ hδ hc hhi hR hcost hgap hq aN hm ε hεpos hε k hk
  obtain ⟨D, hD, hdenom⟩ := M.exists_recurrence_box_enlargement T hunimod eW
    F.N.equiv F.ExpN F.isExpN haarN dynkinN b₀
  refine ⟨D, hD, ?_⟩
  filter_upwards [hslack, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  obtain ⟨hcontain, hvolume⟩ := hdenom E β hβ r hr0
  refine ⟨?_, hvolume _⟩
  intro j x hx u hu
  obtain ⟨t, ht, rfl⟩ := hu
  have ht' : |t| ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using ht
  apply hcontain _ _ ?_ x hx
  simpa only [rootIntervalSample_letter, smul_smul, Function.comp_apply] using hr (letters j) t ht'

end PolycyclicRecognition.CartanWordModel

end

end OAI
