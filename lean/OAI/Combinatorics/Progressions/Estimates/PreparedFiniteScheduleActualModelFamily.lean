import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteScheduleActualModelFamily
    {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ]
    {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hbox : (integerBox N).Nonempty)
    (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Path → integerBox (Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S)) → integerBox N)
    {Stage : Type} {Branch : Stage → Type} [∀ k, Fintype (Branch k)]
    (u p cap sliceLog testLog budget E : Stage → ℝ)
    (hModel : ∀ k, PreparedFiniteScheduleModelsAtLaw B U b S N Pdetect μ poly hbox law hweight
      physical (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k))
    {Tests : Stage → Path → Type} [∀ k z, Nonempty (Tests k z)]
    {Ldetect : ∀ k z, Tests k z → Type} [∀ k z j, LieRing (Ldetect k z j)]
    [∀ k z j, LieAlgebra ℚ (Ldetect k z j)] {dims : ∀ k z, Tests k z → ℕ}
    [∀ k z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, T2Space (ℝ ⊗[ℚ] Ldetect k z j)]
    (Ddetect : ∀ k z j, RationalFilteredNilmanifold (Ldetect k z j) 0 (dims k z j))
    (Vdetect : ∀ k z j, (Ddetect k z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ k z, Tests k z → Finset (integerBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))))
    (cdetect : ∀ k z, Tests k z → LayerSamplerVariables G I n B → ℤ)
    (stepdetect : ∀ k z, Tests k z → ℕ)
    (Hdetect : ∀ k z, Tests k z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ k z j, 0 < stepdetect k z j)
    (hSlices : ∀ k z j, (slices k z j).image Subtype.val =
      commonStrideBox (cdetect k z j) (stepdetect k z j) (Hdetect k z j))
    (hDense : ∀ k z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) (sliceLog k)
      ((slices k z j).image Subtype.val))
    (hnum : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hcomplex : ∀ k z j, (Vdetect k z j).ComplexityLE
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k)))
    (hcap : ∀ k z j, ((Vdetect k z j).normBound : ℝ) ≤ 1)
    {Forecast : Stage → Type} [∀ k, Nonempty (Forecast k)]
    (Pnative massLog capLog Edata : Stage → ℝ)
    (data : ∀ k, Forecast k → ActualForecastData N poly (Pnative k) (massLog k) (capLog k) (Edata k))
    (hNative : ∀ k, 0 ≤ Pnative k)
    (hAccuracy : ∀ k, 2 * u k + 4 * p k + 12 ≤ Edata k)
    (hCap : ∀ k, Real.exp (capLog k) ≤ cap k)
    (hPrecision : ∀ k, actualForecastDataModelRequired (budget k) (Pnative k) (massLog k)
      (u k) (p k) ≤ E k)
    (input : ∀ k, Branch k → integerBox N → ℂ)
    (hinput : ∀ k branch v, ‖input k branch v‖ ≤ Real.exp (p k)) :
    let tests : ∀ k z, Tests k z → integerBox
        (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℂ :=
      fun k z j t => star ((Vdetect k z j).eval
        (commonStrideIndex (cdetect k z j) (stepdetect k z j) t.val))
    let commonBudget := fun k => max (budget k) (3 * Pnative k + 3)
    let Qmodel := fun k => max (commonBudget k) (2 * u k + 4 * p k + max 0 (massLog k) + 20)
    let native := fun k => twistedNativeSampleFunctions (1 : Fin nX → ℕ) 0 (commonBudget k)
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp (commonBudget k)) (Real.exp (commonBudget k))
        ⟨Real.exp (commonBudget k), Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : Stage → (integerBox N → ℂ) → ℝ := fun k =>
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical (slices k) (tests k)
    let selectedLocal : Stage → (integerBox N → ℂ) →
        (CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) → Prop :=
      fun k err errLocal => ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices k z j, err (physical z t) * tests k z j t
    ∃ models : ∀ k, Branch k → CenteredForecastModel (integerBox N),
      (∀ k branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
        (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
        (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
        (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models k branch)) ∧
      (∀ k branch, sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
        physical (slices k) (tests k) (models k branch).residual ≤ Real.exp (-u k)) := by
  classical
  intro tests commonBudget Qmodel native localSeminorm selectedLocal
  have hstage (k : Stage) :
      ∃ models : Branch k → CenteredForecastModel (integerBox N),
        ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
          (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
          (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
          (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
          (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models branch) := by
    exact preparedFiniteScheduleModelsAtLaw_actualData
      (B := B) (U := U) (b := b) (S := S)
      N Pdetect μ poly hbox law hweight physical
      (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k) (hModel k)
      (Ddetect k) (Vdetect k) (slices k) (cdetect k) (stepdetect k) (Hdetect k)
      (hstep k) (hSlices k) (hDense k) (hnum k) (hcomplex k) (hcap k)
      (data k) (hNative k) (hAccuracy k) (hCap k) (hPrecision k) (input k) (hinput k)
  choose models hmodels using hstage
  exact ⟨models, hmodels, fun k branch => (hmodels k branch).2.2.2.1⟩

end Erdos3.VectorPolynomial

end

end OAI
