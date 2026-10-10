import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProfilePacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceRecurrentWordImage

namespace OAI

/-! # From recurrent good sheets to the actual Cartan support inequality -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

include hπExp dynkinD haarN haarD in
theorem templateSupport_le_of_recurrent_good_profiles_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (source E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (w₀ : W)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (x : ℕ → G) (d₀ : ℕ → F.D.carrier)
    (A Q : ℕ → Set F.N.carrier) (K₀ R₀ : ℕ → ℕ → Set F.N.carrier)
    (D : ℕ → ℕ → ℝ)
    (μ : Measure F.N.carrier) [SFinite μ] [μ.IsMulRightInvariant]
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
    {m c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
    (s : Fin M.letterCount → ℝ) (letters : Fin m → Fin M.letterCount)
    (sample : ℕ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (scale r * s (letters j)) • M.letter (letters j)))))
    (S : Set (((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)))
    (hS : IsCompact S)
    (hb : ∀ r, (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * s i) • M.letter i)) ∈ S)
    (b₁ : ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hb₁ : b₁ ∈ S)
    (hlim : Tendsto (fun r => (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 b₁))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
    (honto : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters b₁) t₀))
    (σ : ℕ → ℕ → Measure F.N.carrier) [∀ r j, IsProbabilityMeasure (σ r j)]
    (hlaw : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK₀ : ∀ r j, ∀ᵐ u ∂σ r j, u ∈ K₀ r j)
    (hRfin : ∀ r j, μ (R₀ r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R₀ r j)).toReal)
    (hQR : ∀ r j, ∀ u ∈ Q r, ∀ v ∈ K₀ r j, u * v ∈ R₀ r j)
    (hD : ∀ r j, 0 < D r j)
    (hdenom : ∀ r j, (μ (R₀ r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale
      (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ r, ∀ i : Fin m, Continuous (fun t => F.inclusionN (sample r i.val t)))
    (hf₀ : ∀ r, ∀ i : Fin m, F.inclusionN (sample r i.val 0) = 1)
    (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    {speed switchError : ℝ} (hspeed : 0 ≤ speed) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ E, ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hstart : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • w₀‖ ≤ scale r * (ζ r + η))
    (hleg : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m,
      ∀ t : unitInterval, ∃ w ∈ E,
        ‖(π ((f r).val.1 ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r * t)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hmetric : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → u * sample r i.val b ∈ A r →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => F.inclusionN (sample r i.val t)) (hf r i) (hf₀ r i)
        (x r * F.inclusionN u) (F.inclusionD (d₀ r)) (scale r) b)
        (speed * scale r) (speed * (1 + Real.log (2 + scale r))))
    (hswitch : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * F.inclusionN u) * F.inclusionN (sample r i.val ((t : ℝ) * b)) *
          (F.inclusionD (d₀ r) * d i (scale r)))
        ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r)) ≤
          switchError * (1 + Real.log (2 + scale r)))
 :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport E := by
  let cN := chartN.symm.trans
    (finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)).equivFun.toContinuousLinearEquiv.toHomeomorph
  let : SecondCountableTopology F.N.carrier := cN.secondCountableTopology
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨n₀, C, hn₀, hC, hvol, haccessible⟩ := recurrent_differenceWord_image_sequence
    scale hscale rem hdim aN letters S hS _ hb b₁ hb₁ hlim ρ hρ t₀ ht₀ honto
    μ sample σ hlaw Q A K₀ R₀ D hQfin hQpos hK₀ hRfin hRpos hQR hD hdenom
    hA hAQ hApos hAlower hDupper
  apply M.templateSupport_le_of_good_profile_paths_sequence T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD scale hscale
    b₀ source E hE hne w₀ β hβ C hC hvol x d₀ n₀ A hn₀ f hΛ hφ hpath hLip
    aN hm s letters sample hsub hsample d hd hd₀ hf hf₀ center ζ hζ
    hspeed hswitchError hbase _ hleg hmetric hswitch haccessible
  intro η hη
  filter_upwards [hstart η hη] with r hr
  exact hr (n₀ r) (hn₀ r)

end PolycyclicRecognition.CartanWordModel

end

end OAI
