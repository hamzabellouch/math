import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAccessibleComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SublinearAccessiblePaths

namespace OAI

/-! # Packing comparison from the actual successful good-sheet paths -/

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
/-- The good-sheet leg estimates and short root switches supply the full
controlled-path premise of the Cartan volume comparison. -/
theorem templateSupport_le_of_good_profile_paths
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (source E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (w₀ : W)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (C : ℝ → Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hC : ∀ r, IsCompact (C r))
    (hvol : HasSubexponentialLowerBound (fun r => (volume (C r)).toReal))
    (x : ℝ → G) (d₀ : ℝ → F.D.carrier) (n₀ : ℝ → F.N.carrier)
    (A : ℝ → Set F.N.carrier) (hn₀ : ∀ r, n₀ r ∈ A r)
    (f : ℝ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
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
    (sample : ℝ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (r * s (letters j)) • M.letter (letters j)))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ r, ∀ i : Fin m, Continuous (fun t => F.inclusionN (sample r i.val t)))
    (hf₀ : ∀ r, ∀ i : Fin m, F.inclusionN (sample r i.val 0) = 1)
    (center : ℝ → W) (ζ : ℝ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    {speed switchError ρ : ℝ} (hspeed : 0 ≤ speed) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ E, ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - r • w‖ ≤ r * (ζ r + η))
    (hstart : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop,
      ‖(π ((f r).val.1 (x r * F.inclusionN (n₀ r) * F.inclusionD (d₀ r)))).toAdd -
        center r - r • w₀‖ ≤ r * (ζ r + η))
    (hleg : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m,
      ∀ t : unitInterval, ∃ w ∈ E,
        ‖(π ((f r).val.1 ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (r * t)))).toAdd -
          center r - r • w‖ ≤ r * (ζ r + η))
    (hmetric : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → u * sample r i.val b ∈ A r →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => F.inclusionN (sample r i.val t)) (hf r i) (hf₀ r i)
        (x r * F.inclusionN u) (F.inclusionD (d₀ r)) r b)
        (speed * r) (speed * (1 + Real.log (2 + r))))
    (hswitch : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * F.inclusionN u) * F.inclusionN (sample r i.val ((t : ℝ) * b)) *
          (F.inclusionD (d₀ r) * d i r))
        ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i r) ≤
          switchError * (1 + Real.log (2 + r)))
    (haccessible : ∀ᶠ r in atTop, ∀ y ∈ C r,
      ∃ t ∈ Metric.closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A r) 0 m (n₀ r) (sampledSwitchParameters (sample r) m t) ∧
      differenceAmplitudeWordEndpoint aN letters
        (basisBracket (M.boxBasis T hunimod eW source β r),
          fun i => (M.boxBasis T hunimod eW source β r).equivFun
            (Real.exp (r * s i) • M.letter i)) t = y) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport E := by
  let J := fun r g => (π ((f r).val.1 g)).toAdd
  have hJ (r : ℝ) : LipschitzWith (K * Λ) (J r) := hLip.comp (f r).property.1.1
  have hpaths := sublinear_accessible_word_paths
    (M.boxBasis T hunimod eW source β) (F.ExpN ∘ F.N.equiv)
    (by simp [F.isExpN.map_zero]) aN (model_binary_dynkin F.N.equiv F.ExpN aN hm)
    M.letter s letters F.inclusionN F.closedN.injective x (fun r => F.inclusionD (d₀ r))
    A n₀ hn₀ sample hsub hsample d hd hd₀ hf hf₀ J hJ center w₀ E ζ hζ
    hspeed hswitchError hbase hstart hleg hmetric hswitch C haccessible
  let L := speed * 2 ^ m + switchError
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have htranslate := (M.supportIn T hunimod eW).templateSupport_translate hE hne (-w₀)
  rw [← htranslate]
  simp only [← sub_eq_add_neg]
  apply M.accessible_templateSupport_le T F hunimod eW π hπExp chartN hchartN chartD hchartD
    dynkinN dynkinD haarN haarD b₀ source ((fun z => z - w₀) '' E)
    (hE.image (continuous_id.sub continuous_const)) (hne.image _) β hβ C hC hvol
    (fun r => x r * F.inclusionN (n₀ r)) d₀
    (fun r => x r * F.inclusionN (n₀ r) * F.inclusionD (d₀ r)) f hΛ hφ hpath
    K.coe_nonneg hL
    (fun g h => by simpa only [dist_eq_norm] using hLip.dist_le_mul g h)
  intro η hη
  filter_upwards [hpaths η hη, eventually_ge_atTop (0 : ℝ)] with r hr hr0 y hy
  obtain ⟨γ, hγ, hh⟩ := hr y hy
  have hend :
      (x r * F.inclusionN (n₀ r)) * F.inclusionN (F.ExpN (F.N.equiv
        ((M.boxBasis T hunimod eW source β r).equivFun.symm y))) * F.inclusionD (d₀ r) =
      x r * F.inclusionN (n₀ r * F.ExpN (F.N.equiv
        ((M.boxBasis T hunimod eW source β r).equivFun.symm y))) * F.inclusionD (d₀ r) := by
    simp only [map_mul, mul_assoc]
  refine ⟨γ.cast rfl hend, ?_, ?_⟩
  · apply hγ.mono
    · apply mul_le_mul_of_nonneg_right _ hr0
      exact le_add_of_nonneg_right hswitchError
    · apply mul_le_mul_of_nonneg_right _ (by
        have := Real.log_nonneg (show 1 ≤ 2 + r by linarith)
        linarith)
      exact le_add_of_nonneg_right hswitchError
  · intro t
    obtain ⟨w, hw, hb⟩ := hh t
    refine ⟨w, hw, hb.trans ?_⟩
    simp only [NNReal.coe_mul]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (by
      have := Real.log_nonneg (show 1 ≤ 2 + r by linarith)
      linarith)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity : 0 ≤ speed * 2 ^ m))
      (mul_nonneg K.coe_nonneg Λ.coe_nonneg)

end PolycyclicRecognition.CartanWordModel

end

end OAI
