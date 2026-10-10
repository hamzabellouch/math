import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRecurrentProfilePacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceRecurrentWordImage
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntervalVisits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SegmentProfileLegs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # From recurrent good sheets to the actual Cartan support inequality -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal Topology

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
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

include hπExp dynkinN dynkinD haarN haarD in
/-- Whole good segment legs, the actual pivot visits and recurrent sheet volume
imply the support inequality. No separate path or switch estimate is assumed. -/
theorem templateSupport_le_of_recurrent_segment_cells_sequence
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (X : I → H) (SD : Finset (FreeMagma I)) (βD : WordBasisSelections X SD)
    (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (source : Set W)
    (hsource : source = segment ℝ
      (eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      ((eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) +
        T₀ • eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (x : ℕ → G)
    (A Q : ℕ → Set F.N.carrier) (K₀ R₀ : ℕ → ℕ → Set F.N.carrier)
    (D : ℕ → ℕ → ℝ)
    (μ : Measure F.N.carrier) [SFinite μ] [μ.IsMulRightInvariant]
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
    {m c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
    (letters : Fin m → Fin M.letterCount)
    (sample : ℕ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source (letters j)) • M.letter (letters j)))))
    (S : Set (((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)))
    (hS : IsCompact S)
    (hb : ∀ r, (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i)) ∈ S)
    (b₁ : ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hb₁ : b₁ ∈ S)
    (hlim : Tendsto (fun r => (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i))) atTop (𝓝 b₁))
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
    (g : ℝ → W) (hg : Continuous g)
    (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    (hgood : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ t ∈ Icc 0 T₀,
      ‖(π ((f r).val.1 ((x r * F.inclusionN u *
        F.inclusionD (F.ExpD (F.D.equiv (wordChartPivot X SD βD (scale r) z)))) *
          F.inclusionD (F.ExpD (F.D.equiv ((scale r * t) • v)))))).toAdd -
        center r - scale r • g t‖ ≤ scale r * (ζ r + η)) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport (g '' Icc 0 T₀) := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let P := M.supportIn T hunimod eW
  let θ := P.segmentSupportTime (eW (heightProjection T.character v)) T₀
  let d : Fin m → ℝ → G := fun i t => Exp (t • (θ (letters i) • v : H))
  let d₀ : ℕ → F.D.carrier := fun n =>
    F.ExpD (F.D.equiv (wordChartPivot X SD βD (scale n) z))
  have hd (i : Fin m) : Continuous (d i) :=
    continuous_exp_line_of_published_realization T Exp hExp realize (θ (letters i) • v)
  have hd₀ (i : Fin m) : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hsampleG (r : ℕ) (j : Fin m) (t : ℝ) :
      F.inclusionN (sample r j.val t) =
        Exp ((t * Real.exp (scale r * P.weightSupport source (letters j))) •
          (M.letter (letters j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [hsample, F.compatibleN]
    simp only [SetLike.val_smul, smul_smul, P]
  have hf (r : ℕ) (j : Fin m) : Continuous (fun t => F.inclusionN (sample r j.val t)) := by
    have he := funext (hsampleG r j)
    rw [he]
    exact (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter (letters j))).comp
      (continuous_id.mul_const _)
  have hf₀ (r : ℕ) (j : Fin m) : F.inclusionN (sample r j.val 0) = 1 := by
    simp [hsampleG, hExp.map_zero]
  have hvisit := M.exists_segment_sampled_visit_bound T F hExp realize haarD dynkinD
    hunimod eW π hπExp X SD βD z v hT₀.le (zero_le_one.trans hρ)
  dsimp only at hvisit
  rw [← hsource] at hvisit
  rcases hvisit with ⟨C, hC, hbound⟩
  have hmetrics : ∀ r u (i : Fin m) b, |b| ≤ 2 * ρ →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => F.inclusionN (sample r i.val t)) (hf r i) (hf₀ r i)
        (x r * F.inclusionN u) (F.inclusionD (d₀ r)) (scale r) b)
        (C * scale r) (C * (1 + Real.log (2 + scale r))) := by
    intro r u i b hb
    have hh := (hbound (scale r) (hscale1 r) (x r * F.inclusionN u) (letters i) b hb).1
    intro t t'
    have he (s : unitInterval) := M.supportVisitPath_apply_eq_sampled T hExp realize
      (θ (letters i) • v) (letters i) (x r * F.inclusionN u) (F.inclusionD (d₀ r))
      (wordChartPivot X SD βD (scale r) z) (scale r) (P.weightSupport source (letters i)) b
      _ (hf r i) (hf₀ r i) (hsampleG r i) (hd i) (hd₀ i) (F.compatibleD _) s
    rw [he, he]
    exact hh t t'
  have hswitches : ∀ r u (i : Fin m) b, |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * F.inclusionN u) * F.inclusionN (sample r i.val ((t : ℝ) * b)) *
          (F.inclusionD (d₀ r) * d i (scale r)))
        ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r)) ≤
          C * (1 + Real.log (2 + scale r)) := by
    intro r u i b hb t
    have hh := (hbound (scale r) (hscale1 r) (x r * F.inclusionN u) (letters i) b hb).2
      t t.property 0 ⟨le_rfl, zero_le_one⟩
    simp only [zero_mul, zero_smul, hExp.map_zero, mul_one] at hh
    simp only [hsampleG, d₀, F.compatibleD, d, P, θ, SetLike.val_smul]
    have hle : C * Real.log (2 + scale r) ≤ C * (1 + Real.log (2 + scale r)) := by nlinarith
    simpa only [mul_assoc, SetLike.val_smul] using hh.trans hle
  have hgood' (η : ℝ) (hη : 0 < η) : ∀ᶠ r in atTop,
      (∀ u ∈ A r, ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • g 0‖ ≤ scale r * (ζ r + η)) ∧
      ∀ u ∈ A r, ∀ i : Fin m, ∀ t : unitInterval, ∃ w ∈ g '' Icc 0 T₀,
        ‖(π ((f r).val.1 ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r * t)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η) := by
    filter_upwards [hgood η hη] with r hr
    have hh := segment_profile_support_legs (F.ExpD ∘ F.D.equiv)
      (by simp [F.isExpD.map_zero]) F.inclusionN F.inclusionD
      (fun y => (π ((f r).val.1 y)).toAdd) (x r) (F.inclusionD (d₀ r)) (center r)
      (A r) (scale r) T₀ (scale r * (ζ r + η)) hT₀.le v (fun i : Fin m => θ (letters i))
      (fun i => P.segmentSupportTime_mem _ hT₀.le (letters i)) g hr
    simpa only [Function.comp_apply, F.compatibleD, d, d₀, SetLike.val_smul] using hh
  have hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ g '' Icc 0 T₀,
        ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η) := by
    intro η hη
    filter_upwards [hgood' η hη] with r hr u hu
    exact ⟨g 0, ⟨0, ⟨le_rfl, hT₀.le⟩, rfl⟩, hr.1 u hu⟩
  exact M.templateSupport_le_of_recurrent_good_profiles_sequence T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD scale hscale
    b₀ source (g '' Icc 0 T₀) (isCompact_Icc.image hg) ⟨g 0, 0, ⟨le_rfl, hT₀.le⟩, rfl⟩
    (g 0) β hβ x d₀ A Q K₀ R₀ D μ f hΛ
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExp realize _ _ dynkinN d)
    hpath hLip aN hm (P.weightSupport source) letters sample hsub hsample S hS hb b₁ hb₁ hlim
    rem hdim ρ hρ t₀ ht₀ honto σ hlaw hQfin hQpos hK₀ hRfin hRpos hQR hD hdenom hA hAQ hApos
    hAlower hDupper d hd hd₀ hf hf₀ center ζ hζ hC hC hbase
    (fun η hη => (hgood' η hη).mono fun _ h => h.1)
    (fun η hη => (hgood' η hη).mono fun _ h => h.2)
    (Eventually.of_forall fun r u _ i b hb _ => hmetrics r u i b hb)
    (Eventually.of_forall fun r u _ i b hb => hswitches r u i b hb)

end PolycyclicRecognition.CartanWordModel

end

end OAI
