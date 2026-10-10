import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFullCellAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborBoxAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborProfileAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSuffixRate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightRays
import Mathlib.Topology.Algebra.ConstMulAction

namespace OAI

/-! # Neighboring-sheet affinity directly from enlarged box membership -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Apply the proved uniform neighbor-label threshold to actual supported
profiles. The row is assembled from the original enlarged cells and the
published-input affinity theorem, including the raw-chart identities. -/
theorem cartan_neighbor_profiles_common_affine_of_threshold
    [IsTopologicalGroup F.N.carrier]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hconv : Convex ℝ E) (hint : (interior E).Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 < 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (fun q => (profile n q, profile n (q * step n)))) atTop (𝓝 ν))
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (pivot : Fin M.letterCount → H) (B : ℝ) (mode : Fin M.letterCount)
    (time : ℕ → ℝ)
    (htime : ∀ n, |time n| ≤ R n * Real.exp
      ((M.weight mode (pivot mode) + δ * B) * scale n))
    (hroot : ∀ n, F.inclusionN (step n) =
      Exp (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hthreshold : ∀ D : AffineNeighborRow T M F hunimod eW π b₀ E β X βD
      haarN chartN hchartN pivot c B δ S (Λ := Λ), D.label₁ = D.label₂) :
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior E →
          f.1.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  intro f hf
  obtain ⟨A₁, A₂, b₁, b₂, haff⟩ :=
    M.cartan_neighbor_profiles_affine_on_contracted_cell T F hunimod eW hExp realize
      haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath chartN hchartN
      b₀ hE hconv hint β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
      aN hmN aD hmD scale hscale hmono hscale1 R hR0 hR k₀ step hk₀ hstep
      rem hdim p x S hS profile hp hactual ν hν σ hσ f hf
  have hraw (n) (q : F.N.carrier)
      (hq : q ∈ (fun v => v * k₀ n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1) (z) :
      let b := WordBasisSelections.basis X (boundedBracketWords d) βD
      let br := exponentialRescaleBasis b
        (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale n))
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (Real.log (scale n)) (fun z => Exp (br.equivFun.symm z)) z ∧
      (profile n (q * step n)).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN (q * step n))
        (Real.log (scale n)) (fun z => Exp (br.equivFun.symm z)) z := by
    have htlog : max (Real.log (scale n)) 0 = Real.log (scale n) :=
      max_eq_left (Real.log_nonneg (hscale1 n))
    have hqstep : q * step n ∈ (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
      obtain ⟨v, hv, rfl⟩ := hq
      exact ⟨v, hv, rfl⟩
    constructor
    · simpa only [htlog, F.compatibleD] using hactual n q (Or.inl hq) z
    · simpa only [htlog, F.compatibleD] using hactual n (q * step n) (Or.inr hqstep) z
  let row : AffineNeighborRow T M F hunimod eW π b₀ E β X βD
      haarN chartN hchartN pivot c B δ S (Λ := Λ) :=
    { scale := scale
      grows := hscale
      pair := p
      center := x
      radius := R
      radius_nonneg := hR0
      radius_subexponential := hR
      base := k₀
      step := step
      basis := fun _ => β
      base_mem := hk₀
      step_mem := hstep
      mode := mode
      time := time
      time_bound := htime
      root_step := hroot
      profile := fun n q => (profile n q, profile n (q * step n))
      measurable_profile := fun n => (hp n).prodMk
        ((hp n).comp (continuous_id.mul continuous_const).measurable)
      actual := hraw
      law := ν
      converges := hν
      point := f
      supported := hf
      label₁ := A₁
      label₂ := A₂
      offset₁ := b₁
      offset₂ := b₂
      affine₁ := fun z hz => (haff z hz).1
      affine₂ := fun z hz => (haff z hz).2 }
  have heq : A₁ = A₂ := hthreshold row
  refine ⟨A₁, b₁, b₂, ?_⟩
  simpa only [heq] using haff

end PolycyclicRecognition.CartanWordModel

end

end OAI
