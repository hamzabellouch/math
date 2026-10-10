import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanEventualNeighborLabels

namespace OAI

/-! # A uniform positive threshold for affine neighboring labels -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I] {J : Type*} [Fintype J]

/-- One affine supported pair together with its original sampling data.
The fields record the actual maps, cells, root step and weak law; no
neighbor-label conclusion is included. -/
structure AffineNeighborRow
    (π : G →* Multiplicative W)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (cell : Set W) (βcell : M.Bases)
    (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    {Λ : ℝ≥0} where
  scale : ℕ → ℝ
  grows : Tendsto scale atTop atTop
  pair : ℕ → NormalizedPair G Λ
  center : ℕ → G
  radius : ℕ → ℝ
  radius_nonneg : ∀ n, 0 ≤ radius n
  radius_subexponential : HasSubexponentialUpperBoundSeq scale radius
  base : ℕ → F.N.carrier
  step : ℕ → F.N.carrier
  basis : ℕ → M.Bases
  base_mem : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) (basis n) (scale n) (radius n)
  step_mem : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) (basis n) (scale n) (radius n)
  mode : Fin M.letterCount
  time : ℕ → ℝ
  time_bound : ∀ n, |time n| ≤ radius n * Real.exp
    ((M.weight mode (pivot mode) + δ * B) * scale n)
  root_step : ∀ n, F.inclusionN (step n) =
    ExpG (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  profile : ℕ → F.N.carrier → S × S
  measurable_profile : ∀ n, Measurable (profile n)
  actual : ∀ n q, q ∈ (fun y => y * base n) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1 → ∀ z,
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let br := exponentialRescaleBasis b
      (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale n))
    (profile n q).1.val z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (Real.log (scale n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
    (profile n q).2.val z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN (q * step n))
      (Real.log (scale n)) (fun z => ExpG (br.equivFun.symm z)) z
  law : ProbabilityMeasure (S × S)
  converges : Tendsto (fun n => ProbabilityMeasure.map
    (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
      cell βcell (scale n) (base n)) (profile n)) atTop (𝓝 law)
  point : S × S
  supported : point ∈ (law : Measure (S × S)).support
  label₁ : templateSymmetryGroup (M.supportIn T hunimod eW)
  label₂ : templateSymmetryGroup (M.supportIn T hunimod eW)
  offset₁ : W
  offset₂ : W
  affine₁ : ∀ z, eW (heightProjection T.character
    ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ) • w) '' interior cell →
    point.1.val z = label₁.val (eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) + offset₁
  affine₂ : ∀ z, eW (heightProjection T.character
    ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ) • w) '' interior cell →
    point.2.val z = label₂.val (eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) + offset₂

/-- The shrinking-family contradiction gives a positive enlargement
threshold uniform over all admissible sampling rows in the compact profile
family. The reflection comparison uses the precisely stated published inputs. -/
theorem exists_uniform_neighbor_label_threshold
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (cell : Set W) (hcell : IsCompact cell) (hconv : Convex ℝ cell)
    (hint : (interior cell).Nonempty)
    (pivot : Fin M.letterCount → H)
    (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ cell)
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
    (shrink B : ℝ)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)] :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S (Λ := Λ), D.label₁ = D.label₂ := by
  classical
  by_contra hn
  push Not at hn
  have hbad (j : ℕ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / ((j : ℝ) + 1) ∧
      ∃ D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S (Λ := Λ), D.label₁ ≠ D.label₂ :=
    hn (1 / ((j : ℝ) + 1)) (by positivity)
  choose δ hδpos hδle D hne using hbad
  have hδ : Tendsto δ atTop (𝓝 0) := squeeze_zero
    (fun j => (hδpos j).le) hδle tendsto_one_div_add_atTop_nhds_zero_nat
  have he := M.eventually_root_neighbor_labels_eq T F hunimod eW hExpG hinjG realize rem π hLip
    hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    cell hcell hconv hint pivot hpivot (fun j => (D j).mode) α c hpoly hactive
    (fun j => (D j).label₁) (fun j => (D j).label₂) βcell hβcell X hDnil bD₀ βD hβD
    aN hm hdim (fun j => (D j).scale) (fun j => (D j).grows) νD hpath hΛ
    (fun j => (D j).pair) (fun j => (D j).center) (fun j => (D j).radius)
    (fun j => (D j).base) (fun j => (D j).step) (fun j => δ j * B) δ
    (fun j => (D j).time) (fun j => (D j).basis)
    (fun j => (D j).radius_nonneg) (fun j => (D j).radius_subexponential)
    (fun j => (hδpos j).le) hδ (fun j => (D j).base_mem) (fun j => (D j).step_mem)
    (by simpa only [zero_mul] using hδ.mul_const B)
    (fun j => (D j).time_bound) (fun j => (D j).root_step) S hS
    (fun j => (D j).profile) (fun j => (D j).measurable_profile)
    (fun j => (D j).actual) (fun j => (D j).law) (fun j => (D j).converges)
    (fun j => (D j).point) (fun j => (D j).supported)
    (fun j => (D j).offset₁) (fun j => (D j).offset₂) shrink
    (fun j => (D j).affine₁) (fun j => (D j).affine₂)
  obtain ⟨j, hj⟩ := he.exists
  exact hne j hj

end PolycyclicRecognition.CartanWordModel

end

end OAI
