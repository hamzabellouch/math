import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDiagonalNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteModeProfileChains

namespace OAI

/-! # Eventual agreement for shrinking-enlargement families -/

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

/-- Along any shrinking-enlargement family, supported neighboring affine
labels agree eventually. Compactness and the finite symmetry group supply
the converging constant-label subsequence required by the geometric diagonal. -/
theorem eventually_root_neighbor_labels_eq
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
    (mode : ℕ → Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : ℕ → templateSymmetryGroup (M.supportIn T hunimod eW))
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
    (scale : ℕ → ℕ → ℝ) (hscale : ∀ j, Tendsto (scale j) atTop atTop)
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
    (p : ℕ → ℕ → NormalizedPair G Λ) (x : ℕ → ℕ → G)
    (R : ℕ → ℕ → ℝ) (k₀ k : ℕ → ℕ → F.N.carrier) (η δ : ℕ → ℝ)
    (t : ℕ → ℕ → ℝ) (β : ℕ → ℕ → M.Bases)
    (hR0 : ∀ j n, 0 ≤ R j n)
    (hR : ∀ j, HasSubexponentialUpperBoundSeq (scale j) (R j))
    (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
    (hk₀ : ∀ j n, k₀ j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hk : ∀ j n, k j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ j n, |t j n| ≤ R j n * Real.exp ((M.weight (mode j) (pivot (mode j)) + η j) * scale j n))
    (hstep : ∀ j n, F.inclusionN (k j n) =
      ExpG (t j n • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (profile : ℕ → ℕ → F.N.carrier → S × S) (hp : ∀ j n, Measurable (profile j n))
    (hactual : ∀ j n q, q ∈ (fun y => y * k₀ j n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1 → ∀ z,
      let b := WordBasisSelections.basis X (boundedBracketWords d) βD
      let br := exponentialRescaleBasis b
        (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale j n))
      (profile j n q).1.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN q)
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
      (profile j n q).2.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN (q * k j n))
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z)
    (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (scale j n) (k₀ j n)) (profile j n)) atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support) (b₁ b₂ : ℕ → W) (shrink : ℝ)
    (haff₁ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).1.val z = (A₁ j).val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ j)
    (haff₂ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).2.val z = (A₂ j).val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ j) : (∀ᶠ j in atTop, A₁ j = A₂ j) := by
  classical
  by_contra h
  have hbad : ∃ᶠ j in atTop, A₁ j ≠ A₂ j := not_eventually.mp h
  obtain ⟨v, hv, hvbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨ab, w, hw, hab⟩ := exists_constant_mode_subsequence (fun j => (mode (v j), A₁ (v j), A₂ (v j)))
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨g, u, hu, hfg⟩ := CompactSpace.tendsto_subseq (fun j => f (v (w j)))
  let a := v ∘ w ∘ u
  have ha : StrictMono a := hv.comp (hw.comp hu)
  have hlabels j : (mode (a j), A₁ (a j), A₂ (a j)) = ab := hab (u j)
  have hmode j : mode (a j) = ab.1 := congrArg Prod.fst (hlabels j)
  have hlabel₁ j : A₁ (a j) = ab.2.1 := congrArg (fun q => q.2.1) (hlabels j)
  have hlabel₂ j : A₂ (a j) = ab.2.2 := congrArg (fun q => q.2.2) (hlabels j)
  have hne : ab.2.1 ≠ ab.2.2 := by
    intro heq
    apply hvbad (w (u 0))
    change A₁ (a 0) = A₂ (a 0)
    rw [hlabel₁ 0, hlabel₂ 0]
    exact heq
  apply hne
  apply M.diagonal_root_neighbor_labels_eq T F hunimod eW hExpG hinjG realize rem π hLip hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    cell hcell hconv hint (pivot ab.1) (hpivot ab.1) ab.1 α c hpoly (hactive ab.1)
    ab.2.1 ab.2.2 βcell hβcell
    X hDnil bD₀ βD hβD aN hm hdim (fun j => scale (a j)) (fun j => hscale (a j))
    νD hpath hΛ (fun j => p (a j)) (fun j => x (a j)) (fun j => R (a j))
    (fun j => k₀ (a j)) (fun j => k (a j)) (η ∘ a) (δ ∘ a)
    (fun j => t (a j)) (fun j => β (a j)) (fun j => hR0 (a j)) (fun j => hR (a j))
    (fun j => hδ0 (a j)) (hδ.comp ha.tendsto_atTop)
    (fun j => hk₀ (a j)) (fun j => hk (a j)) (hη.comp ha.tendsto_atTop)
    (by intro j n; simpa only [hmode j, Function.comp_apply] using ht (a j) n)
    (by intro j n; simpa only [hmode j, Function.comp_apply] using hstep (a j) n) S (fun j => profile (a j))
    (fun j => hp (a j)) (fun j => hactual (a j)) (ν ∘ a) (fun j => hν (a j)) (f ∘ a) g
    (fun j => hf (a j)) hfg (b₁ ∘ a) (b₂ ∘ a) shrink
  · intro j z hz
    simpa only [hlabel₁ j, Function.comp_apply] using haff₁ (a j) z hz
  · intro j z hz
    simpa only [hlabel₂ j, Function.comp_apply] using haff₂ (a j) z hz

end PolycyclicRecognition.CartanWordModel

end

end OAI
