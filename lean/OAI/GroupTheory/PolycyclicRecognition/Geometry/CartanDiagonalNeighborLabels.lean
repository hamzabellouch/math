import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGoodRootNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanShrinkingBoxEnvelope
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProbability
import OAI.GroupTheory.PolycyclicRecognition.Analysis.DiagonalAffineCellProfiles
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequenceVanishingRate
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ShrinkingProfileDomains

namespace OAI

/-! # One geometric diagonal for shrinking neighboring sheets -/

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

/-- Supported affine labels along shrinking enlargements agree. The proof
selects the actual Haar cells, their subexponential mass and all geometric
bounds on one diagonal before applying the reflection comparison. -/
theorem diagonal_root_neighbor_labels_eq
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
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ cell)
    (i : Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ j, α j (eW (heightProjection T.character pivot)) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW))
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
    (ht : ∀ j n, |t j n| ≤ R j n * Real.exp ((M.weight i pivot + η j) * scale j n))
    (hstep : ∀ j n, F.inclusionN (k j n) =
      ExpG (t j n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
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
    (f : ℕ → S × S) (g : S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support)
    (hfg : Tendsto f atTop (𝓝 g)) (b₁ b₂ : ℕ → W) (shrink : ℝ)
    (haff₁ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).1.val z = A₁.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ j)
    (haff₂ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).2.val z = A₂.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ j) : A₁ = A₂ := by
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let q := height.comp b.equivFun.symm.toLinearMap
  have hq : Function.Surjective q := by
    intro w
    refine ⟨b.equivFun (cartanHeightSection T H (eW.symm w)), ?_⟩
    change eW (heightProjection T.character
      (b.equivFun.symm (b.equivFun (cartanHeightSection T H (eW.symm w))) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
    rw [LinearEquiv.symm_apply_apply, cartanHeightSection_height, eW.apply_symm_apply]
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let Q := fun j n => (fun y => y * k₀ j n) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1
  have hQ j n : MeasurableSet (Q j n) ∧ μ (Q j n) ≠ 0 ∧ μ (Q j n) ≠ ∞ :=
    M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀
      cell βcell (scale j n) (k₀ j n)
  let P := fun j n => 1 ≤ scale j n ∧
    R j n ≤ Real.exp ((1 / ((j : ℝ) + 1)) * scale j n)
  have hP j : ∀ᶠ n in atTop, P j n :=
    ((hscale j).eventually (eventually_ge_atTop (1 : ℝ))).and
      (hR j (1 / ((j : ℝ) + 1)) (by positivity))
  obtain ⟨c₁, c₂, u, n, Good, hu, hn, hs, hGood, hGoodQ, hGoodpos, hmass, happ⟩ :=
    exists_diagonal_affine_cell_profiles q q.continuous_of_finiteDimensional hq
      cell hconv hcell.isClosed hint S
      (fun j => Metric.closedBall 0 ((j : ℝ) + 1)) (fun _ => isCompact_closedBall _ _)
      (fun C hC => compact_eventually_subset_coordinate_balls 0 C hC)
      scale hscale μ Q (fun j n => (hQ j n).1) (fun j n => (hQ j n).2.1)
      (fun j n => (hQ j n).2.2) profile hp ν hν f g hf hfg
      A₁.val.toLinearMap.toContinuousLinearMap A₂.val.toLinearMap.toContinuousLinearMap
      b₁ b₂
      (eventually_affine_of_shrinking_interiors q cell (fun j z => (f j).1.val z)
        A₁.val b₁ hδ shrink haff₁)
      (eventually_affine_of_shrinking_interiors q cell (fun j z => (f j).2.val z)
        A₂.val b₂ hδ shrink haff₂) P hP
  let r := fun j => scale (u j) (n j)
  let R' := fun j => R (u j) (n j)
  have hr1 j : 1 ≤ r j := (hn j).1
  have hr0 j : 0 ≤ r j := zero_le_one.trans (hr1 j)
  have hR' : HasSubexponentialUpperBoundSeq r R' := by
    intro ε hε
    filter_upwards [sequence_subexponential_exp_of_vanishing_rate hr0
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hu) ε hε] with j hj
    exact (hn j).2.trans hj
  obtain ⟨V, hV0, hV, hbox⟩ := M.exists_homothetic_box_envelope_sequence T hunimod eW
    (F.ExpN ∘ F.N.equiv) b₀ hcell (hint.mono interior_subset) βcell hβcell
    r (δ ∘ u) R' hs hr0 (fun j => hδ0 (u j)) (hδ.comp hu)
    (fun j => hR0 (u j) (n j)) hR'
  let R'' := fun j => V j + R' j
  have hR''0 j : 0 ≤ R'' j := add_nonneg (hV0 j) (hR0 (u j) (n j))
  have hR'' : HasSubexponentialUpperBoundSeq r R'' := hV.add hR' hs
  have hbox' j γ :
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ (u j)) • w) '' cell) γ (r j) (R' j) ⊆
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (r j) (R'' j) := by
    intro v hv
    obtain ⟨a, ha, he⟩ := hbox j γ hv
    exact ⟨a, ha, he.trans (le_add_of_nonneg_right (hR0 (u j) (n j)))⟩
  apply M.good_root_neighbor_labels_eq T F hunimod eW hExpG hinjG realize rem π hLip hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    cell hcell pivot hpivot i α c hpoly hactive A₁ A₂ c₁ c₂ βcell hβcell X hDnil bD₀ βD hβD
    aN hm hdim r hs hr1 νD hpath hΛ
    (fun j => p (u j) (n j)) (fun j => x (u j) (n j)) R''
    (fun j => k₀ (u j) (n j)) (fun j => k (u j) (n j)) (η ∘ u)
    (fun j => t (u j) (n j)) hR''0 hR''
    (fun j => hbox' j _ (hk₀ (u j) (n j))) (fun j => hbox' j _ (hk (u j) (n j)))
    (hη.comp hu) (fun j => (ht (u j) (n j)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hV0 j)) (Real.exp_pos _).le))
    (fun j => hstep (u j) (n j))
  intro C hC
  refine ⟨Good, fun j => 2 / ((j : ℝ) + 1), hGood, hGoodQ, hGoodpos, hmass,
    fun _ => by positivity, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
  · filter_upwards [happ C hC] with j hj
    intro a ha z hz hze
    have hraw := hactual (u j) (n j) a (hGoodQ j ha) z
    simpa only [hraw.1, hraw.2, r, q, height, b, LinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe] using hj a ha z hz hze

end PolycyclicRecognition.CartanWordModel

end

end OAI
