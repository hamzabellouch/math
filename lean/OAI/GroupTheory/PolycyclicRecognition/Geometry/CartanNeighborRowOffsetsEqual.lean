import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowProfile
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowReverse
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateOffsetCones

namespace OAI

/-! # The finite polar tests determine both affine offsets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

/-- Apply each fixed quotient trace to the original row and to its actual
reversal. The ray and two-ray tests then force the offsets to agree. -/
theorem AffineNeighborRow.offsets_eq_of_cone_bounds
    (hExp : IsGroupExponential ExpG)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n)
    (hlabels : D.label₂ = D.label₁)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (coeff : rootOffsetConeIndex (M.supportIn T hunimod eW) D.mode →
      Fin M.letterCount → ℕ)
    (hout : ∀ s j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
      transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz D.mode s)
        D.label₁.val → coeff s j = 0)
    (hin : ∀ s j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
      transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz D.mode s)
        D.label₁.val → 0 < coeff s j)
    (hbound : ∀ s,
      ∀ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S (Λ := Λ),
      R.mode = D.mode → R.label₁ = D.label₁ → R.label₂ = D.label₁ →
        (∑ j, (coeff s j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (R.offset₂ - R.offset₁) ≤ 0) :
    D.offset₁ = D.offset₂ := by
  obtain ⟨R, _, hmode, hlabel₁, hlabel₂, hoffset₁, hoffset₂⟩ :=
    D.exists_reverse T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S hExp dynkinN hcell hne hβ hδ hs
  apply eq_of_rootOffsetCone_trace_inequalities (M.supportIn T hunimod eW)
    D.label₁ hnz D.mode coeff hout hin D.offset₁ D.offset₂
  · intro s
    exact hbound s D rfl rfl hlabels
  · intro s
    simpa only [hoffset₁, hoffset₂] using
      hbound s R hmode (hlabel₁.trans hlabels) hlabel₂

/-- Finitely many cone and label thresholds give a single positive
threshold for all original neighboring rows. Cofinal restriction supplies
positive scales before reversal. -/
theorem exists_uniform_neighbor_offset_threshold
    [Nonempty (Fin M.letterCount)]
    (hExp : IsGroupExponential ExpG)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (hcone : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      ∃ coeff : Fin M.letterCount → ℕ,
        (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
          transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val →
            coeff j = 0) ∧
        (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
          transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val →
            0 < coeff j) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ ε →
          ∀ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
            haarN chartN hchartN pivot shrink B ζ S (Λ := Λ),
          R.mode = i → R.label₁ = A → R.label₂ = A →
            (∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
              (R.offset₂ - R.offset₁) ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ ε →
      ∀ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B ζ S (Λ := Λ),
      R.label₂ = R.label₁ → R.offset₁ = R.offset₂ := by
  classical
  choose coeff hout hin ε hε hbound using hcone
  let J := Σ i : Fin M.letterCount,
    (templateSymmetryGroup (M.supportIn T hunimod eW) ×
      rootOffsetConeIndex (M.supportIn T hunimod eW) i)
  let : Fintype J := Fintype.ofFinite J
  let : Nonempty J := ⟨⟨Classical.arbitrary _, 1, none⟩⟩
  let threshold : J → ℝ := fun j => ε j.1 j.2.1 j.2.2
  obtain ⟨j₀, _, hmin⟩ := Finset.exists_min_image Finset.univ threshold Finset.univ_nonempty
  refine ⟨threshold j₀, hε _ _ _, ?_⟩
  intro ζ hζ hζε R hlabels
  obtain ⟨u, hu, _, hs⟩ := exists_strictMono_scale_subsequence R.scale R.grows
  let R' := R.reindex T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B ζ S u hu
  apply R'.offsets_eq_of_cone_bounds T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B ζ S hExp dynkinN hcell hne hβ hζ.le
    (fun n => zero_le_one.trans (hs n)) hlabels hnz (coeff R'.mode R'.label₁)
    (hout R'.mode R'.label₁) (hin R'.mode R'.label₁)
  intro s Q hmode hlabel₁ hlabel₂
  exact hbound R'.mode R'.label₁ s ζ hζ
    (hζε.trans (hmin ⟨R'.mode, R'.label₁, s⟩ (Finset.mem_univ _))) Q hmode hlabel₁ hlabel₂

end PolycyclicRecognition.CartanWordModel

end

end OAI
