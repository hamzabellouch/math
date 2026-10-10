import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSeparatedAlternatingComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathTupleLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactTupleThickening
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ShortSheetBridges

namespace OAI

/-! # Alternating volume comparison from actual controlled target paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

theorem path_alternating_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
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
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (t : ℕ → Finset G) {Rc q : ℝ}
    (hpaths : ∀ n x, x ∈ s n →
      ∃ path : ∀ i : Fin (h * 2), Path (1 : G)
          ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)),
        (∀ i, PathMetricBound (path i) (A * scale n)
          (B * (1 + Real.log (2 + scale n)))) ∧
        (∀ i u, ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
          ‖(π (path i u)).toAdd - scale n • z‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ∧
        ∀ i : Fin (h * 2),
          ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
            η n * scale n)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → 1 ≤ dist x y)
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩) y ≤ Rc)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * q))) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤ q := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let path := fun n (x : Fin (h * 2) → G) =>
    if hx : x ∈ s n then (hpaths n x hx).choose
    else fun i : Fin (h * 2) => (exists_short_path_of_minimizing_paths hpath 1
      ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).choose
  have hmetric n x (hx : x ∈ s n) i : PathMetricBound (path n x i)
      (A * scale n) (B * (1 + Real.log (2 + scale n))) := by
    simpa only [path, dite_eq_left hx] using (hpaths n x hx).choose_spec.1 i
  have htemplate n x (hx : x ∈ s n) i u : ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
      ‖(π (path n x i u)).toAdd - scale n • z‖ ≤
        2 * scale n * η n + A * (1 + Real.log (2 + scale n)) := by
    simpa only [path, dite_eq_left hx] using (hpaths n x hx).choose_spec.2.1 i u
  have hend n x (hx : x ∈ s n) (i : Fin (h * 2)) :
      ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
        η n * scale n := (hpaths n x hx).choose_spec.2.2 i
  have hEc (i : Fin (h * 2)) : IsCompact (alternatingCoordinateFamily h E₁ E₂ i) := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hEn (i : Fin (h * 2)) : (alternatingCoordinateFamily h E₁ E₂ i).Nonempty := by
    refine ⟨0, ?_⟩
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hβ (i : Fin (h * 2)) : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (alternatingCoordinateFamily h E₁ E₂ i))
      (alternatingCoordinateFamily h β₁ β₂ i).val := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  obtain ⟨RH, R, p, hRH0, hR0, hRH, hR, hp⟩ := M.exists_sequence_path_tuple_lifts
    T F hunimod eW hExpG realize π hπExp chartN hchartN chartD hchartD hbijN hbijD
    dynkinN dynkinD b₀ β hpath hKπ hLip (h * 2) (alternatingCoordinateFamily h E₁ E₂)
    (alternatingCoordinateFamily h β₁ β₂) hEc hEn hβ scale η hs hscale hη0 hη
    A B hA hB (fun n => (↑(s n) : Set (Fin (h * 2) → G))) path hmetric htemplate hend
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let : LocallyCompactSpace F.D.carrier := F.closedD.locallyCompactSpace
  let : SigmaFinite μ := inferInstance
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨U, hU, hUpos, hsmall⟩ := exists_small_factor_tuple_neighborhood
    F.inclusionN F.inclusionD F.closedN.continuous F.closedD.continuous μ ν (h * 2)
    (show (0 : ℝ) < 1 by norm_num)
  have hη' : Tendsto (fun n => ((h * 2 : ℕ) : ℝ) * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hη
  exact M.separated_alternating_product_exponent_le T F hunimod eW hExpG hinjG realize rem
    π hπ hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD
    b₀ β β₁ β₂ E E₁ E₂ hh aN hm hn scale RH R (fun n => ((h * 2 : ℕ) : ℝ) * η n)
    hs (fun n => lt_of_lt_of_le zero_lt_one (hscale n)) hRH0 hR0 hRH hR hη' p₀ hlim z₀ hsub
    hE₁ hE₂ h01 h02 hβ₁ hβ₂ ν s p U hU hUpos t
    (fun n x hx => (hp n x hx).1) hsmall hsep
    (fun n x hx => (hp n x hx).2.1) (fun n x hx => (hp n x hx).2.2.1)
    (fun n x hx => (hp n x hx).2.2.2) hnum hcover hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
