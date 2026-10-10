import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGoodTemplateComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGoodFacetAgreement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FacetReflectionTemplates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction

namespace OAI

/-! # Root-neighbor label equality from the diagonal's retained good sets

The relative Haar mass may decay subexponentially. No positive limiting
fraction or supported point of the full sampling law is required.
-/

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

theorem good_root_neighbor_labels_eq
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

    (cell : Set W) (hcell : IsCompact cell)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ cell)
    (i : Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ j, α j (eW (heightProjection T.character pivot)) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (offset₁ offset₂ : W)
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (R : ℕ → ℝ) (k₀ k : ℕ → F.N.carrier) (η t : ℕ → ℝ)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hk : ∀ n, k n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp ((M.weight i pivot + η n) * scale n))
    (hstep : ∀ n, F.inclusionN (k n) =
      ExpG (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hgood : ∀ Q : Set (Fin (finrank ℝ H) → ℝ), IsCompact Q →
      ∃ (Good : ℕ → Set F.N.carrier) (ε : ℕ → ℝ),
        (∀ n, MeasurableSet (Good n)) ∧
        (∀ n, Good n ⊆ (fun y => y * k₀ n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1) ∧
        (∀ n, 0 < ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
          (Good n)).toReal) ∧
        HasSubexponentialLowerBoundSeq scale (fun n =>
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal /
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
            ((fun y => y * k₀ n) '' M.groupBox T hunimod eW
              (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1)).toReal) ∧
        (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := fun n => exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
          ((heightProjection T.character).comp H.incl.toLinearMap)
        ∀ᶠ n in atTop, ∀ q ∈ Good n, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ cell →
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN q) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₁.val (height (b.equivFun.symm z)) + offset₁)‖ ≤ ε n ∧
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n)) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₂.val (height (b.equivFun.symm z)) + offset₂)‖ ≤ ε n) : A₁ = A₂ := by
  classical
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let ℓ := (M.supportIn T hunimod eW).weight i
  have hweight (v : H) : ℓ (height v) = M.weight i v := by
    change cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) = _
    rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  have hℓ : ℓ ≠ 0 := by
    intro hzero
    apply M.weight_nonzero i
    funext v
    change M.weight i v = 0
    have hz := congrArg (fun f : W →ₗ[ℝ] ℝ => f (height v)) hzero
    simpa only [hweight, LinearMap.zero_apply] using hz
  have hpoint : ∀ j, α j (height pivot) ≤ c j := by
    have hp : height pivot ∈ cell := hpivot
    rw [hpoly] at hp
    exact hp
  obtain ⟨ρ, hρ, hlocal⟩ := exists_relative_facet_neighborhood α c (height pivot) ℓ hpoint hactive
  obtain ⟨δ, hδ0, hδ, hbridge⟩ := exists_facet_pivot_bridge_rate T H (M.weight i)
    (M.weight_nonzero i) ExpG hExpG realize ⟨M.letter i, M.letter_root i⟩ pivot
    scale R η t hscale (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) hR0 hR hη ht
  have hagree : ∀ w, ℓ w = ℓ (height pivot) → ‖w - height pivot‖ < ρ →
      A₁.val w + offset₁ = A₂.val w + offset₂ := by
    intro w hw hn
    let v := cartanHeightSection T H (eW.symm w)
    let z := b.equivFun v
    have hz : height (b.equivFun.symm z) = w := by
      change eW (heightProjection T.character
        (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
      simp only [z, LinearEquiv.symm_apply_apply, v,
        cartanHeightSection_height, eW.apply_symm_apply]
    have hz' : (eW.toLinearMap.comp
        ((heightProjection T.character).comp H.incl.toLinearMap))
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z) = w := hz
    have hwcell : w ∈ cell := by rw [hpoly]; exact hlocal w hw hn
    have hwt : M.weight i (b.equivFun.symm z) = M.weight i pivot := by
      rw [← hweight, hz, hw, hweight]
    obtain ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, happ⟩ :=
      hgood {z} isCompact_singleton
    have hne n : (Good n).Nonempty := by
      by_contra hn
      have he : Good n = ∅ := not_nonempty_iff_eq_empty.mp hn
      simpa only [he, measure_empty, ENNReal.toReal_zero, lt_self_iff_false] using hGoodpos n
    have hsame := M.good_word_profiles_agree_on_facet T ExpG hExpG realize X
      (boundedBracketWords d) βD z i scale R η t hscale hscale1 hR0 hR hη
      (by
        change ∀ n, |t n| ≤ R n * Real.exp ((M.weight i (b.equivFun.symm z) + η n) * scale n)
        simpa only [hwt] using ht)
      (fun n g => (π ((p n).val.1 g)).toAdd)
      (fun n => hLip.comp (p n).property.1.1) x (fun _ q => F.inclusionN q)
      Good hne ε hε (A₁.val w + offset₁) (A₂.val w + offset₂) ?_
    · exact hsame
    · filter_upwards [happ] with n hn
      intro q hq
      have hb := hn q hq z (mem_singleton z) (hz ▸ hwcell)
      simpa only [map_mul, hstep, hz', wordChartPivot,
        max_eq_left (Real.log_nonneg (hscale1 n))] using hb
  apply affine_labels_eq_of_template_comparison (M.supportIn T hunimod eW) A₁ A₂ ℓ hℓ
    offset₁ offset₂ (height pivot) α c hpoint hactive hρ hagree
  intro E hE hEconv hEcell hpE
  have hEcell' : E ⊆ cell := by simpa only [hpoly] using hEcell
  apply M.good_affine_templates_support_le T F hunimod eW hExpG hinjG realize rem π hLip
    hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    E cell hE hEconv hcell hEcell' pivot hpE A₁ A₂ offset₁ offset₂ βcell hβcell X hDnil
    bD₀ βD hβD aN hm hdim scale hscale hscale1 ν hpath hΛ p x R k₀ k δ hR0 hR hk₀ hk
    hδ0 hδ (Eventually.of_forall (fun n => by
      simpa only [one_mul, hstep] using hbridge n 1))
  intro Q hQ
  obtain ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, happ⟩ := hgood Q hQ
  refine ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, ?_⟩
  filter_upwards [happ] with n hn
  intro q hq z hz hze
  exact hn q hq z hz (hEcell' hze)

end PolycyclicRecognition.CartanWordModel

end

end OAI
