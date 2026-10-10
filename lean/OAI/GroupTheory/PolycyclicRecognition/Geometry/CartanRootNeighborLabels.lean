import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportedTemplateComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFacetSupportedAgreement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FacetReflectionTemplates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction

namespace OAI

/-! # Labels agree for supported root-neighbor profiles on a closed cell

The root distortion estimate proves contact-facet agreement and supplies
the pivot bridge. The actual coupled-volume theorem then rules out the
reflection alternative. No neighboring-label assertion is assumed.
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

theorem supported_root_neighbor_labels_eq
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
    (SP : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace SP] [BorelSpace SP] [BorelSpace (SP × SP)] [HasOuterApproxClosed (SP × SP)]
    (profile : ℕ → F.N.carrier → SP × SP) (hprofile : ∀ n, Measurable (profile n))
    (limit : ProbabilityMeasure (SP × SP)) (f : SP × SP)
    (hf : f ∈ (limit : Measure (SP × SP)).support)
    (hlimit : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ cell βcell
        (scale n) (k₀ n)) (profile n)) atTop (𝓝 limit)) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let br := fun n => exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    let Qcell := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1
    (∀ n q, q ∈ Qcell n → ∀ z, (profile n q).1.val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN q) (Real.log (scale n)) (fun z => ExpG ((br n).equivFun.symm z)) z) →
    (∀ n q, q ∈ Qcell n → ∀ z, (profile n q).2.val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (q * k n)) (Real.log (scale n)) (fun z => ExpG ((br n).equivFun.symm z)) z) →
    (∀ z, height (b.equivFun.symm z) ∈ cell →
      f.1.val z = A₁.val (height (b.equivFun.symm z)) + offset₁) →
    (∀ z, height (b.equivFun.symm z) ∈ cell →
      f.2.val z = A₂.val (height (b.equivFun.symm z)) + offset₂) →
    A₁ = A₂ := by
  classical
  dsimp only
  intro hactual₁ hactual₂ haffine₁ haffine₂
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
  let samples := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN
    b₀ cell βcell (scale n) (k₀ n)
  let Qcell := fun n => (fun y => y * k₀ n) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1
  have hfull n : ∀ᵐ q ∂(samples n : Measure F.N.carrier), q ∈ Qcell n := by
    exact ae_mem_cellProbabilityMeasure _ _
      (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ cell βcell
        (scale n) (k₀ n)).1 _ _
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
    have hwcell : w ∈ cell := by rw [hpoly]; exact hlocal w hw hn
    have hwt : M.weight i (b.equivFun.symm z) = M.weight i pivot := by
      rw [← hweight, hz, hw, hweight]
    have hsame := M.supported_word_profiles_agree_on_facet T ExpG hExpG realize X
      (boundedBracketWords d) βD z i scale R η t hscale hscale1 hR0 hR hη
      (by
        change ∀ n, |t n| ≤ R n * Real.exp ((M.weight i (b.equivFun.symm z) + η n) * scale n)
        simpa only [hwt] using ht)
      (fun n g => (π ((p n).val.1 g)).toAdd)
      (fun n => hLip.comp (p n).property.1.1) x (fun _ q => F.inclusionN q)
      SP samples profile hprofile limit hlimit ?_ ?_ hf
    · rw [haffine₁ z (hz ▸ hwcell), haffine₂ z (hz ▸ hwcell), hz] at hsame
      exact hsame
    · intro n
      filter_upwards [hfull n] with q hq
      have he := hactual₁ n q hq z
      simpa only [wordChartPivot, max_eq_left (Real.log_nonneg (hscale1 n))] using he
    · intro n
      filter_upwards [hfull n] with q hq
      have he := hactual₂ n q hq z
      simpa only [map_mul, hstep, wordChartPivot,
        max_eq_left (Real.log_nonneg (hscale1 n))] using he
  apply affine_labels_eq_of_template_comparison (M.supportIn T hunimod eW) A₁ A₂ ℓ hℓ
    offset₁ offset₂ (height pivot) α c hpoint hactive hρ hagree
  intro E hE hEconv hEcell hpE
  have hEcell' : E ⊆ cell := by simpa only [hpoly] using hEcell
  exact M.supported_affine_templates_support_le T F hunimod eW hExpG hinjG realize rem π hLip
    hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    E cell hE hEconv hcell hEcell' pivot hpE A₁ A₂ offset₁ offset₂ βcell hβcell X hDnil
    bD₀ βD hβD aN hm hdim scale hscale hscale1 ν hpath hΛ p x R k₀ k δ hR0 hR hk₀ hk
    hδ0 hδ (Eventually.of_forall (fun n => by
      simpa only [one_mul, hstep] using hbridge n 1)) SP profile hprofile limit f hf hlimit
    hactual₁ hactual₂
    (fun z hz => haffine₁ z (hEcell' hz)) (fun z hz => haffine₂ z (hEcell' hz))

end PolycyclicRecognition.CartanWordModel

end

end OAI
