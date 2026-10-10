import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoupledProfileComparison
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubsequences
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanComparisonSchemes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSupports

namespace OAI

/-! # Template comparison for the diagonal's actual positive good sets

The good sets have subexponential relative Haar mass and affine errors
vanishing on every prescribed compact. They need not occupy a fixed
positive fraction of the original sampling probability.
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


variable [Fintype I] [DecidableEq I]

theorem good_affine_templates_support_le
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

    (E cell : Set W) (hE : IsCompact E) (hEconv : Convex ℝ E)
    (hcell : IsCompact cell) (hEcell : E ⊆ cell)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ E)
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
    (R : ℕ → ℝ) (k₀ k : ℕ → F.N.carrier) (δ : ℕ → ℝ)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hk : ∀ n, k n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hbridge : ∀ᶠ n in atTop,
      dist (ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (k n) * ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ n * scale n)
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
        ∀ᶠ n in atTop, ∀ q ∈ Good n, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN q) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₁.val (height (b.equivFun.symm z)) + offset₁)‖ ≤ ε n ∧
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n)) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₂.val (height (b.equivFun.symm z)) + offset₂)‖ ≤ ε n) :
    (M.supportIn T hunimod eW).templateSupport
      ((A₁.val '' ((fun w => w - eW (heightProjection T.character pivot)) '' E)) ∪
        (A₂.val '' ((fun w => w - eW (heightProjection T.character pivot)) '' E))) ≤
      (M.supportIn T hunimod eW).templateSupport E := by
  classical
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let E₀ := (fun w => w - height pivot) '' E
  let E₁ := A₁.val '' E₀
  let E₂ := A₂.val '' E₀
  have hE₀ : IsCompact E₀ := hE.image (continuous_id.sub continuous_const)
  have hE₀conv : Convex ℝ E₀ := hEconv.affine_image
    ((AffineMap.id ℝ W) - AffineMap.const ℝ W (height pivot))
  have h0 : (0 : W) ∈ E₀ := ⟨height pivot, hpivot, sub_self _⟩
  have hE₁ : IsCompact E₁ := hE₀.image A₁.val.continuous_of_finiteDimensional
  have hE₂ : IsCompact E₂ := hE₀.image A₂.val.continuous_of_finiteDimensional
  have h01 : (0 : W) ∈ E₁ := ⟨0, h0, map_zero _⟩
  have h02 : (0 : W) ∈ E₂ := ⟨0, h0, map_zero _⟩
  have hP : (M.supportIn T hunimod eW).templateSupport E₀ =
      (M.supportIn T hunimod eW).templateSupport E := by
    simpa only [E₀, sub_eq_add_neg] using
      (M.supportIn T hunimod eW).templateSupport_translate hE ⟨_, hpivot⟩ (-height pivot)
  have hP₁ : (M.supportIn T hunimod eW).templateSupport E₁ =
      (M.supportIn T hunimod eW).templateSupport E :=
    (A₁.property E₀ hE₀ ⟨0, h0⟩ hE₀conv).trans hP
  have hP₂ : (M.supportIn T hunimod eW).templateSupport E₂ =
      (M.supportIn T hunimod eW).templateSupport E :=
    (A₂.property E₀ hE₀ ⟨0, h0⟩ hE₀conv).trans hP
  obtain ⟨β, hβ, hβweight⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ (E₁ ∪ E₂)
  obtain ⟨β₁, hβ₁, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E₁
  obtain ⟨β₂, hβ₂, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E₂
  obtain ⟨γ, hγ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  obtain ⟨u, hu, h, hh, target, z₀, ht, htsub, m, letters, source, t₀, hs, hssub⟩ :=
    M.exists_source_target_comparison_schemes T F hunimod eW hExpG realize haarN b₀ aN hm
      E E₁ E₂ hE₁ ⟨0, h01⟩ hE₂ ⟨0, h02⟩ β β₁ β₂ γ hβ hβ₁ hβ₂ hγ scale
      (fun n => le_trans zero_le_one (hscale1 n)) hdim
  obtain ⟨support, hsupport, hsupportWeight⟩ :=
    M.exists_cartan_template_supports T hunimod eW E hE ⟨_, hpivot⟩
  let v := fun i => support i - pivot
  let s := (M.supportIn T hunimod eW).weightSupport E
  have hv i : eW (heightProjection T.character (pivot + v i : H)) ∈ E := by
    simpa only [v, add_sub_cancel] using hsupport i
  have hvs i : cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i := by
    rw [show pivot + v i = support i by dsimp [v]; abel, eW.symm_apply_apply,
      cartanHeightWeight_projection]
    exact congrFun hsupportWeight i
  have hsCell i : s i ≤ (M.supportIn T hunimod eW).weightSupport cell i := by
    dsimp only [s]
    rw [← hsupportWeight]
    have ht := (M.supportIn T hunimod eW).weight_le_weightSupport hcell
      (hEcell (hsupport i)) i
    simpa only [templateSupportExponent, supportIn, SupportDatum.transport_weight_apply, supportDatum_weight,
      eW.symm_apply_apply, cartanHeightWeight_projection] using ht
  let kb := fun n => alternatingCoordinateFamily h (1 : F.N.carrier) (k (u n))
  let As := alternatingCoordinateFamily h A₁.val.toLinearMap A₂.val.toLinearMap
  let bs := alternatingCoordinateFamily h offset₁ offset₂
  have hk1 n : (1 : F.N.carrier) ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      cell βcell (scale (u n)) (R (u n)) := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
    · simpa only [map_zero, norm_zero] using hR0 (u n)
  have hkb n i : kb n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      cell βcell (scale (u n)) (R (u n)) := by
    dsimp only [kb, alternatingCoordinateFamily]
    split_ifs
    · exact hk1 n
    · exact hk (u n)
  have himage i : (fun w => As i (w - height pivot)) '' E =
      alternatingCoordinateFamily h E₁ E₂ i := by
    dsimp only [As, alternatingCoordinateFamily]
    split_ifs <;> simp only [E₁, E₂, E₀, image_image, LinearEquiv.coe_coe]
  have hb : ∀ᶠ n in atTop, ∀ i,
      dist (ExpG (scale (u n) • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (kb n i) * ExpG (scale (u n) • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ (u n) * scale (u n) := by
    filter_upwards [hu.tendsto_atTop.eventually hbridge] with n hn i
    dsimp only [kb, alternatingCoordinateFamily]
    split_ifs
    · simpa only [map_one, one_mul, dist_self] using
        mul_nonneg (hδ0 (u n)) (le_trans zero_le_one (hscale1 (u n)))
    · exact hn
  obtain ⟨Q, hQ, _, hcompare⟩ := M.exists_coupled_profile_comparison_region T F hunimod eW
    hExpG hinjG realize rem π hLip hπExp chartN hchartN chartD hchartD hbijN hbijD
    dynkinN dynkinD haarN haarD b₀ E univ cell E₁ E₂ hE hEconv pivot hpivot
    isOpen_univ convex_univ (subset_univ _) v hv s hvs hsCell β β₁ β₂ βcell γ
    hβ₁ hβ₂ hβcell hγ hE₁ hE₂ h01 h02 hP₁ hP₂ X hDnil bD₀ βD hβD letters hh aN hm
    hdim (scale ∘ u) (hscale.comp hu.tendsto_atTop) (fun n => hscale1 (u n))
    source hs t₀ hssub target ht z₀ htsub ν 1 le_rfl As bs himage hpath
  obtain ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, happ⟩ := hgood Q hQ
  change (M.supportIn T hunimod eW).templateSupport (E₁ ∪ E₂) ≤ _
  rw [← hβweight]
  apply hcompare hΛ (p ∘ u) (x ∘ u) (R ∘ u) (k₀ ∘ u) kb (Good ∘ u) (ε ∘ u) (δ ∘ u)
    (fun n => hR0 (u n)) (hR.comp hu.tendsto_atTop) (fun n => hk₀ (u n)) hkb
    (fun n => hGood (u n)) (fun n => hGoodQ (u n)) (fun n => hGoodpos (u n))
    (hGoodmass.comp hu.tendsto_atTop) (fun n => hε0 (u n)) (hε.comp hu.tendsto_atTop)
    (fun n => hδ0 (u n)) (hδ.comp hu.tendsto_atTop) hb
  filter_upwards [hu.tendsto_atTop.eventually happ] with n hn
  intro i q hq z hz hze
  have hboth := hn q hq z hz hze
  dsimp only [kb, As, bs, alternatingCoordinateFamily]
  split_ifs
  · simpa only [mul_one, LinearEquiv.coe_coe, Function.comp_apply] using hboth.1
  · exact hboth.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
