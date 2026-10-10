import OAI.Combinatorics.Progressions.Estimates.AnchoredSelectedNormalization
import OAI.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
import OAI.Combinatorics.Progressions.Estimates.RelativeWidthProfileScale

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

theorem exists_anchored_sampler_geometry (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G Q : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    [Fintype Q] [DecidableEq Q]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (site : Q → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (_hsitebound : ∀ q k, |(site q k : ℝ)| ≤ Real.exp P)
    (anchor : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S ρ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (_hρ : 0 < ρ) (_hρP : 1/ρ ≤ Real.exp P)
    (H : X → ℝ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) H Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p hm
    let Z := selectedResidueDensityMass stride T W (fun z => D (anchor + z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : 0 < Z,
    let law := translatedSelectedResidueDensityPMF anchor stride T W hW hZ D
      (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm) hD
    |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      (∀ z, 0 < (law z).toReal →
        z - anchor ∈ rectangularWeightIndices 0 W 1 ∧
        columnResiduePattern stride (z - anchor) ∈ T ∧ 0 < D z) ∧
      (∀ z, 0 < (law z).toReal →
        HasQuarterAffinePolynomialLifts p (fun _ => 0) (fun k x => (z (k,x) : ℝ))
          (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀))) ∧
      (∑' z, (law z).toReal *
        noninjectivityIndicator (fun q => integerPhysicalSite (site q) z)) ≤ δ := by
  obtain ⟨A₀, _, hnormal⟩ := exists_anchored_selected_sampler_normalization m
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_selectedCollisionLog_bound m
  let A := max 256 (max A₀ A₁)
  have hA : 256 ≤ A := le_max_left _ _
  refine ⟨A, by omega, ?_⟩
  intro X G Q _ _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite hsitebound anchor p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  have hthreshold (a : ℕ) (ha : a ≤ A) : Real.exp ((P+a)^a) ≤ Real.exp ((P+A)^A) := by
    apply Real.exp_le_exp.mpr
    have haa : (a : ℝ) ≤ A := by exact_mod_cast ha
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P+(a:ℝ) ≤ P+A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P+A) ha)
  have h₀ := hthreshold A₀ ((le_max_left A₀ A₁).trans (le_max_right 256 _))
  have h₁ := hthreshold A₁ ((le_max_right A₀ A₁).trans (le_max_right 256 _))
  obtain ⟨hZ, hD, hclose, hlower, hupper, _⟩ :=
    hnormal B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor p hp hm stride hs
      hS hSP hstride hρ hρP H (fun i => h₀.trans (hsize i)) hrank (h₀.trans hRrank)
      T hT W hW hwidth
  let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p hm
  have hD0 : ∀ z, 0 ≤ D z := selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm
  have hsupport := translatedSelectedResidueDensityPMF_support anchor stride T W hW hZ D hD0 hD
  refine ⟨hZ, hD, hclose, hlower, hupper, hsupport, ?_, ?_⟩
  · intro z hz
    exact selectedPhysicalDensity_quarter_lifts B U b hb o R σ hR hσ L₀
      hσ1 Cinv hCinv hchart hsmall p hp hm z (hsupport z hz).2.2.ne'
  · let i : X := Classical.choice inferInstance
    have hscale := residueProfileWidth_large_of_exp_size hP hρ hρP hAP stride hs
      (fun j => (hstride j).trans hSP) H
      (fun j => (spatial_threshold_large hP hA).trans (hsize j)) W hwidth
    exact anchored_selectedResidue_tilted_collision_small m anchor site hsite i hP hδ hδP hK
      hsitebound stride hs ((hstride i).trans hSP) T hT W hW hZ hscale hρ
      (hρP.trans (Real.exp_le_exp.mpr (le_spatialSamplingBudget hP)))
      ((Real.exp_le_exp.mpr (hcollisionBudget P hP)).trans (h₁.trans (hsize i)))
      (fun k => hwidth (some k,i)) D hD0 hD hlower
      (selectedPhysicalDensity_le_exp B U b hb o C V hC hV R σ hR hσ hσ1 Cinv hCinv
        hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP p hm)

end Erdos3.VectorPolynomial

end

end OAI
