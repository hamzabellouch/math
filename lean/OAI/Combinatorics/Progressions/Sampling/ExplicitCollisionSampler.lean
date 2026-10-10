import OAI.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
variable (L₀ : ℕ) {P : ℝ} (hP : 0 ≤ P)
variable (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
variable (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
variable (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
variable (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
variable (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
variable (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)

include hC hV hσ1 hCinv hchart hsmall hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP in
theorem selectedPhysicalDensity_collision_small {X S : Type*}
    [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (site : S → LayerSamplerVariables G I n B → ℤ) (hsite : Function.Injective site) (i : X)
    {δ : ℝ} (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X modulus))
    (hT : T.Nonempty) (W : Option (LayerSamplerVariables G I n B) × X → ℝ)
    (hW : ∀ z, 0 < W z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (selectedCollisionLog m P) ≤ N) (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (hD : 0 < selectedResidueDensityMass modulus T W
      (selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm))
    (hlower : 1/2 ≤ selectedResidueDensityMass modulus T W
      (selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm)) :
    (∑' z, (selectedResidueDensityPMF modulus T W hW hZ
      (selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm)
      (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm) hD z).toReal *
      noninjectivityIndicator (fun s => BooleanCubeKernel.integerPhysicalSite (site s) z)) ≤ δ := by
  exact BooleanCubeKernel.selectedResidue_tilted_collision_small m site hsite i hP hδ hδP
    hK hbound modulus hmodulus hmodP T hT W hW hZ hscale hρ hρP hN hwidth
    (selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm)
    (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm) hD hlower
    (selectedPhysicalDensity_le_exp B U b hb o C V hC hV R σ hR hσ hσ1 Cinv hCinv
      hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP p hm)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_explicit_spatial_sampler_with_collisions (m : ℕ) :
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
    (τ : ℝ) (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := centeredSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
    let a : X → ℝ := fun i => (integerBoxCenter N i : ℝ)
    let p' := fun j => translate a (p j)
    let hm' := fun j => coefficients_translate_mem (U j) a (p j) (hm j)
    let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p' hm'
    let Z := selectedResidueDensityMass stride T W D
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hDpos : 0 < Z,
    let law := selectedResidueDensityPMF stride T W hW hZ D
      (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p' hm') hDpos
    |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      (∀ root : LayerSamplerVariables G I n B → ℤ,
        (∀ k, |(root k : ℝ)| ≤ Real.exp P) → ∀ z, 0 < (law z).toReal →
          centeredIntegerPhysicalSite root N z ∈ integerBox N) ∧
      (∀ root : LayerSamplerVariables G I n B → ℤ,
        (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
        ∀ φ : (X → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
          (∑' z, (law z).toReal * φ (fun i => (centeredIntegerPhysicalSite root N z i : ℝ))) ≤
            2*M*(16*S)^Fintype.card X * (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ) ∧
      (∑' z, (law z).toReal *
        noninjectivityIndicator (fun q => centeredIntegerPhysicalSite (site q) N z)) ≤ δ := by
  obtain ⟨A₀, _, hsampler⟩ := exists_explicit_spatial_sampler m
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_selectedCollisionLog_bound m
  let A := max 256 (max A₀ A₁)
  have hA : 256 ≤ A := le_max_left _ _
  refine ⟨A, by omega, ?_⟩
  intro X G Q _ _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite hsitebound τ hτ hτ1 hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  have hthreshold (a : ℕ) (ha : a ≤ A) : Real.exp ((P+a)^a) ≤ Real.exp ((P+A)^A) := by
    apply Real.exp_le_exp.mpr
    have haa : (a : ℝ) ≤ A := by exact_mod_cast ha
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P+(a:ℝ) ≤ P+A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P+A) ha)
  have h₀ := hthreshold A₀ ((le_max_left A₀ A₁).trans (le_max_right 256 _))
  have h₁ := hthreshold A₁ ((le_max_right A₀ A₁).trans (le_max_right 256 _))
  have hsample (root : LayerSamplerVariables G I n B → ℤ)
      (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P) :=
    hsampler B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot τ hτ hτ1 hτP
      p hp hm stride hs hS hSP hstride N (fun i => h₀.trans (hsize i)) hrank
      (h₀.trans hRrank) T hT
  obtain ⟨hW, hZ, hDpos, hclose, hlower, hupper, _⟩ :=
    hsample 0 (fun k => by simpa using (Real.exp_pos P).le)
  let W := centeredSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
  let a : X → ℝ := fun i => (integerBoxCenter N i : ℝ)
  let p' := fun j => translate a (p j)
  let hm' := fun j => coefficients_translate_mem (U j) a (p j) (hm j)
  let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p' hm'
  have hN (i) : 4 ≤ N i := four_le_of_spatial_threshold hP hA (N i) (hsize i)
  have hscale := centeredSpatialWidths_scale (K := LayerSamplerVariables G I n B)
    (Real.exp_pos (2*P)).le hτ1 stride hs N (fun i =>
      spatial_scale_of_exp_size hP hτ hτP (Nat.cast_nonneg _) ((hstride i).trans hSP) hAP
        ((spatial_threshold_large hP hA).trans (hsize i)))
  refine ⟨hW, hZ, hDpos, hclose, hlower, hupper, ?_, ?_, ?_⟩
  · intro root hroot z hz
    exact selectedResidueDensityPMF_centered_mem_box root N hN stride T W hW
      (centeredSpatialWidths_fit (Real.exp_pos (2*P)).le hτ.le hτ1 root
        (root_sum_le_spatial_budget hK root hroot) N) hZ D
      (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p' hm') hDpos z hz
  · intro root hroot φ hφ
    obtain ⟨_, _, _, _, _, _, htest⟩ := hsample root hroot
    simpa only [centeredIntegerPhysicalSite_cast] using htest φ hφ
  · simp_rw [noninjectivityIndicator_centered]
    let i : X := Classical.choice inferInstance
    exact selectedPhysicalDensity_collision_small B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP
      p' hm' site hsite i hδ hδP hsitebound stride hs ((hstride i).trans hSP) T hT W hW hZ
      hscale (spatialWidthFraction_pos P hτ) (spatialWidthFraction_inv_le hP hτ hτP)
      ((Real.exp_le_exp.mpr (hcollisionBudget P hP)).trans (h₁.trans (hsize i)))
      (fun k => spatialWidthFraction_mul_le_width P hτ1 N (some k,i)) hDpos hlower

end Erdos3.BooleanCubeKernel

end

end OAI
