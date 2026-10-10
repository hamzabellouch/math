import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial
noncomputable def coefficientCoverTiltedConstant (m : ℕ) : ℕ :=
  Classical.choose (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)

theorem coefficientCoverTiltedConstant_ge_two (m : ℕ) :
    2 ≤ coefficientCoverTiltedConstant m :=
  (Classical.choose_spec (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)).1

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_selected_density_ambient_cover_tilted_comparison (R σ : Fin m → ℝ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (cover : ℕ) (hcover : 0 < cover)
    (f : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → UnitAddCircle) → ℂ)
    (Lf : ℝ≥0) (hf : LipschitzWith Lf f) (hfb : ∀ x, ‖f x‖ ≤ 1)
    {η Q : ℝ} (hη : 0 < η) (hQ : 0 ≤ Q)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ Q)
    (hLf : (Lf : ℝ) ≤ Real.exp Q) (hηQ : η⁻¹ ≤ Real.exp Q)

    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hcoverPs : (cover : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, (stride x : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + coefficientCoverTiltedConstant m) ^ coefficientCoverTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + coefficientCoverTiltedConstant m) ^ coefficientCoverTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : cover * Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) +
      Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp Ps)
    (hmassPs : Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) *
      Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp Ps)
    (hsmallError : 2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε ≤ 1 / 2) :
    let D := selectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hm
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm cover (fun k x => (z (k, x) : ℝ))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width D,
      |selectedResidueDensityMass stride cells width D - 1| ≤
        2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width D ∧
      selectedResidueDensityMass stride cells width D ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ D
        (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hm) hDpos z).toReal : ℂ) *
          f (coefficientAmbientTorus U (sample z))) -
        (∫ x, (selectedCoefficientDensity B U b hb o R σ hR hσ L₀
          (quotientIntegerCover (coefficientIntegerLattice U) cover x) : ℂ) *
            f (coefficientAmbientTorus U x) ∂μ)‖ ≤
        4 * (2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε) := by
  dsimp only
  let D : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ := selectedCoefficientDensity B U b hb o R σ hR hσ L₀
  let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) cover x)
  let ft := fun x => f (coefficientAmbientTorus U x)
  have hpair (a : Bool) := exists_selected_density_ambient_product_fourier B U b hb o C V hC hV
    R σ hR hσ hσ1 Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
    cover (fun x => if a then f x else 1) Lf
    (by cases a with
      | false => exact (LipschitzWith.const (1 : ℂ)).weaken (by positivity)
      | true => exact hf)
    (by intro x; cases a <;> simp [hfb x]) hη hQ hdim hLf hηQ
  choose F inst frequency coeff hcard hfreq hmass happ using hpair
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ
    (selectedLayerSamplerScale B U b R σ hR hσ L₀) hσ1 Cinv hCinv hchart hsmall μ ν
  have hDc := coefficientCover_density_integral U μ cover hcover D hspec.2.2.1 hspec.2.2.2.1
  have hD0 : ∀ x, 0 ≤ Dc x := fun x => selectedCoefficientDensity_nonneg B U b hb o R σ hR hσ L₀ _
  have hcont : Continuous ft := by
    apply hf.continuous.comp
    apply continuous_pi
    intro a
    exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
      ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))
  have hresult := (Classical.choose_spec (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)).2
    F hPs hX hframe U μ (by positivity) hfreqPs frequency hfreq coeff
    (by positivity) hmassPs hmass poly hp hm cover hcover hcoverPs stride hstride
    hSmax hSmaxPs hρ hε hρPs hεPs hstrideMax H hsize hrank hRs cells hcells width hwidth hwide
    Dc hDc.1 hDc.2 hD0 ft hcont.aestronglyMeasurable (fun x => hfb _)
    (by positivity) (by intro a x; simpa only [Dc, D, ft, selectedCoefficientDensity] using happ a x) hsmallError
  have hdensity : (fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      Dc (affineCoefficientCoverSample U poly hm cover (fun k x => (z (k, x) : ℝ)))) =
      selectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hm := by
    funext z
    exact coefficientCover_density_sample U poly hm cover hcover D _
  simpa only [hdensity, ft, Dc, D] using hresult

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem selectedResidueDensityPMF_approximation {K X : Type*} [Fintype K] [Fintype X]
    (modulus : X → ℕ) (cells : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells V z)
    (D : (K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus cells V D)
    (f g : (K × X → ℤ) → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (he : ∀ z ∈ rectangularWeightIndices 0 V 1, ‖f z - g z‖ ≤ η) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus cells V hV hZ D hD0 hD z).toReal : ℂ) * f z) -
      ∑' z, ((selectedResidueDensityPMF modulus cells V hV hZ D hD0 hD z).toReal : ℂ) * g z‖ ≤ η := by
  have h := normalized_finite_weight_approximation
    (fun z => selectedResidueSmoothWeight modulus cells V z * D z) (rectangularWeightIndices 0 V 1)
    (fun z => mul_nonneg (selectedResidueSmoothWeight_nonneg modulus cells V z) (hD0 z))
    (fun z hz => by rw [selectedResidueSmoothWeight_zero_off modulus cells V hV z hz, zero_mul])
    (finiteDensityMass_raw_pos (selectedResidueSmoothWeight modulus cells V) D hZ hD)
    (fun _ => 1) f g hη (fun _ _ => by simp) he
  simpa only [selectedResidueDensityPMF, finiteDensityTiltPMF, realWeightPMF_apply, one_mul] using h

namespace VectorPolynomial

open BooleanCubeKernel

noncomputable def normalizedPhysicalRootRadius {K X : Type*} [Fintype K] [Fintype X]
    (N : X → ℕ) (V : Option K × X → ℝ) (root : K → ℤ) : ℝ :=
  ‖fun x => physicalSiteWidth root V x / N x‖

theorem normalizedPhysicalRootRadius_nonneg {K X : Type*} [Fintype K] [Fintype X]
    (N : X → ℕ) (V : Option K × X → ℝ) (root : K → ℤ) :
    0 ≤ normalizedPhysicalRootRadius N V root := norm_nonneg _

theorem normalized_integerPhysicalSite_norm_le {K X : Type*} [Fintype K] [Fintype X]
    (N : X → ℕ) (V : Option K × X → ℝ) (root : K → ℤ)
    {z : Option K × X → ℤ} (hz : z ∈ rectangularWeightIndices 0 V 1) :
    ‖fun x => (integerPhysicalSite root z x : ℝ) / N x‖ ≤ normalizedPhysicalRootRadius N V root := by
  apply (pi_norm_le_iff_of_nonneg (normalizedPhysicalRootRadius_nonneg N V root)).mpr
  intro x
  have hsite := integerPhysicalSite_abs_bound root V z (rectangularWeightIndices_zero_bound V hz) x
  calc
    _ = |(integerPhysicalSite root z x : ℝ)| / N x := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (N x) : (0 : ℝ) ≤ N x)]
    _ ≤ physicalSiteWidth root V x / N x := div_le_div_of_nonneg_right hsite (Nat.cast_nonneg _)
    _ ≤ |physicalSiteWidth root V x / N x| := le_abs_self _
    _ ≤ normalizedPhysicalRootRadius N V root := by
      simpa only [Real.norm_eq_abs, normalizedPhysicalRootRadius] using
        norm_le_pi_norm (fun x => physicalSiteWidth root V x / (N x : ℝ)) x

namespace NormalizedPolynomialTwist

variable {K X : Type*} [Fintype K] [Fintype X] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem selected_density_eval_sub_frozenSpatialEval_root
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (modulus : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X modulus))
    (root : K → ℤ) (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells V z)
    (D : (Option K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus cells V D) :
    ‖(∑' z : Option K × X → ℤ,
      ((selectedResidueDensityPMF modulus cells V hV hZ D hD0 hD z).toReal : ℂ) *
        W.eval N poly (integerPhysicalSite root z)) -
      ∑' z : Option K × X → ℤ,
        ((selectedResidueDensityPMF modulus cells V hV hZ D hD0 hD z).toReal : ℂ) *
          W.frozenSpatialEval center poly (integerPhysicalSite root z)‖ ≤
      (L : ℝ) * (normalizedPhysicalRootRadius N V root + ‖center‖) := by
  apply selectedResidueDensityPMF_approximation modulus cells V hV hZ D hD0 hD
  · exact mul_nonneg L.coe_nonneg
      (add_nonneg (normalizedPhysicalRootRadius_nonneg N V root) (norm_nonneg center))
  intro z hz
  apply (W.eval_sub_frozenSpatialEval N center poly _).trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  rw [dist_eq_norm]
  exact (norm_sub_le _ _).trans
    (add_le_add (normalized_integerPhysicalSite_norm_le N V root hz) le_rfl)

theorem selected_density_eval_sub_frozenSpatialEval_root_zero
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (modulus : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X modulus))
    (root : K → ℤ) (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells V z)
    (D : (Option K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus cells V D) :
    ‖(∑' z : Option K × X → ℤ,
      ((selectedResidueDensityPMF modulus cells V hV hZ D hD0 hD z).toReal : ℂ) *
        W.eval N poly (integerPhysicalSite root z)) -
      ∑' z : Option K × X → ℤ,
        ((selectedResidueDensityPMF modulus cells V hV hZ D hD0 hD z).toReal : ℂ) *
          W.frozenSpatialEval 0 poly (integerPhysicalSite root z)‖ ≤
      (L : ℝ) * normalizedPhysicalRootRadius N V root := by
  simpa only [norm_zero, add_zero] using
    W.selected_density_eval_sub_frozenSpatialEval_root N 0 poly modulus cells root V hV hZ D hD0 hD

end NormalizedPolynomialTwist
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_selected_density_normalizedTwist_root_comparison (R σ : Fin m → ℝ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (root : LayerSamplerVariables G I n B → ℤ)
    (r : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X (fun _ => W.modulus))
    {η Q : ℝ} (hη : 0 < η) (hQ : 0 ≤ Q)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ Q)
    (hLf : ((L * coefficientAmbientRootLip m root : ℝ≥0) : ℝ) ≤ Real.exp Q) (hηQ : η⁻¹ ≤ Real.exp Q)

    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Ps ε ρ Rs : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hcoverPs : (W.cover : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (hmodulusPs : (W.modulus : ℝ) ≤ Real.exp Ps)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + coefficientCoverTiltedConstant m) ^ coefficientCoverTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + coefficientCoverTiltedConstant m) ^ coefficientCoverTiltedConstant m) ≤ Rs)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : W.cover * Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) +
      Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp Ps)
    (hmassPs : Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) *
      Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp Ps)
    (hsmallError : 2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε ≤ 1 / 2) :
    let D := selectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hm
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} width z,
    ∃ hDpos : 0 < selectedResidueDensityMass (fun _ => W.modulus) {r} width D,
      |selectedResidueDensityMass (fun _ => W.modulus) {r} width D - 1| ≤
        2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε ∧
      1 / 2 ≤ selectedResidueDensityMass (fun _ => W.modulus) {r} width D ∧
      selectedResidueDensityMass (fun _ => W.modulus) {r} width D ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF (fun _ => W.modulus) {r} width hwidth hZ D
        (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hm) hDpos z).toReal : ℂ) *
          W.frozenSpatialEval center poly (integerPhysicalSite root z)) -
        (∫ x, (selectedCoefficientDensity B U b hb o R σ hR hσ L₀
          (quotientIntegerCover (coefficientIntegerLattice U) W.cover x) : ℂ) *
            W.frozenAmbientRootObservable (NormalizedPolynomialTwist.rootResidue W.modulus root r)
              center root (coefficientAmbientTorus U x) ∂μ)‖ ≤
        4 * (2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε) := by
  dsimp only
  let residue := NormalizedPolynomialTwist.rootResidue W.modulus root r
  obtain ⟨hZ, hDpos, hmass, hlower, hupper, hcomp⟩ :=
    exists_selected_density_ambient_cover_tilted_comparison B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
      W.cover W.cover_pos (W.frozenAmbientRootObservable residue center root)
      (L * coefficientAmbientRootLip m root)
      (W.frozenAmbientRootObservable_lipschitz residue center root)
      (W.norm_frozenAmbientRootObservable_le residue center root)
      hη hQ hdim hLf hηQ μ ν poly hp hm hPs hX hframe hcoverPs hε hρ hεPs hρPs
      (fun _ => W.modulus) (fun _ => W.modulus_pos) (Nat.cast_nonneg _) hmodulusPs
      (fun _ => le_rfl) H hsize hrank hRs {r} (Finset.singleton_nonempty r) width hwidth hwide
      hfreqPs hmassPs hsmallError
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  rw [W.selected_density_frozenSpatialEval_root_eq center poly root r width hwidth hZ
    (selectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hm)
    (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hm) hDpos]
  simpa only [W.frozenAmbientRootObservable_sample residue center root U poly hp hm] using hcomp

include hC hV in
theorem exists_selected_density_normalizedTwist_eval_comparison (R σ : Fin m → ℝ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (center : X → ℝ) (root : LayerSamplerVariables G I n B → ℤ)
    (r : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X (fun _ => W.modulus))
    {η Q : ℝ} (hη : 0 < η) (hQ : 0 ≤ Q)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ Q)
    (hLf : ((L * coefficientAmbientRootLip m root : ℝ≥0) : ℝ) ≤ Real.exp Q) (hηQ : η⁻¹ ≤ Real.exp Q)

    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Ps ε ρ Rs : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hcoverPs : (W.cover : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (hmodulusPs : (W.modulus : ℝ) ≤ Real.exp Ps)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + coefficientCoverTiltedConstant m) ^ coefficientCoverTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + coefficientCoverTiltedConstant m) ^ coefficientCoverTiltedConstant m) ≤ Rs)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : W.cover * Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) +
      Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp Ps)
    (hmassPs : Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) *
      Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp Ps)
    (hsmallError : 2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε ≤ 1 / 2) :
    let D := selectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hm
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} width z,
    ∃ hDpos : 0 < selectedResidueDensityMass (fun _ => W.modulus) {r} width D,
      |selectedResidueDensityMass (fun _ => W.modulus) {r} width D - 1| ≤
        2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε ∧
      1 / 2 ≤ selectedResidueDensityMass (fun _ => W.modulus) {r} width D ∧
      selectedResidueDensityMass (fun _ => W.modulus) {r} width D ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF (fun _ => W.modulus) {r} width hwidth hZ D
        (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hm) hDpos z).toReal : ℂ) *
          W.eval N poly (integerPhysicalSite root z)) -
        (∫ x, (selectedCoefficientDensity B U b hb o R σ hR hσ L₀
          (quotientIntegerCover (coefficientIntegerLattice U) W.cover x) : ℂ) *
            W.frozenAmbientRootObservable (NormalizedPolynomialTwist.rootResidue W.modulus root r)
              center root (coefficientAmbientTorus U x) ∂μ)‖ ≤
        (L : ℝ) * (normalizedPhysicalRootRadius N width root + ‖center‖) +
          4 * (2 * (δ + Real.exp ((P + selectedFourierExponent m) ^ selectedFourierExponent m) * η) + ε) := by
  dsimp only
  obtain ⟨hZ, hDpos, hmass, hlower, hupper, hcomp⟩ :=
    exists_selected_density_normalizedTwist_root_comparison B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
      poly hp hm W center root r hη hQ hdim hLf hηQ μ ν hPs hX hframe hcoverPs
      hε hρ hεPs hρPs hmodulusPs H hsize hrank hRs width hwidth hwide hfreqPs hmassPs hsmallError
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  have hfreeze := W.selected_density_eval_sub_frozenSpatialEval_root N center poly
    (fun _ => W.modulus) {r} root width hwidth hZ
    (selectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hm)
    (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hm) hDpos
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfreeze hcomp)

end Erdos3.VectorPolynomial

end

end OAI
