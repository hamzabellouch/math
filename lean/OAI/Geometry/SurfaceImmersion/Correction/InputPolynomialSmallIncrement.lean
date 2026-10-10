import OAI.Geometry.SurfaceImmersion.Correction.InputPolynomialFreeCorrection
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialFreeResidual
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialIncrementBound
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialNonlinearProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedIncrementEstimate
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds

namespace OAI

/-! Assemble a uniform nearby-map increment from fixed profiles and an adjusted mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance polynomialSmallAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSmallAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialSmallAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSmallAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialSmallAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSmallAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem input_polynomial_small_increment_fixed_phase
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : A.centers × Fin 3 → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          φ k l)) x))
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ∀ i, Fin 3 → ChartedMeanProfile (Q i)) {ρ R : ℝ} (hρ : 0 < ρ),
      ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
      (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
    (C E : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (_hE : ∀ m, 0 ≤ E m) (q : ℕ),
    ∃ B T : ℕ → ℝ,
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Q i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      (∀ m, A.TensorWeightedBound τ m (E m*δ^2*η^(q+1))
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*η^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  classical
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_polynomial_free_correction_fixed_phase Pol Q hQ hquad hlin
    F hF φ hφ hImm hgood Ω hΩ KΩ hΩK hweight
  refine ⟨ρ₀,hρ₀,?_⟩
  intro p ρ R hρ r reference D hD C E hC hE q
  let N := fun m => Finset.univ.sup
    (fun i : A.centers => PolynomialSolveData.inputOrder (P := Q i) q m)
  choose Af hAf hfree using fun m => A.uniform_atlas_free_size p hρ r reference q m (C (N m)) (hC (N m))
  choose Ef hEf hfreeRes using fun m => A.uniform_atlas_polynomial_free_residual Pol Q hQ hlin
    p hρ r reference q m (C (N m)) (hC (N m))
  obtain ⟨Cv,Ct,hCv,hCt,hcorr⟩ := hall p hρ r reference D hD C hC q
  let L : ℝ := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let A₀ := fun m => L*Af m
  let B₀ := fun m => L*Cv m
  have hA₀ (m) : 0 ≤ A₀ m := mul_nonneg hL (zero_le_one.trans (hAf m))
  have hB₀ (m) : 0 ≤ B₀ m := mul_nonneg hL (hCv m)
  obtain ⟨E₁,E₂,hE₁,hE₂,hnonlinear⟩ := A.atlas_polynomial_nonlinear_profiles Pol hPol
    Ω hΩ KΩ hΩK houter D A₀ B₀ hD hA₀ hB₀
  choose Dm hDm hincrement using fun m => A.atlas_polynomial_increment_bound m
    (A₀ (m+1)) (B₀ (m+1)) (hA₀ (m+1)) (hB₀ (m+1))
  let B := fun m => A₀ m+B₀ m
  let T := fun m => Ef m+Ct m+E m+Dm m+E₁ m+E₂ m
  have hB (m) : 0 ≤ B m := add_nonneg (hA₀ m) (hB₀ m)
  have hT (m) : 0 ≤ T m := by
    dsimp [T]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (zero_le_one.trans (hEf m)) (hCt m)) (hE m)) (hDm m)) (hE₁ m)) (hE₂ m)
  refine ⟨B,T,hB,hT,?_⟩
  intro G hG b hb hbρ hclose ε τ s d hfit hphase hdG hτ hs hτs hs1 hε hε1
    η hη hη1 hsmall hd hK δ hδ hδτ u H hu hH hball hbu hmean
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  let loss := max (Finset.univ.sup (fun i : A.centers => tensorLoss (Q i)))
    (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))
  have hle (k : ℕ) (hk : k ≤ loss) : τ/s+ε/τ^k ≤ η := by
    apply le_trans _ hsmall
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    exact pow_le_pow_of_le_one hτ.le hτ1 hk
  have hQsmall (i) : τ/s+ε/τ^tensorLoss (Q i) ≤ η := hle _
    ((Finset.le_sup (f := fun i : A.centers => tensorLoss (Q i)) (Finset.mem_univ i)).trans (le_max_left _ _))
  have hPsmall (i) : ε/τ^tensorLoss (Pol i) ≤ 1 := by
    have hh := hle _ ((Finset.le_sup (f := fun i : A.centers => tensorLoss (Pol i))
      (Finset.mem_univ i)).trans (le_max_right _ _))
    linarith [div_nonneg hτ.le hs.le]
  have hfreeSmall : τ/s+ε/τ^(Finset.univ.sup (fun i : A.centers => tensorLoss (Q i))) ≤ 1 :=
    (hle _ (le_max_left _ _)).trans hη1
  obtain ⟨W,hW,hwsize,hwres⟩ := hcorr G hG b hb hbρ hclose d hfit hphase hdG hτ hs hτs hs1
    hε hε1 η hη hη1 hQsmall hd hK δ hδ u hu hball hbu
  let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
  let V := spaceCoordinates.symm ∘ W
  have hUr := A.atlasFreeOscillation_smooth d hρ δ q u
  have hU : ContMDiff planeModel spaceModel ∞ U := spaceCoordinates.symm.contDiff.contMDiff.comp hUr
  have hV : ContMDiff planeModel spaceModel ∞ V := spaceCoordinates.symm.contDiff.contMDiff.comp hW
  have hbU (m) : A.WeightedBound τ m (A₀ m*(δ*τ)) U := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hUr hτ.le
      (hfree m d hfit hτ hs hτs hs1 hε hfreeSmall δ hδ.le u hu hball (hbu (N m)))
    convert hh using 1 <;> dsimp [U,A₀,L]
    all_goals ring
  have hbV (m) : A.WeightedBound τ m (B₀ m*δ^2) V := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hW hτ.le (hwsize m)
    convert hh using 1 <;> dsimp [V,B₀,L]
    all_goals ring
  have hfreeResidual (m) : A.TensorWeightedBound τ m (Ef m*(δ*τ)*η^(q+1))
      (linearMetricTensor G U+A.atlasPolynomialVariation Pol ε G U) :=
    hfreeRes m G hG d hdG hfit hτ hs hτs hs1 hε hη hη1 hQsmall hK δ hδ.le u hu hball (hbu (N m))
  obtain ⟨hinter,hremainder⟩ := hnonlinear G U V hG hU hV s τ ε δ hτ hs hτs hs1
    hε hε1 hδ hδτ hPsmall hd hbU hbV
  let H₀ := A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u))
  have hH₀ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H₀ x)) := by
    apply A.tensorPlaneRestore_smooth
    intro i
    exact combinedQuadraticMean_smooth_global (hQ i) (d i).smoothG
      (fun j => ((d i).solver j).smoothPhase)
      (fun j => ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff) ε τ
  refine ⟨U+V,hU.add hV,?_,?_⟩
  · intro m k
    apply ((A.weightedBound_add hU hV hτ.le (hbU m) (hbV m)) k).mono_const
    have hδ2 : δ^2 ≤ δ*τ := by nlinarith
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hδ2 (hB₀ m)]
  · intro m k
    have hforced : A.TensorWeightedBound τ m (Ct m*δ^2*η^(q+1))
        (linearMetricTensor G V+A.atlasPolynomialVariation Pol ε G V+
          (inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U)-H₀) := by
      have hh := hwres m
      have heq : linearMetricTensor G V+A.atlasPolynomialVariation Pol ε G V+
          (inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U-H₀) =
          linearMetricTensor G V+A.atlasPolynomialVariation Pol ε G V+
          (inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U)-H₀ := by abel
      change A.TensorWeightedBound τ m _ (linearMetricTensor G V+
        A.atlasPolynomialVariation Pol ε G V+(inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U-H₀)) at hh
      rw [heq] at hh
      convert hh using 1
      ring
    have hh := hincrement m Pol hPol G U V hG hU hV (δ^2 • H) H₀
      (hH.const_smul_section (a := δ^2)) hH₀ τ ε δ
      (Ef m*(δ*τ)*η^(q+1)) (Ct m*δ^2*η^(q+1)) (E m*δ^2*η^(q+1)) (E₁ m) (E₂ m)
      hτ hτ1 hδ.le hδτ (hbU (m+1)) (hbV (m+1)) (hfreeResidual m) hforced (hmean m)
      (hinter m) (hremainder m)
    apply (hh k).mono_const
    have hδ1 : δ ≤ 1 := hδτ.trans hτ1
    have hδt : δ*τ ≤ δ := mul_le_of_le_one_right hδ.le hτ1
    have hδ2 : δ^2 ≤ δ := by nlinarith
    have hp : 0 ≤ η^(q+1) := pow_nonneg hη _
    have hx : 0 ≤ δ^3/τ := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδt (zero_le_one.trans (hEf m))) hp
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ2 (hCt m)) hp
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ2 (hE m)) hp
    have h4 : 0 ≤ Ef m+Ct m+E m := add_nonneg (add_nonneg (zero_le_one.trans (hEf m)) (hCt m)) (hE m)
    have h5 : 0 ≤ Dm m+E₁ m+E₂ m := add_nonneg (add_nonneg (hDm m) (hE₁ m)) (hE₂ m)
    dsimp [T]
    nlinarith [mul_nonneg h4 hx,mul_nonneg h5 (mul_nonneg hδ.le hp)]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
