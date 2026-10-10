import OAI.Geometry.SurfaceImmersion.Correction.InputAtlasFreeQuadraticCorrection
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeResidual
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasIncrementBound
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds

namespace OAI

/-! Assemble a uniform nearby-map increment from fixed profiles and an adjusted mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance inputSmallAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputSmallAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputSmallAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputSmallAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputSmallAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputSmallAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem input_atlas_small_increment_fixed_phase
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
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {n : A.centers → ℕ}
        {P : (k : A.centers) → Fin 3 → Fin (n k) → JetPolynomial.Expression}
        (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ),
      ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
      (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
    (C E : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (_hE : ∀ m, 0 ≤ E m) (q : ℕ),
    ∃ B T : ℕ → ℝ,
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ {τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ τ → ∀ u H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      (∀ m, A.TensorWeightedBound τ m (E m*δ^2*(τ/s)^(q+1))
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (G+X) - inducedTensor G - δ^2 • H)) := by
  classical
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_atlas_free_quadratic_correction_fixed_phase F hF φ hφ hImm hgood
  refine ⟨ρ₀,hρ₀,?_⟩
  intro n P p ρ R hρ r reference D hD C E hC hE q
  let N := fun m => Finset.univ.sup
    (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose Af hAf hfree using fun m => A.uniform_atlas_free_size p hρ r reference q m (C (N m)) (hC (N m))
  choose Ef hEf hfreeRes using fun m => A.uniform_atlas_free_residual p hρ r reference q m (C (N m)) (hC (N m))
  obtain ⟨Cv,Ct,hCv,hCt,hcorr⟩ := hall p hρ r reference D hD C hC q
  let L : ℝ := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  choose D hD hincrement using fun m => A.atlas_free_forced_increment_bound m
    (L*Af (m+1)) (L*Cv (m+1))
    (mul_nonneg hL (zero_le_one.trans (hAf (m+1)))) (mul_nonneg hL (hCv (m+1)))
  let B := fun m => L*(Af m+Cv m)
  let T := fun m => Ef m+Ct m+E m+D m
  have hB (m) : 0 ≤ B m := mul_nonneg hL (add_nonneg (zero_le_one.trans (hAf m)) (hCv m))
  have hT (m) : 0 ≤ T m := by
    dsimp [T]
    exact add_nonneg (add_nonneg (add_nonneg (zero_le_one.trans (hEf m)) (hCt m)) (hE m)) (hD m)
  refine ⟨B,T,hB,hT,?_⟩
  intro G hG b hb hbρ hclose τ s d hfit hphase hdG hτ hs hτs hs1 hd hK δ hδ hδτ u H hu hH hball hbu hmean
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hη : τ/s ≤ 1 := (div_le_one₀ hs).mpr hτs
  obtain ⟨W,hW,hwsize,hwres⟩ := hcorr G hG b hb hbρ hclose d hfit hphase hτ hs hτs hs1 hd hK δ hδ u hu hball hbu
  let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
  let V := spaceCoordinates.symm ∘ W
  have hUr := A.atlasFreeOscillation_smooth d hρ δ q u
  have hU : ContMDiff planeModel spaceModel ∞ U := spaceCoordinates.symm.contDiff.contMDiff.comp hUr
  have hV : ContMDiff planeModel spaceModel ∞ V := spaceCoordinates.symm.contDiff.contMDiff.comp hW
  have hbU (m) : A.WeightedBound τ m ((L*Af m)*(δ*τ)) U := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hUr hτ.le
      (hfree m d hfit hτ hs hτs hs1 (le_refl 0)
        (by simpa only [zero_div,add_zero] using hη) δ hδ u hu hball (hbu (N m)))
    convert hh using 1 <;> dsimp [U,L]
    all_goals ring
  have hbV (m) : A.WeightedBound τ m ((L*Cv m)*δ^2) V := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hW hτ.le (hwsize m)
    convert hh using 1 <;> dsimp [V,L]
    all_goals ring
  have hlin (m) : A.TensorWeightedBound τ m (Ef m*(δ*τ)*(τ/s)^(q+1)) (linearMetricTensor G U) :=
    hfreeRes m G hG d hdG hfit hτ hs hτs hs1 hK δ hδ u hu hball (hbu (N m))
  refine ⟨U+V,hU.add hV,?_,?_⟩
  · intro m k
    apply ((A.weightedBound_add hU hV hτ.le (hbU m) (hbV m)) k).mono_const
    have hsmall : δ^2 ≤ δ*τ := by nlinarith
    calc
      (L*Af m)*(δ*τ)+(L*Cv m)*δ^2 ≤ (L*Af m)*(δ*τ)+(L*Cv m)*(δ*τ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall (mul_nonneg hL (hCv m)))
      _ = B m*(δ*τ) := by dsimp [B]; ring
  · intro m k
    have hforced : A.TensorWeightedBound τ m (Ct m*δ^2*(τ/s)^(q+1))
        (linearMetricTensor G V + A.atlasFreeQuadraticOscillation d hρ δ q u) := by
      convert hwres m using 1
      ring
    have hh := hincrement m d hρ δ q u hK G V hG hV H hH hτ hτ1 hδ hδτ
      (Ef m*(δ*τ)*(τ/s)^(q+1)) (Ct m*δ^2*(τ/s)^(q+1)) (E m*δ^2*(τ/s)^(q+1))
      (hbU (m+1)) (hbV (m+1)) (hlin m) hforced (hmean m)
    apply (hh k).mono_const
    have hd1 : δ ≤ 1 := hδτ.trans hτ1
    have hdt : δ*τ ≤ δ := mul_le_of_le_one_right hδ hτ1
    have hd2 : δ^2 ≤ δ := by nlinarith
    have hp : 0 ≤ (τ/s)^(q+1) := pow_nonneg (div_nonneg hτ.le hs.le) _
    have hx : 0 ≤ δ^3/τ := by positivity
    calc
      Ef m*(δ*τ)*(τ/s)^(q+1) + Ct m*δ^2*(τ/s)^(q+1) + E m*δ^2*(τ/s)^(q+1) + D m*(δ^3/τ)
          ≤ (Ef m+Ct m+E m)*(δ*(τ/s)^(q+1))+D m*(δ^3/τ) := by
        have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdt (zero_le_one.trans (hEf m))) hp
        have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 (hCt m)) hp
        have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 (hE m)) hp
        nlinarith only [h1,h2,h3]
      _ ≤ T m*(δ*(τ/s)^(q+1)+δ^3/τ) := by
        dsimp [T]
        have hmain : 0 ≤ δ*(τ/s)^(q+1) := mul_nonneg hδ hp
        have hsum : 0 ≤ Ef m+Ct m+E m := add_nonneg (add_nonneg (zero_le_one.trans (hEf m)) (hCt m)) (hE m)
        nlinarith [mul_nonneg (hD m) hmain,mul_nonneg hsum hx]

theorem input_atlas_small_increment
    {n : A.centers → ℕ} {P : (k : A.centers) → Fin 3 → Fin (n k) → JetPolynomial.Expression}
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r r₀ : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 (r₀ i) ρ R (reference i))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x))
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (C E : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hE : ∀ m, 0 ≤ E m) (q : ℕ) :
    ∃ (ρ₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ {τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ i, (d i).phase = (d₀ i).phase) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ τ → ∀ u H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      (∀ m, A.TensorWeightedBound τ m (E m*δ^2*(τ/s)^(q+1))
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (G+X) - inducedTensor G - δ^2 • H)) := by
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_atlas_small_increment_fixed_phase F hF
    (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2)
    (fun a => A.freeGlobalPhase_smooth d₀ a.1 a.2) hImm hgood
  obtain ⟨B,T,hB,hT,hstep⟩ := hall p hρ r reference D hD C E hC hE q
  refine ⟨ρ₀,B,T,hρ₀,hB,hT,?_⟩
  intro G hG b hb hbρ hclose τ s d hfit hphase hdG hτ hs hτs hs1 hd hK δ hδ hδτ u H
    hu hH hball hbu hmean
  apply hstep G hG b hb hbρ hclose d hfit ?_ hdG hτ hs hτs hs1 hd hK δ hδ hδτ u H
    hu hH hball hbu hmean
  intro a
  unfold freeGlobalPhase
  rw [hphase a.1]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
