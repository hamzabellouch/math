import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFiniteAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialTensorMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorSymmetricMean

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialFiniteTrialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFiniteTrialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFiniteTrialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFiniteTrialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialFiniteTrialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFiniteTrialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


theorem polynomial_finite_atlas_trial (q : ℕ) (B H Y : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hH : ∀ m, HasPolynomialBound (H m))
    (hY : ∀ m, HasPolynomialBound (Y m)) :
    ∃ e : ℕ, ∃ E : ℝ, ∃ S T : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (S m)) ∧ (∀ m, HasPolynomialBound (T m)) ∧
    ∀ x : ℝ, 1 ≤ x →
    ∀ (reference : ∀ y : M, CovariantTwoTensor y),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (reference y)) →
    ∀ r : ℝ, 0 < r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {ρ R : ℝ}
      (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R
        (A.tensorPlaneRead i reference)),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, 1 ≤ H m x) → (∀ m, 1 ≤ Y m x) →
      (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m x ∧ ρ⁻¹ ≤ H m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.chi m ≤ B m x ∧
        (d i j).budgets.forms m ≤ B m x ∧ (d i j).budgets.pull m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ B m x ∧
        (d i j).budgets.mode m ≤ B m x) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*x^e))) →
      ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v w, f y v w = f y w v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode reference y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m x) f) →
      ∀ δ : ℝ, 0 < δ → ∃ u : ∀ y : M, CovariantTwoTensor y,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
          (fun y => TotalSpace.mk' TensorFiber y (u y)) ∧
        (∀ y v w, u y v w = u y w v) ∧
        FiniteMean.InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
        (∀ i, FiniteMean.InTrialBall univ (A.tensorPlaneRead i reference)
          (A.tensorReadBallConstant*r) (A.tensorPlaneRead i u)) ∧
        (∀ m, A.TensorWeightedBound s m (S m x) u) ∧
        (∀ m, A.TensorWeightedBound s m (T m x*(τ/s)^(q+1))
          (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) := by
  classical
  obtain ⟨p,C,D,E,hC,hD,hE,hmean⟩ := A.polynomial_finite_atlas_mean q
  let p' := fun m => 2*p m+2
  let C' := fun m => 1+C m
  let Z := fun m x => transportedMeanGeometry (q+2)
    (meanGeometryEnvelope q (fun j => H j x) (fun j => B j x)) D E m
  have hC' (m : ℕ) : 0 ≤ C' m := by dsimp [C']; linarith [hC m]
  have hZ (m : ℕ) : HasPolynomialBound (Z m) :=
    transportedMeanGeometry_growth (q+2)
      (fun m x => meanGeometryEnvelope q (fun j => H j x) (fun j => B j x) m)
      (fun m _ => D m) (fun m _ => E m)
      (meanGeometryEnvelope_growth q H B hH hB)
      (fun m => polynomialBound_const (zero_le_one.trans (hD m)))
      (fun m => polynomialBound_const (hE m)) m
  obtain ⟨e,A₀,hA₀,htrial⟩ := A.polynomial_tensor_mean_threshold (q+2) p' C' Z Y hC' hZ hY q
  let S := polynomialMeanSize (q+2) p' C' Z Y q
  let T := polynomialMeanDifference (q+2) p' C' Z Y q
  have hS (m : ℕ) : HasPolynomialBound (S m) :=
    polynomialMeanSize_growth (q+2) p' C' Z Y hC' hZ hY q m
  have hT (m : ℕ) : HasPolynomialBound (T m) :=
    polynomialMeanDifference_growth (q+2) p' C' Z Y hC' hZ hY q m
  refine ⟨e,A₀,S,T,hA₀,hS,hT,?_⟩
  intro x hx reference href r hr ι _ n P G hG φ K τ s c ρ R d hρ hτ hs hτs hs1
    hHx hYx hcard hbud hsmall f hf hsym hnear hsize δ hδ
  have hBx (m : ℕ) : 0 ≤ B m x := by
    obtain ⟨_,_,_,hh⟩ := hB m
    exact (hh x hx).1
  let μ := A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q)
  have hm := hmean reference href r hr.le d hρ hτ hs hτs hs1
    (fun m => H m x) (fun m => B m x) hHx hBx hcard hbud δ hδ
  have ht := htrial x hx hs reference f hf (r/2) r (by linarith)
    hnear hYx hsize (τ/s) (div_pos hτ hs) hsmall μ hm q le_rfl
  let u := A.tensorMeanTrial f μ q
  have hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun y => TotalSpace.mk' TensorFiber y (u y)) := ht.1
  have hb := ht.2.1
  have hlocal (i : A.centers) := A.tensorReadBallConstant_ball reference href
    (A.tensorEncode u) r hr.le (A.tensorEncode_smooth hu) hb i
  simp only [A.tensorDecode_encode] at hlocal
  exact ⟨u,hu,A.tensorMeanTrial_symmetric f μ hsym
    (fun v _ => A.atlasMean_symmetric _ v) q,hb,hlocal,ht.2.2.1,ht.2.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
