import OAI.Geometry.SurfaceImmersion.Correction.AtlasCorrectionAssembly
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteCatalogCancellation

namespace OAI

/-! Assemble actual local supported corrections. Atlas constants are chosen before the phase family and its cardinality. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance catalogAtlasCancellationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance catalogAtlasCancellationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance catalogAtlasCancellationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance catalogAtlasCancellationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance catalogAtlasCancellationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance catalogAtlasCancellationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_catalog_atlas_cancellation
    (Γ : A.centers → Finset (SmallModes.Base → ℝ))
    (hΓ : ∀ i φ, φ ∈ Γ i → ContDiff ℝ ∞ φ)
    {ε b D : ℝ} (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B : ℕ → ℝ → ℝ) (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
      ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : (i : A.centers) → ι i → SmallModes.Base → ℝ),
      (∀ i j, φ i j ∈ Γ i) →
      ∀ K : (i : A.centers) → ι i → TopologicalSpace.Compacts SmallModes.Base,
      (∀ i j, (K i j : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        ε*‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖ ≤
          ‖PhaseGeometry.secondQuadratic
            (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
            (-(phaseDerivative (φ i j) y).2,(phaseDerivative (φ i j) y).1)‖) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (K i j),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (E m*x^(d m)*(∑ i : A.centers, ∑ j, supportedWeightedSeminorm (K i j) s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(E m*x^(d m))*(∑ i : A.centers, ∑ j,
            supportedWeightedSeminorm (K i j) s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i y => ∑ j,
              QuadraticMean.displacement τ (φ i j) (target i j) y))) := by
  classical
  choose e C hC solve using fun i : A.centers =>
    PhaseGeometry.finite_catalog_polynomial_cancellation (Γ i) (hΓ i)
      (modeSupport (A.chartWeightCompact i)) hε hb hD hDB B hB hB1 q
  obtain ⟨Dv,Dt,hDv,hDt,assemble⟩ := A.uniform_local_correction_assembly
  let S := fun m x => ∑ i : A.centers, C i m*x^(e i m)
  have hS (m : ℕ) : RealModes.HasPolynomialBound (S m) :=
    RealModes.HasPolynomialBound.sum Finset.univ
      (fun i : A.centers => fun x => C i m*x^(e i m)) (fun i _ =>
        (RealModes.polynomialBound_const (zero_le_one.trans (hC i m))).mul
          (RealModes.polynomialBound_id.pow (e i m)))
  let H := fun m x => (Dv m+Dt m+1)*S m x
  have hH (m : ℕ) : RealModes.HasPolynomialBound (H m) :=
    (RealModes.polynomialBound_const (by linarith [hDv m,hDt m])).mul (hS m)
  choose d E hE hpoly using hH
  have hSn (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ S m x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (zero_le_one.trans (hC i m))
      (pow_nonneg (zero_le_one.trans hx) _))
  have hlocal (i : A.centers) (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : C i m*x^(e i m) ≤ S m x :=
    Finset.single_le_sum (fun j _ => mul_nonneg (zero_le_one.trans (hC j m))
      (pow_nonneg (zero_le_one.trans hx) (e j m))) (Finset.mem_univ i)
  have hrestore (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
      Dv m*S m x ≤ E m*x^(d m) ∧ Dt m*S m x ≤ E m*x^(d m) := by
    constructor
    · exact (mul_le_mul_of_nonneg_right (by linarith [hDt m] : Dv m ≤ Dv m+Dt m+1)
        (hSn m x hx)).trans (hpoly m x hx).2
    · exact (mul_le_mul_of_nonneg_right (by linarith [hDv m] : Dt m ≤ Dv m+Dt m+1)
        (hSn m x hx)).trans (hpoly m x hx).2
  refine ⟨d,E,hE,?_⟩
  intro ι inst x hx F hF φ hφ K hK hImm hnormal hrel hgram τ s hτ hs hτs hs1 hFj target
  have hsolve (i : A.centers) (j : ι i) := solve i x hx (φ i j) (hφ i j)
    (A.jetChartMap_smooth i hF) (K i j) (hK i j)
    (by simpa only [A.jetChartMap_plane] using hImm i j)
    (by simpa only [A.jetChartMap_plane] using hnormal i j)
    (by simpa only [A.jetChartMap_plane] using hrel i j)
    (by simpa only [A.jetChartMap_plane] using hgram i j)
    τ s hτ hs hτs hs1 (by simpa only [A.jetChartMap_plane] using hFj i) (target i j)
  choose X hX hsp hv hr using hsolve
  let N := fun i (j : ι i) m => supportedWeightedSeminorm (K i j) s
    (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)
  let Cv := fun i (j : ι i) m => S m x*N i j m
  let Ct := fun i (j : ι i) m => (τ/s)^(q+1)*S m x*N i j m
  have hη : 0 ≤ (τ/(s : ℝ))^(q+1) := pow_nonneg (div_nonneg hτ.le hs.le) _
  have hnv (i : A.centers) (j : ι i) (m : ℕ) : 0 ≤ Cv i j m :=
    mul_nonneg (hSn m x hx) (apply_nonneg _ _)
  have hnt (i : A.centers) (j : ι i) (m : ℕ) : 0 ≤ Ct i j m :=
    mul_nonneg (mul_nonneg hη (hSn m x hx)) (apply_nonneg _ _)
  obtain ⟨W,hW,hvW,hrW⟩ := assemble F hF φ (fun i j => hΓ i _ (hφ i j)) K hK
    τ hτ (hτs.trans hs1) X hX hsp target Cv Ct hnv hnt
    (fun i j m => (hv i j m).mono_const
      (mul_le_mul_of_nonneg_right (hlocal i m x hx) (apply_nonneg _ _)))
    (fun i j m => (by
      have hh := hr i j m
      simp only [A.jetChartMap_plane] at hh
      exact hh.mono_const (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlocal i m x hx) hη) (apply_nonneg _ _))))
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    apply (hvW m k).mono_const
    have he : (∑ i : A.centers, ∑ j, Cv i j m) = S m x*(∑ i : A.centers, ∑ j, N i j m) := by
      simp only [Cv,Finset.mul_sum]
    rw [he,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrestore m x hx).1
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => apply_nonneg _ _)))
  · intro m k
    apply (hrW m k).mono_const
    have he : (∑ i : A.centers, ∑ j, Ct i j m) =
        ((τ/s)^(q+1)*S m x)*(∑ i : A.centers, ∑ j, N i j m) := by
      simp only [Ct,Finset.mul_sum]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (hrestore m x hx).2 hη
    have hnorm : 0 ≤ ∑ i : A.centers, ∑ j : ι i, N i j m :=
      Finset.sum_nonneg (fun (i : A.centers) _ =>
        Finset.sum_nonneg (fun (j : ι i) _ => (show 0 ≤ N i j m from apply_nonneg _ _)))
    convert mul_le_mul_of_nonneg_right hh hnorm using 1; ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
