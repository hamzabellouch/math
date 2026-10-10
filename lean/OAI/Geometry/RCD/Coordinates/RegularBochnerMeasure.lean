import OAI.Geometry.RCD.Sobolev.BochnerCauchySchwarz
import OAI.Geometry.RCD.Sobolev.CompactBochnerSobolevMeasure
import OAI.Geometry.RCD.Sobolev.SignedTestFunctional
import OAI.Geometry.RCD.Coordinates.LocalPositiveBilinearMeasure
import OAI.Geometry.RCD.Sobolev.AnnularLipschitzCutoff

namespace OAI

/-! # A common full Bochner measure for a finite regular span -/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction BigOperators

noncomputable section
namespace RegularPointCoordinates

private theorem coordinateBilinear_of_form {m : ℕ} (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ) :
    coordinateBilinear (fun i j => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = B := by
  classical
  apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
  intro i
  apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
  intro j
  simp [coordinateBilinear,EuclideanSpace.basisFun_apply]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {m : ℕ}

/-- The scalar RCD Bochner measures polarize to one positive bilinear
measure on the whole regular span. No source derivatives are assumed. -/
theorem NoncollapsedRCD.regular_span_bochner_sobolev_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    {r : ℝ} (hr : 0<r)
    (U : Euclidean m →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 (hausdorff n X))
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (U a) x≤L a)
    (hcompact : ∀ a, ∃ (v : X → ℝ) (Q : ℝ≥0), LipschitzWith Q v ∧ HasCompactSupport v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (U a) =ᵐ[hausdorff n X] v)
    (hD : ∀ a, IsWeakLaplacian (hausdorff n X) hX.quadratic (U a) (D a))
    (hH : ∀ a, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H a a) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (U a) (U a))
    (hsym : ∀ a b, H a b=H b a) :
    ∃ M : PositiveBilinearMeasure X (Euclidean m),
      ∀ (a : Euclidean m) (ψ : SobolevSpace (hausdorff n X) hX.quadratic)
        (q : X →ᵇ ℝ), Continuous (q : X → ℝ) → HasCompactSupport (q : X → ℝ) →
        tsupport q ⊆ ball p r → SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] q →
        (∫ x, q x ∂M.measure a) = regularBochnerForm (hausdorff n X) hX.quadratic K U D H q ψ L hU a a := by
  classical
  let := hX.separable
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  choose v C hv hvc hav using hcompact
  have hscalar (a : Euclidean m) := hX.compact_bochner_sobolev_measure hn (hv a) (hvc a)
    p (U a) (hav a) (D a) (hD a) (H a a) (hH a) (R := 2*r) (by positivity)
  choose σ hσ hσtest using hscalar
  let B (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) := regularBochnerForm μ hQ K U D H q ψ L hU
  have hscalarB (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ)
      (hq : Continuous (q : X → ℝ)) (hqc : HasCompactSupport (q : X → ℝ))
      (hqs : tsupport q ⊆ ball p (2*r)) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q) :
      (∫ x, q x ∂σ a) = B q ψ a a := by
    have ht := hσtest a ψ q hq hqc hqs hψ
    change (∫ x, q x ∂σ a) = bochnerTestForm μ hQ (-K) (H a a) ψ+
      weightedLaplacianPair μ q (D a) (D a)+
      (1/2 : ℝ)*(weightedGamma μ hQ (D a) (U a) ψ+weightedGamma μ hQ (D a) (U a) ψ)
    rw [bochnerTestForm_apply,weightedLaplacianPair_apply]
    have heq : (∫ x, q x*D a x*D a x ∂μ) = ∫ x, q x*(D a x)^2 ∂μ := by
      congr 1
      funext x
      ring
    rw [heq]
    linarith only [ht]
  let e (i : Fin m) : Euclidean m := EuclideanSpace.single i 1
  let s (a : Euclidean m) : SignedMeasure X := @Measure.toSignedMeasure X _ (σ a) (hσ a)
  let A (i j : Fin m) := (1/2 : ℝ) • (s (e i+e j)-s (e i)-s (e j))
  let Q := coordinateBilinear A
  have hA (i j : Fin m) : A i j=A j i := by
    dsimp only [A]
    rw [add_comm (e i) (e j)]
    congr 1
    abel
  have hentry (i j : Fin m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ)
      (hq : Continuous (q : X → ℝ)) (hqc : HasCompactSupport (q : X → ℝ))
      (hqs : tsupport q ⊆ ball p (2*r)) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q) :
      signedTestIntegral q (A i j) = B q ψ (e i) (e j) := by
    have ht (a : Euclidean m) : signedTestIntegral q (s a) = B q ψ a a := by
      have : IsFiniteMeasure (σ a) := hσ a
      change (∫ᵛ x, q x ∂<•(σ a).toSignedMeasure) = _
      rw [VectorMeasure.integral_toSignedMeasure]
      exact hscalarB a ψ q hq hqc hqs hψ
    change signedTestIntegral q ((1/2 : ℝ) • (s (e i+e j)-s (e i)-s (e j))) = _
    simp only [map_smul,map_sub,ht,smul_eq_mul]
    simp only [map_add,LinearMap.add_apply]
    have hb := regularBochnerForm_symmetric μ hQ K U D H q ψ L hU hsym (e j) (e i)
    change B q ψ (e j) (e i)=B q ψ (e i) (e j) at hb
    rw [hb]
    ring
  have htest (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ)
      (hq : Continuous (q : X → ℝ)) (hqc : HasCompactSupport (q : X → ℝ))
      (hqs : tsupport q ⊆ ball p (2*r)) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q) :
      signedTestIntegral q (Q a a) = B q ψ a a := by
    rw [signedTestIntegral_coordinate]
    simp_rw [hentry _ _ ψ q hq hqc hqs hψ]
    have hc := congrArg (fun F : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ => F a a)
      (coordinateBilinear_of_form (B q ψ))
    simpa only [coordinateBilinear_apply,smul_eq_mul] using hc
  have hpos (a : Euclidean m) (q : compactLipschitzTests (ball p (2*r)))
      (hq : 0≤(q : X →ᵇ ℝ)) : 0≤∫ᵛ x, (q : X →ᵇ ℝ) x ∂<•(Q a a) := by
    obtain ⟨C,hC,hqc,hqs⟩ := q.property
    let ψ := compactTestSobolev μ hQ _ q
    have hψ := compactTestSobolev_coe μ hQ _ q
    change 0 ≤ signedTestIntegral (q : X →ᵇ ℝ) (Q a a)
    rw [htest a ψ q hC.continuous hqc hqs hψ,← hscalarB a ψ q hC.continuous hqc hqs hψ]
    exact integral_nonneg hq
  obtain ⟨χ,C,hχ,hχc,hχs,hχb,hχ1⟩ :=
    exists_annular_lipschitz_cutoff p (a := r) (b := 3*r/2) (by linarith)
  let M := positiveBilinearMeasure_of_local_tests Q (coordinateBilinear_symmetric A hA)
    measurableSet_closedBall χ hχ hχc
    (hχs.trans (closedBall_subset_ball (show 3*r/2<2*r by linarith)))
    (fun x => (hχb x).1) hχ1 hpos
  refine ⟨M,?_⟩
  intro a ψ q hq hqc hqs hψ
  rw [← VectorMeasure.integral_toSignedMeasure,M.measure_toSignedMeasure]
  change signedTestIntegral q ((Q a a).restrict (closedBall p r)) = _
  rw [signedTestIntegral_restrict q _ measurableSet_closedBall (hqs.trans ball_subset_closedBall)]
  exact htest a ψ q hq hqc (hqs.trans (ball_subset_ball (by linarith))) hψ


/-- The compact Lipschitz test specialization of the full Sobolev test identity. -/
theorem NoncollapsedRCD.regular_span_bochner_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    {r : ℝ} (hr : 0<r)
    (U : Euclidean m →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 (hausdorff n X))
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (U a) x≤L a)
    (hcompact : ∀ a, ∃ (v : X → ℝ) (Q : ℝ≥0), LipschitzWith Q v ∧ HasCompactSupport v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (U a) =ᵐ[hausdorff n X] v)
    (hD : ∀ a, IsWeakLaplacian (hausdorff n X) hX.quadratic (U a) (D a))
    (hH : ∀ a, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H a a) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (U a) (U a))
    (hsym : ∀ a b, H a b=H b a) :
    ∃ M : PositiveBilinearMeasure X (Euclidean m),
      ∀ (a : Euclidean m) (ψ : SobolevSpace (hausdorff n X) hX.quadratic)
        (q : X →ᵇ ℝ) (C : ℝ≥0), LipschitzWith C q → HasCompactSupport (q : X → ℝ) →
        tsupport q ⊆ ball p r → SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] q →
        (∫ x, q x ∂M.measure a) = regularBochnerForm (hausdorff n X) hX.quadratic K U D H q ψ L hU a a := by
  obtain ⟨M,hM⟩ := hX.regular_span_bochner_sobolev_measure hn p hr U D H L hU hcompact hD hH hsym
  exact ⟨M,fun a ψ q C hq hqc hqs hψ => hM a ψ q hq.continuous hqc hqs hψ⟩

end RegularPointCoordinates

end

end OAI
