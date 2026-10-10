import OAI.Geometry.RCD.Sobolev.WeakLaplacianOperator
import OAI.Geometry.RCD.Coordinates.RegularBochnerMeasure
import OAI.Geometry.RCD.Coordinates.RegularDirichletCore
import OAI.Geometry.RCD.Sobolev.CompactMixedEnergy
import OAI.Geometry.RCD.Sobolev.FiniteEnergyRepresentatives

namespace OAI

/-! # The actual Laplacian and Gram representatives of a regular finite span -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Every finite family in the proved regular test core has a common
linear Laplacian and a symmetric Sobolev Gram form. -/
theorem NoncollapsedRCD.regular_finite_span {K : ℝ} {n m : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    {Ω : Set X} (u : Fin m → compactLaplacianCore (hausdorff n X) hX.quadratic Ω) :
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val)
    ∃ (D : Euclidean m →L[ℝ] Lp ℝ 2 (hausdorff n X))
      (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (L : Euclidean m → ℝ≥0),
      (∀ a, ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (U a) x≤L a) ∧
      (∀ a, ∃ (v : X → ℝ) (Q : ℝ≥0), LipschitzWith Q v ∧ HasCompactSupport v ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (U a) =ᵐ[hausdorff n X] v) ∧
      (∀ a, IsWeakLaplacian (hausdorff n X) hX.quadratic (U a) (D a)) ∧
      (∀ a b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H a b) =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic (U a) (U b)) ∧
      (∀ a b, H a b=H b a) := by
  classical
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let U := sobolevColumnMap μ hQ (fun i => (u i).val)
  have hmem (a : Euclidean m) : U a ∈ compactLaplacianCore μ hQ Ω := by
    rw [sobolevColumnMap_apply]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (u i).property)
  let V : Euclidean m →ₗ[ℝ] weakLaplacianDomain μ hQ :=
    U.toLinearMap.codRestrict _ (fun a => (hmem a).2)
  let D := ((weakLaplacianOperator μ hQ).comp V).toContinuousLinearMap
  have hD (a : Euclidean m) : IsWeakLaplacian μ hQ (U a) (D a) :=
    weakLaplacianOperator_spec μ hQ (V a)
  have hc (a : Euclidean m) : ∃ (v : X → ℝ) (Q : ℝ≥0), LipschitzWith Q v ∧
      HasCompactSupport v ∧ SobolevSpace.toLp μ hQ (U a) =ᵐ[μ] v := by
    obtain ⟨v,Q,hv,hvc,-,hvr⟩ := (hmem a).1
    exact ⟨v,Q,hv,hvc,hvr⟩
  choose v L hv hvc hvr using hc
  have hL (a : Euclidean m) : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a :=
    SobolevSpace.minimalSlope_le_lipschitz μ hQ (U a) (hv a) (hvr a)
  let e (i : Fin m) : Euclidean m := EuclideanSpace.single i 1
  have hentry (i j : Fin m) : ∃ G : SobolevSpace μ hQ,
      SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ (U (e i)) (U (e j)) :=
    hX.compact_mixed_energy hn p (U (e i)) (U (e j)) (hv (e i)) (hvc (e i)) (hvr (e i))
      (hv (e j)) (hvc (e j)) (hvr (e j)) (D (e i)) (D (e j)) (hD (e i)) (hD (e j))
  choose G hG using hentry
  let H := coordinateBilinear G
  have hH (a b : Euclidean m) : SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ]
      localGamma μ hQ (U a) (U b) := by
    simpa only [Measure.restrict_univ] using
      coordinate_energy_representative μ hQ U G (Ω := univ) (by
        intro i j
        simpa only [Measure.restrict_univ] using hG i j) a b
  refine ⟨D,H,L,hL,(fun a => ⟨v a,L a,hv a,hvc a,hvr a⟩),hD,hH,?_⟩
  intro a b
  apply Subtype.ext
  apply Lp.ext
  exact (hH a b).trans ((localGamma_comm μ hQ (U a) (U b)).trans (hH b a).symm)

end RegularPointCoordinates

end

end OAI
