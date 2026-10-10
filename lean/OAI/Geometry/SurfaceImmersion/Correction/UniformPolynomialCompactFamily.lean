import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseFamily
import OAI.Geometry.SurfaceImmersion.Correction.UniformPolynomialPhasePrefix
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! Fixed finite good-phase covers provide the perturbed polynomial solvers. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem CompactPhaseFamily.uniform_polynomial_solvers_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (KU : Compacts JetPolynomial.Base)
    (hUK : U ⊆ KU) (hKU : (jetSupport K : Set JetPolynomial.Base) ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℕ → ℝ, (∀ m, 0 ≤ R m) →
    ∃ C D J I : a.centers → ℕ → ℝ,
      (∀ i m, 0 ≤ C i m) ∧ (∀ i m, 0 ≤ D i m) ∧
      (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ I i m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G) (B : ℝ),
      0 ≤ B → B < ρ → WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ ε : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : (i : a.centers) → PolynomialSolveData P ε G hG φ (a.support i) τ s,
        (∀ i, (c i).C = C i) ∧ (∀ i, (c i).D = D i) ∧ (∀ i, (c i).J = J i) ∧
        ∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
          ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I i m := by
  classical
  have hs (i : a.centers) : (a.support i : Set JetPolynomial.Base) ⊆ U := by
    intro x hx
    apply hKU
    have hp : planeCoordinateIsometry x ∈ (K : Set SmallModes.Base) :=
      a.support_subset i ⟨x,hx,rfl⟩
    exact ⟨planeCoordinateIsometry x,hp,planeCoordinateIsometry.symm_apply_apply x⟩
  choose r hr hall using fun i => (a.charts i).uniform_polynomial_solvers_of_prefix_all_profiles
    P hP hF hφ (a.support i) (a.support_chart i) hU KU hUK (hs i)
  obtain ⟨ρ,hρ,_,hρr⟩ := finite_positive_threshold r hr
  refine ⟨ρ,hρ,?_⟩
  intro R hR
  choose C D J I hC hD hJ hI hsolve using fun i => hall i R hR
  refine ⟨C,D,J,I,hC,hD,hJ,hI,?_⟩
  intro G hG B hB hBρ hb τ ε s hτ hs hτs hs1 hε hε1 hp
  choose c _ hc hd hj hi using fun i => hsolve i G hG B hB (hBρ.trans_le (hρr i))
    hb τ ε s hτ hs hτs hs1 hε hε1 hp
  exact ⟨c,hc,hd,hj,hi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
