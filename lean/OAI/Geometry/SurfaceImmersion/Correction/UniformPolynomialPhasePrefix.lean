import OAI.Geometry.SurfaceImmersion.Correction.UniformPolynomialPhaseSolver
import OAI.Geometry.SurfaceImmersion.Geometry.LocalIsometryBounds

namespace OAI

/-! Polynomial phase solvers from the shifted derivative bounds of the iteration. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem GoodPhaseChart.uniform_polynomial_solvers_of_prefix_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ))
    (K : Compacts JetPolynomial.Base) (hK : (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source)
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (KU : Compacts JetPolynomial.Base)
    (hUK : U ⊆ KU) (hKU : (K : Set JetPolynomial.Base) ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℕ → ℝ, (∀ m, 0 ≤ R m) →
    ∃ C D J I : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 0 ≤ D m) ∧
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ I m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G) (B : ℝ),
      0 ≤ B → B < ρ → WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ ε : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : PolynomialSolveData P ε G hG φ K τ s,
        c.e = e.chart ∧ c.C = C ∧ c.D = D ∧ c.J = J ∧
        ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ c.e.target,
          ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I m := by
  obtain ⟨ρ,hρ,hall⟩ := e.uniform_polynomial_solvers_all_profiles P hP hF hφ K hK hU KU hUK hKU
  refine ⟨ρ,hρ,?_⟩
  intro R hR
  choose E hE he using fun m => compact_realTwoJet_comp_prefix_bound e.smoothInverse
    e.targetCompact e.chart.open_target e.targetBound m
  let H := fun m => 1+E m*R m
  have hH (m) : 1 ≤ H m := le_add_of_nonneg_right
    (mul_nonneg (zero_le_one.trans (hE m)) (hR m))
  obtain ⟨Q,C,D,J,I,_,hC,hD,hJ,hI,hsolve⟩ := hall H R hH hR
  refine ⟨C,D,J,I,hC,hD,hJ,hI,?_⟩
  intro G hG B hB hBρ hb τ ε s hτ hs hτs hs1 hε hε1 hp
  have hjet (m) : WeightedBound e.chart.target s (m+1) (H (m+1))
      (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘ e.chart.symm)) := by
    apply (he (m+1) (G ∘ planeCoordinateIsometry.symm)
      (hG.comp planeCoordinateIsometry.symm.contDiff) s (R (m+1)) hs hs1 (hR _) (hp _)).mono_const
    exact le_add_of_nonneg_left zero_le_one
  have hpref (m j) (hj : j ≤ m+2) : WeightedBound U 1 j (R m/(s:ℝ)^(j-2)) G := by
    have hh := weightedBound_comp_isometry planeCoordinateIsometry
      (hG.comp planeCoordinateIsometry.symm.contDiff) (hp m j hj)
    have hcomp : (G ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = G := by
      funext x
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    rw [hcomp] at hh
    exact hh.restrict_open hU
  obtain ⟨_,c,_,_,heq,hc,hd,hj,hi⟩ :=
    hsolve G hG B hB hBρ hb s hs hs1 hjet hpref τ ε hτ hτs hε hε1
  exact ⟨c,heq,hc,hd,hj,hi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
