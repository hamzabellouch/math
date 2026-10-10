import OAI.Geometry.RCD.Sobolev.BoundedGlobalDimensionalBochner
import OAI.Geometry.RCD.Sobolev.PositiveSobolevTestMeasure
import OAI.Geometry.RCD.Sobolev.SobolevTestFunctional
import OAI.Geometry.RCD.Sobolev.SobolevSourceMassBound
import OAI.Geometry.RCD.Sobolev.RadialCutoffNorm

namespace OAI

/-! # Quantitative full Bochner measures on continuous compact Sobolev tests -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_regular_bochner_mass {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0) (p : X)
    (u d G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic d))
    (V : X → ℝ) {L : ℝ≥0} (hV : LipschitzWith L V)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] V)
    (A : ℝ≥0) (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u) :
    ∃ M : ℝ, 0 < M ∧ ∀ R : ℝ, 0 < R → ∃ σ : Measure X, IsFiniteMeasure σ ∧
      (∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (3*R) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm (hausdorff n X) hX.quadratic G ψ-
          K*inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic G)-
          weightedGamma (hausdorff n X) hX.quadratic
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ) u d) ∧
      σ.real (closedBall p R) ≤ M*Real.sqrt
        ((1+R⁻¹^2)*(hausdorff n X).real (closedBall p (2*R))) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hΓ := localGamma_memLp_of_bounded_gradient μ Q u d L
    (SobolevSpace.minimalSlope_le_lipschitz μ Q u hV hu)
  let T := hΓ.toLp (localGamma μ Q u d)
  let H := SobolevSpace.toLp μ Q G
  let ρ := (-K) • H-T
  let q := (-(1/2:ℝ)) • G
  have hformula (ψ : SobolevSpace μ Q) :
      sobolevSourceFunctional μ Q q ρ ψ=-(1/2:ℝ)*energyForm μ Q G ψ-
        K*inner ℝ (SobolevSpace.toLp μ Q ψ) H-
        weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) u d := by
    change energyForm μ Q ((-(1/2:ℝ)) • G) ψ+
      inner ℝ ((-K) • H-T) (SobolevSpace.toLp μ Q ψ)=_
    rw [energyForm_smul_left,inner_sub_left,real_inner_smul_left,
      weightedGamma_eq_L2_inner μ Q u d hΓ,real_inner_comm H,real_inner_comm T]
    ring
  let M := 2*‖q‖+‖ρ‖+1
  refine ⟨M,by dsimp only [M]; positivity,?_⟩
  intro R hR
  let Ω := ball p (3*(3*R)/2)
  let Tψ := compactSobolevTestLift μ Q Ω
  let Φ := (sobolevSourceFunctional μ Q q ρ).comp Tψ
  have hpos (b : compactSobolevTests μ Q Ω) (hb : 0 ≤ (b : X →ᵇ ℝ)) : 0 ≤ Φ b := by
    have htest := hX.bounded_global_dimensional_bochner hn hK p u d G (Tψ b) hd V hV hu A hA hG
      b (b : X →ᵇ ℝ).continuous ‖(b : X →ᵇ ℝ)‖₊
      (fun x => by simpa only [coe_nnnorm,Real.norm_eq_abs] using (b : X →ᵇ ℝ).norm_coe_le_norm x)
      hb (compactSobolevTestLift_coe μ Q Ω b)
    have hnonneg : 0 ≤ (1/(n:ℝ))*(∫ x, (b : X →ᵇ ℝ) x*(SobolevSpace.toLp μ Q d x)^2 ∂μ) :=
      mul_nonneg (by positivity) (integral_nonneg fun x => mul_nonneg (hb x) (sq_nonneg _))
    change 0 ≤ sobolevSourceFunctional μ Q q ρ (Tψ b)
    rw [hformula]
    simpa only [bochnerTestForm_apply,neg_mul,sub_eq_add_neg] using hnonneg.trans htest
  obtain ⟨σ,hσ,hrep⟩ := exists_positive_sobolev_test_measure μ Q p
    (show 0 < 3*R by positivity) Φ hpos
  let := hσ
  have hfull (ψ : SobolevSpace μ Q) (v : X → ℝ) (hv : Continuous v) (hvc : HasCompactSupport v)
      (hvs : tsupport v ⊆ ball p (3*R)) (hψ : SobolevSpace.toLp μ Q ψ =ᵐ[μ] v) :
      (∫ x, v x ∂σ)=sobolevSourceFunctional μ Q q ρ ψ := by
    let vb : X →ᵇ ℝ := ofCompactSupport v hv hvc
    let b : compactSobolevTests μ Q (ball p (3*R)) := ⟨vb,hvc,hvs,ψ,hψ⟩
    let b' : compactSobolevTests μ Q Ω :=
      ⟨vb,hvc,hvs.trans (ball_subset_ball (by linarith)),ψ,hψ⟩
    have he : Tψ b'=ψ := by
      apply Subtype.ext
      apply Lp.ext
      exact (compactSobolevTestLift_coe μ Q Ω b').trans hψ.symm
    have hh := hrep b
    change (∫ x, v x ∂σ)=sobolevSourceFunctional μ Q q ρ (Tψ b') at hh
    rwa [he] at hh
  have hsupp : tsupport (radialCutoff p R) ⊆ ball p (3*R) := by
    apply (show tsupport (radialCutoff p R) ⊆ closedBall p (2*R) from ?_).trans
      (closedBall_subset_ball (by linarith))
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    exact hx (radialCutoff_eq_zero p hR (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hn)))
  have hmass := measure_mass_le_sobolev_source μ Q q (radialSobolevCutoff μ Q p hR) ρ σ
    (S := closedBall p R) measurableSet_closedBall (radialCutoff p R) (radialCutoff_lipschitz p hR).continuous
    (radialCutoff_hasCompactSupport p hR) (fun x => (radialCutoff_bounds p R x).1)
    (fun x hx => by
      rw [radialCutoff_eq_one p hR (by simpa only [dist_comm] using mem_closedBall.mp hx)])
    (hfull _ _ (radialCutoff_lipschitz p hR).continuous (radialCutoff_hasCompactSupport p hR)
      hsupp (radialSobolevCutoff_coe μ Q p hR))
  refine ⟨σ,hσ,fun ψ v hv hvc hvs hψ => (hfull ψ v hv hvc hvs hψ).trans (hformula ψ),hmass.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (radialSobolevCutoff_norm_le μ Q p hR) (by positivity)).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith) (Real.sqrt_nonneg _))

end RegularPointCoordinates

end

end OAI
