import OAI.Geometry.RCD.Sobolev.WeightedBallEnergyLiminf
import OAI.Geometry.RCD.Sobolev.WeightedQuadraticEnergy
import OAI.Geometry.RCD.Sobolev.QuadraticEnergyLimit
import OAI.Geometry.RCD.Sobolev.LocalLipschitzDerivative
import OAI.Geometry.RCD.Sobolev.CorrectionInteriorEnergy

namespace OAI

/-! # Mixed energy convergence from the actual sharp diagonal recoveries -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.weighted_mixed_energy_tendsto {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g ψ : Euclidean n → ℝ) (hg : InteriorSmoothTest n S g) (hψ : InteriorSmoothTest n S ψ)
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (hqconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-ψ (v k x)|≤δ)
    {M Q : ℝ} (hM : 0≤M) (hQ : 0≤Q)
    (hwb : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    (hqb : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤Q)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hs : Function.support φ⊆ball 0 ρ)
    (hwupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
        (∫ x in ball (p k) (S*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X)≤
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 S, φ z*‖fderiv ℝ g z‖^2)+δ)
    (hqupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
        (∫ x in ball (p k) (S*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
          (q k) (q k) x ∂hausdorff n X)≤
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 S, φ z*‖fderiv ℝ ψ z‖^2)+δ) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
        (w k) (q k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, φ z*inner ℝ (gradient g z) (gradient ψ z))) := by
  let μ := hausdorff n X
  obtain ⟨_,_,_,Lg,_,hgL,_,_⟩ := hg.metric_bounds hS
  obtain ⟨_,_,_,L,_,hψL,_,_⟩ := hψ.metric_bounds hS
  have hgi := (local_lipschitz_derivative (show S<S+1 by linarith)
    (fun _ _ => ⟨Lg,hgL.lipschitzOnWith⟩)).2
  have hψi := (local_lipschitz_derivative (show S<S+1 by linarith)
    (fun _ _ => ⟨L,hψL.lipschitzOnWith⟩)).2
  apply cross_tendsto_of_quadratic_lower hwupper hqupper
  intro t δ hδ
  let F := fun k => w k+t • q k
  have hFconv (W : ℝ) (hW : 0<W) (hWS : W<S) (δ : ℝ) (hδ : 0<δ) :
      ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hX.quadratic (F k) x-(g (v k x)+t*ψ (v k x))|≤δ := by
    let a := δ/(2*(1+|t|))
    have ha : 0<a := div_pos hδ (by positivity)
    filter_upwards [hconv W hW hWS a ha,hqconv W hW hWS a ha] with k hk hqk
    filter_upwards [hk,hqk,ae_restrict_of_ae (Lp.coeFn_add
      (SobolevSpace.toLp μ hX.quadratic (w k))
      (SobolevSpace.toLp μ hX.quadratic (t • q k))),
      ae_restrict_of_ae (Lp.coeFn_smul t (SobolevSpace.toLp μ hX.quadratic (q k)))]
      with x hx hqx hadd hsmul
    have he : SobolevSpace.toLp μ hX.quadratic (F k) x=
        SobolevSpace.toLp μ hX.quadratic (w k) x+t*SobolevSpace.toLp μ hX.quadratic (q k) x := by
      simpa only [F,map_add,map_smul,smul_eq_mul,Pi.add_apply,Pi.smul_apply] using hadd.trans (congrArg
        (fun z => SobolevSpace.toLp μ hX.quadratic (w k) x+z) hsmul)
    rw [he]
    calc
      _ = |(SobolevSpace.toLp μ hX.quadratic (w k) x-g (v k x))+
          t*(SobolevSpace.toLp μ hX.quadratic (q k) x-ψ (v k x))| := by congr 1; ring
      _ ≤ |SobolevSpace.toLp μ hX.quadratic (w k) x-g (v k x)|+
          |t| * |SobolevSpace.toLp μ hX.quadratic (q k) x-ψ (v k x)| :=
        (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ a+|t| * a := add_le_add hx (mul_le_mul_of_nonneg_left hqx (abs_nonneg _))
      _ ≤ δ := by dsimp only [a]; field_simp; nlinarith [abs_nonneg t]
  have hFlip : ∀ W<S, ∃ B : ℝ≥0, LipschitzOnWith B (fun y => g y+t*ψ y) (closedBall 0 W) := by
    intro W hWS
    exact ⟨_,hgL.lipschitzOnWith.add ((lipschitzWith_smul t).comp hψL).lipschitzOnWith⟩
  have hFb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma μ hX.quadratic (F k) (F k) x≤2*M+2*t^2*Q := by
    filter_upwards [hwb,hqb] with k hwk hk
    filter_upwards [hwk,hk,
      ae_restrict_of_ae (localGamma_add_self_le μ hX.quadratic (w k) (t • q k)),
      ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic t (q k) (t • q k)),
      ae_restrict_of_ae (localGamma_smul_right μ hX.quadratic t (q k) (q k))]
      with x hwx hqx hx hl hr'
    have ht : localGamma μ hX.quadratic (t • q k) (t • q k) x=
        t^2*localGamma μ hX.quadratic (q k) (q k) x := by rw [hl,hr']; ring
    rw [ht] at hx
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (r k))
    nlinarith [mul_le_mul_of_nonneg_left hqx (sq_nonneg t)]
  have hlo := hX.weighted_energy_eventual_lower_on_ball hn hS hτ hρτ hτR hRS
    p r ε v hr hcurv hε hε1 hεlim hv F (fun y => g y+t*ψ y) hFlip hFconv
    φ hφ hs (by positivity : 0≤2*M+2*t^2*Q) hFb δ hδ
  have hEucl := weighted_gradient_quadratic_energy g ψ (ball (0:Euclidean n) S) φ
    (Eventually.of_forall fun _ => hg.1.differentiable (by simp) _)
    (Eventually.of_forall fun _ => hψ.1.differentiable (by simp) _) hgi hψi t
  have heq (a : Euclidean n → ℝ) : (∫ z, φ z*a z)=∫ z in ball (0:Euclidean n) S, φ z*a z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzφ : φ z=0 := Function.notMem_support.mp (fun hh =>
      hz ((ball_subset_ball (hρτ.trans (hτR.trans hRS)).le) (hs hh)))
    rw [hzφ,zero_mul]
  filter_upwards [hlo] with k hk
  rw [heq,hEucl] at hk
  have hsource := weighted_integral_localGamma_add_smul_square μ hX.quadratic (w k) (q k) t
    (ball (p k) (S*r k)) (fun x => φ (v k x))
    (φ.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => φ.norm_coe_le_norm (v k x))
  dsimp only [F] at hk
  rw [hsource] at hk
  simp only [div_eq_mul_inv] at hk
  convert hk using 1 <;> ring

end RegularPointCoordinates

end

end OAI
