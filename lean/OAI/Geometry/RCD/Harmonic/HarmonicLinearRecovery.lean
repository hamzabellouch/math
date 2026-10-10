import OAI.Geometry.RCD.Harmonic.BoundedHarmonicStrongRecovery
import OAI.Geometry.RCD.Sobolev.BoundedHarmonicScaledEnergy
import OAI.Geometry.RCD.Sobolev.CutoffEnergyCoreConvergence

namespace OAI

/-! # Strong local recovery for unit linear harmonic limits -/

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_linear_recovery {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0<M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k)≤M)
    (L : Euclidean n →L[ℝ] ℝ) (hL : ‖L‖≤1)
    (hconv : ∀ W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-L (V k x)|≤δ) :
    ∃ N : ℕ, ∃ q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∃ B : ℝ, 0≤B ∧ ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (4*r (k+N))),
        r (k+N)^2*localGamma (hausdorff n X) hX.quadratic (w (k+N)) (w (k+N)) x≤B) ∧
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (4*r (k+N))),
          r (k+N)^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤(1+δ)^2) ∧
      Tendsto (fun k => r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (5*r (k+N))))⁻¹*
        ∫ x in ball (p (k+N)) (4*r (k+N)),
          localGamma (hausdorff n X) hX.quadratic (w (k+N)-q k) (w (k+N)-q k) x ∂hausdorff n X)
        atTop (𝓝 0) := by
  obtain ⟨F,_,_,hd,N,q₀,_,hqg,_,_,hstrong⟩ := hX.bounded_harmonic_strong_recovery hn
    (a:=4) (b:=17/4) (R:=9/2) (T:=19/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM
    p r ε V hr hcurv hε hε1 hεlim hV w hw hnorm L L.contDiff.contDiffOn
    (fun _ _ => ⟨_,L.lipschitzWith.lipschitzOnWith⟩) hconv
  let q := fun k => (q₀ k).val
  refine ⟨N,q,?_,?_,?_⟩
  · obtain ⟨B,hB,hbound⟩ := hX.bounded_harmonic_scaled_energy_bound hn
      (S:=5) (R:=4) (by norm_num) (by norm_num) (by norm_num) hM p r hr hcurv w hw hnorm
    exact ⟨B,hB,fun k => ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall (hbound (k+N))⟩
  · intro δ hδ
    filter_upwards [hqg 4 (by norm_num) (by norm_num) δ hδ,
      (hεlim.comp (tendsto_add_atTop_nat N)).eventually
        (eventually_lt_nhds (by norm_num : (0:ℝ)<3/8))] with k hkg hεk
    filter_upwards [hkg,self_mem_ae_restrict measurableSet_ball,
      ae_restrict_of_ae (localGamma_self (hausdorff n X) hX.quadratic (q k)),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg
        (hausdorff n X) hX.quadratic (q k)))] with x hxg hxb hself hnonneg
    have hrad := (abs_le.mp (pointed_radial_distance (hr (k+N)) (by norm_num : (0:ℝ)≤5)
      (hV (k+N)).metric (hxb.le.trans (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ)≤5) (hr _).le)))).2
    have hdist : dist x (p (k+N))/r (k+N)<4 := (div_lt_iff₀ (hr _)).mpr hxb
    have hin : V (k+N) x∈ball (0:Euclidean n) (19/4) := by
      simp only [mem_ball,dist_zero_right]
      change ε (k+N)<3/8 at hεk
      linarith
    have hdn : ‖fderiv ℝ F (V (k+N) x)‖≤1 := by
      rw [hd hin,L.hasFDerivAt.fderiv]
      exact hL
    have hb : r (k+N)*SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (q k) x≤1+δ :=
      hxg.trans (by change ‖fderiv ℝ F (V (k+N) x)‖+δ≤1+δ; linarith)
    have hs := pow_le_pow_left₀ (mul_nonneg (hr _).le hnonneg) hb 2
    simpa only [mul_pow,hself] using hs
  · exact cutoff_energy_core_convergence (hausdorff n X) hX.quadratic
      (a:=4) (b:=17/4) (R:=9/2) (by norm_num) (by norm_num)
      (fun k => p (k+N)) (fun k => r (k+N))
      (fun k => r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (5*r (k+N))))⁻¹)
      (fun k => hr (k+N)) (fun _ => by positivity) (fun k => w (k+N)-q k) hstrong

end RegularPointCoordinates

end

end OAI
