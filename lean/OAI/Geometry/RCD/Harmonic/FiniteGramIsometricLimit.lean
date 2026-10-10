import OAI.Geometry.RCD.Harmonic.FiniteHarmonicLimits
import OAI.Geometry.RCD.Sobolev.HarmonicEnergyRigidity
import OAI.Geometry.RCD.Sobolev.SumEnergyConvergence
import OAI.Geometry.RCD.Sobolev.SobolevSumValueConvergence
import OAI.Geometry.RCD.Coordinates.EuclideanCovectorIsometry
import OAI.Geometry.RCD.Harmonic.FiniteMeasuredHarmonicSequence
import OAI.Geometry.RCD.Coordinates.UnitCoordinateDirections

namespace OAI

/-! # Almost orthonormal harmonic families have affine isometric limits -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.finite_harmonic_isometric_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : Fin n → ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w i k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ i k, harmonicTargetNorm hX (p k) (5*r k) (w i k) ≤ M)
    (hgram : ∀ i j, Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w j k) x-
          (if i=j then 1 else 0)| ∂hausdorff n X) atTop (𝓝 0)) :
    ∃ α : ℕ → ℕ, StrictMono α ∧ ∃ g : Fin n → Euclidean n → ℝ,
      ∃ T : Euclidean n ≃ₗᵢ[ℝ] Euclidean n,
        (∀ i x, x ∈ ball (0 : Euclidean n) 3 → g i x = g i 0+T x i) ∧
        ∀ i W, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
          ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (W*r (α k))),
            |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i (α k)) x-g i (V (α k) x)| ≤ δ := by
  obtain ⟨α,hα,g,hh,hg,hL,hconv⟩ := hX.finite_bounded_harmonic_limits hn
    (by norm_num : (0:ℝ)<5) hM p r ε V hr hcurv hε hε1 hεlim hV w hw hnorm
  let μ := hausdorff n X
  let p' := p∘α
  let r' := r∘α
  let ε' := ε∘α
  let V' := V∘α
  let w' := fun i => w i∘α
  have heps : Tendsto ε' atTop (𝓝 0) := hεlim.comp hα.tendsto_atTop
  have herr (i j : Fin n) : Tendsto (fun k => (μ.real (ball (p' k) (5*r' k)))⁻¹*
      ∫ x in ball (p' k) (4*r' k),
        |r' k^2*localGamma μ hX.quadratic (w' i k) (w' j k) x-(if i=j then 1 else 0)| ∂μ)
      atTop (𝓝 0) := (hgram i j).comp hα.tendsto_atTop
  have hdiag (i : Fin n) : Tendsto (fun k => (μ.real (ball (p' k) (5*r' k)))⁻¹*
      ∫ x in ball (p' k) (4*r' k),
        |r' k^2*localGamma μ hX.quadratic (w' i k) (w' i k) x-1| ∂μ) atTop (𝓝 0) := by
    simpa only [ite_true] using herr i i
  have hgrad (i : Fin n) : ∀ x ∈ ball (0 : Euclidean n) 3, ‖fderiv ℝ (g i) x‖^2=1 :=
    hX.harmonic_constant_energy_gradient_limit hn p' r' ε' V' (fun k => hr (α k))
      (fun k => hcurv (α k)) (fun k => hε (α k)) (fun k => hε1 (α k)) heps
      (fun k => hV (α k)) (w' i) (fun k => hw i (α k)) hM (fun k => hnorm i (α k))
      (g i) (hg i) (hL i) (hconv i) (hdiag i)
  have haff (i : Fin n) : ∀ x ∈ ball (0 : Euclidean n) 3,
      g i x=g i 0+fderiv ℝ (g i) 0 x :=
    local_harmonic_constant_energy_affine (by norm_num) ((hg i).mono (ball_subset_ball (by norm_num)))
      ((hh i).mono (ball_subset_ball (by norm_num))) (hgrad i)
  have hsum (i j : Fin n) (hij : i ≠ j) : ‖fderiv ℝ (g i) 0+fderiv ℝ (g j) 0‖^2=2 := by
    have hpair : Tendsto (fun k => (μ.real (ball (p' k) (5*r' k)))⁻¹*
        ∫ x in ball (p' k) (4*r' k),
          |r' k^2*localGamma μ hX.quadratic (w' i k) (w' j k) x| ∂μ) atTop (𝓝 0) := by
      simpa only [hij,ite_false,sub_zero] using herr i j
    have hsumerr := sum_energy_l1_tendsto μ hX.quadratic
      (fun k => ball (p' k) (4*r' k)) (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
      r' (fun k => (μ.real (ball (p' k) (5*r' k)))⁻¹)
      (fun k => inv_nonneg.mpr (measureReal_nonneg)) (w' i) (w' j) 1 0 1
      (hdiag i) (by simpa only [sub_zero] using hpair) (hdiag j)
    have hconvsum : ∀ W : ℝ, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂μ.restrict (ball (p' k) (W*r' k)),
          |SobolevSpace.toLp μ hX.quadratic (w' i k+w' j k) x-
            (g i (V' k x)+g j (V' k x))| ≤ δ := by
      intro W hW hW5
      exact sobolev_sum_value_convergence μ hX.quadratic (fun k => ball (p' k) (W*r' k)) V'
        (w' i) (w' j) (g i) (g j) (hconv i W hW hW5) (hconv j W hW hW5)
    have hLip : ∀ W < (5:ℝ), ∃ L : ℝ≥0,
        LipschitzOnWith L (fun z => g i z+g j z) (closedBall 0 W) := by
      intro W hW
      obtain ⟨Li,hi⟩ := hL i W hW
      obtain ⟨Lj,hj⟩ := hL j W hW
      exact ⟨Li+Lj,hi.add hj⟩
    have hnormsum (k : ℕ) : harmonicTargetNorm hX (p' k) (5*r' k) (w' i k+w' j k) ≤ 2*M := by
      have hi : harmonicTargetNorm hX (p' k) (5*r' k) (w' i k) ≤ M := hnorm i (α k)
      have hj : harmonicTargetNorm hX (p' k) (5*r' k) (w' j k) ≤ M := hnorm j (α k)
      exact (harmonicTargetNorm_add_le hX _ _ _ _).trans (by linarith)
    have hgradsum := hX.harmonic_constant_energy_gradient_limit hn p' r' ε' V'
      (fun k => hr (α k)) (fun k => hcurv (α k)) (fun k => hε (α k)) (fun k => hε1 (α k))
      heps (fun k => hV (α k)) (fun k => w' i k+w' j k)
      (fun k => (hw i (α k)).add μ hX.quadratic (hw j (α k))) (by positivity : 0<2*M)
      hnormsum (fun z => g i z+g j z) ((hg i).add (hg j)) hLip hconvsum
      (by simpa only [mul_zero,add_zero,zero_add,show (1:ℝ)+1=2 by norm_num] using hsumerr)
    have h0 := hgradsum 0 (mem_ball_self (by norm_num : (0:ℝ)<3))
    rw [fderiv_fun_add ((hg i).differentiableOn (by simp) |>.differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0:ℝ)<5))))
      ((hg j).differentiableOn (by simp) |>.differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0:ℝ)<5))))] at h0
    exact h0
  obtain ⟨T,hT⟩ := euclidean_isometry_of_covector_norms (fun i => fderiv ℝ (g i) 0)
    (fun i => hgrad i 0 (mem_ball_self (by norm_num))) hsum
  exact ⟨α,hα,g,T,fun i x hx => (haff i x hx).trans (by rw [hT]),hconv⟩

end RegularPointCoordinates

end

end OAI
