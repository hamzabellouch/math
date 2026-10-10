import OAI.Geometry.RCD.Harmonic.SmoothHarmonicModelCompactness
import OAI.Geometry.RCD.Harmonic.HomogeneousAffineImprovement

namespace OAI

/-! # Harmonic compactness for uniformly bounded, unnormalized families -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ContDiff Laplacian
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_harmonic_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S M : ℝ} (hS : 0<S) (hM : 0<M)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤M) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ g : Euclidean n → ℝ,
      Measurable g ∧ ContinuousOn g (ball 0 S) ∧ EuclideanWeakHarmonicOn g S ∧
      ContDiffOn ℝ ∞ g (ball 0 S) ∧
      (∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W)) ∧
      ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (W*r (a k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-g (V (a k) x)|≤δ := by
  let v := fun k => M⁻¹ • w k
  have hvnorm (k : ℕ) : harmonicTargetNorm hX (p k) (S*r k) (v k)≤1 := by
    rw [harmonicTargetNorm_smul,abs_of_pos (inv_pos.mpr hM)]
    exact (mul_le_mul_of_nonneg_left (hnorm k) (inv_pos.mpr hM).le).trans_eq
      (inv_mul_cancel₀ hM.ne')
  have hvh (k : ℕ) := (hw k).smul (hausdorff n X) hX.quadratic M⁻¹
  obtain ⟨g,a,ha,hgm,hgc,hgL,hconv,_⟩ := hX.open_ball_harmonic_test_compactness hn hS
    p r ε hr hcurv hε hε1 hεlim V hV v hvh hvnorm
  have hconv' : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (W*r (a k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v (a k)) x-g (V (a k) x)|≤δ := by
    intro W hW hWS δ hδ
    exact (hconv W hW hWS δ hδ).mono fun _ hk => hk.mono fun _ hx => hx.le
  have hweak := hX.harmonic_value_limit_weak_of_curvature hn hS (p∘a) (r∘a) (ε∘a)
    (fun k => hr (a k)) (fun k => hcurv (a k)) (fun k => hε (a k))
    (fun k => hε1 (a k)) (hεlim.comp ha.tendsto_atTop) (V∘a) (v∘a)
    (fun k => hV (a k)) (fun k => hvh (a k)) (fun k => hvnorm (a k)) g hgL hconv'
  have hscaledweak : EuclideanWeakHarmonicOn (fun z => M*g z) S := by
    intro ψ hψ
    simp_rw [mul_assoc]
    rw [integral_const_mul,hweak ψ hψ,mul_zero]
  refine ⟨a,ha,(fun z => M*g z),measurable_const.mul hgm,continuousOn_const.mul hgc,hscaledweak,
    contDiffOn_const.mul (continuous_weak_harmonic_smooth hgc hweak),?_,?_⟩
  · intro W hW
    obtain ⟨L,hL⟩ := hgL W hW
    refine ⟨⟨M,hM.le⟩*L,LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    have hh := mul_le_mul_of_nonneg_left (hL.dist_le_mul x hx y hy) hM.le
    change |M*g x-M*g y|≤(M*(L:ℝ))*dist x y
    rw [← mul_sub,abs_mul,abs_of_pos hM]
    exact hh.trans_eq (by ring)
  · intro W hW hWS δ hδ
    filter_upwards [hconv' W hW hWS (δ/M) (div_pos hδ hM)] with k hk
    have he : SobolevSpace.toLp (hausdorff n X) hX.quadratic (v (a k))=ᵐ[hausdorff n X]
        fun x => M⁻¹*SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x := by
      dsimp only [v]
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    filter_upwards [hk,ae_restrict_of_ae he] with x hx hex
    rw [hex] at hx
    have hh : |M*(M⁻¹*SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-g (V (a k) x))|≤M*(δ/M) := by
      rw [abs_mul,abs_of_pos hM]
      exact mul_le_mul_of_nonneg_left hx hM.le
    have heq : M*(M⁻¹*SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-g (V (a k) x))=
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-M*g (V (a k) x) := by
      field_simp
    rw [heq] at hh
    exact hh.trans_eq (mul_div_cancel₀ δ hM.ne')

end RegularPointCoordinates

end

end OAI
