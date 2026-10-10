import OAI.Geometry.RCD.Coordinates.BoundedFrameBarrier
import OAI.Geometry.RCD.Harmonic.CenteredBoundedGram
import OAI.Geometry.RCD.Coordinates.SplittingCoordinateLipschitz
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # The transverse barrier estimate for the original first-order coordinates -/

open Set Filter MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_transverse_barrier {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} {r ε δ c : ℝ}
    (hr : 0<r) (hε : 0≤ε) (hε1 : ε≤1) (hc : 0≤c)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : X → Euclidean n)
    (hs : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v)
    (a : Euclidean n) (ha : ‖a‖=1)
    (hsmall : ∀ x∈ball p (r/48), -δ<⟪v x-v p,a⟫_ℝ →
      ‖v x-v p‖^2-⟪v x-v p,a⟫_ℝ^2<c → dist x p<r/384) :
    IntegrableOn (fun x =>
      if -δ<⟪v x-v p,a⟫_ℝ then max (c-(‖v x-v p‖^2-⟪v x-v p,a⟫_ℝ^2)) 0 else 0)
      (ball p (r/48)) (hausdorff n X) ∧
    (∫ x in ball p (r/48),
      (if -δ<⟪v x-v p,a⟫_ℝ then max (c-(‖v x-v p‖^2-⟪v x-v p,a⟫_ℝ^2)) 0 else 0)
      ∂hausdorff n X) ≤
      (c+(2*(n:ℝ)*r+|δ|)*2*((n:ℝ)+1)*(2*(n:ℝ)*r))*
        ∫ x in ball p (r/48), gramDefect (hausdorff n X) hX.quadratic u x ∂hausdorff n X := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let Ω := ball p (r/48)
  let V x := v x-v p
  let M := 2*(n:ℝ)*r
  have hM : 0≤M := by dsimp [M]; positivity
  let A : ℝ≥0 := ⟨M,hM⟩
  have hsub : Ω⊆ball p (16*r) := ball_subset_ball (by linarith)
  have hV (x : X) (hx : x∈Ω) : ‖V x‖≤M := by
    have hs' : FirstOrderSplittingOn μ Q p (8*(2*r)) ε u v := by
      simpa only [show (8:ℝ)*(2*r)=16*r by ring] using hs
    have hL := hX.splitting_coordinate_lipschitz hn (by positivity : 0<2*r) hε hs'
    have hh := hL.dist_le_mul x (by change dist x p<2*r; exact lt_trans hx (by linarith))
      p (by change dist p p<2*r; simp; positivity)
    have hC : (n:ℝ)*(1+ε)≤2*(n:ℝ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    change ‖v x-v p‖≤2*(n:ℝ)*r
    rw [← dist_eq_norm]
    apply (hh.trans (mul_le_mul_of_nonneg_right hC dist_nonneg)).trans
    exact mul_le_mul_of_nonneg_left (by have hd : dist x p<r/48 := hx; linarith) (by positivity)
  obtain ⟨Cη,_hCη,⟨η⟩⟩ := hX.goodCutoff_exists hn p hr
  have hη : SobolevSpace.toLp μ Q η.sobolev =ᵐ[μ.restrict Ω] fun _ => (1:ℝ) := by
    filter_upwards [ae_restrict_of_ae η.representative,ae_restrict_mem measurableSet_ball] with x hx hxm
    exact hx.trans (η.one x (by have hd : dist x p<r/48 := hxm; change dist x p<r; linarith))
  have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q η.sobolev x|≤(1:ℝ≥0) := by
    filter_upwards [η.representative] with x hx
    rw [hx,abs_of_nonneg (η.bounds x).1]
    exact (η.bounds x).2
  obtain ⟨U,hUb,hUr,hUh,hUg⟩ := centered_bounded_gram μ Q u v (v p) Ω measurableSet_ball
    (fun i => ae_restrict_of_ae_restrict_of_subset hsub (hs.representative i))
    (fun i => (hs.harmonic i).mono μ Q hsub) η.sobolev hη A (by
      intro x hx i
      have hh : |(V x) i|≤‖V x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (V x) i
      exact hh.trans (hV x hx))
  obtain ⟨Cχ,_hCχ,⟨χ⟩⟩ := hX.goodCutoff_exists hn p (by positivity : 0<r/384)
  have hχb (x : X) : |χ.weight x|≤(1:ℝ≥0) := by
    rw [abs_of_nonneg (χ.bounds x).1]
    exact (χ.bounds x).2
  have hχs : tsupport (χ.weight : X → ℝ)⊆Ω :=
    (χ.tsupport_subset μ Q).trans (closedBall_subset_ball (by linarith))
  have hg : gramDefect μ Q U =ᵐ[μ.restrict Ω] gramDefect μ Q u := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUg i))] with x hx
    dsimp only [gramDefect]
    simp_rw [hx]
  have hb := bounded_frame_transverse_barrier μ Q U (fun _ => A) hUb isOpen_ball
    (hX.finiteOnBounded Ω isBounded_ball).ne V hUr hUh a ha hM hc hV δ
    η.sobolev hηb hη χ.sobolev χ.lipschitz (χ.hasCompactSupport μ Q) hχb
    (fun x => (χ.bounds x).1) hχs χ.representative (fun x hx hax hsx => χ.one x (hsmall x hx hax hsx))
  refine ⟨hb.1,?_⟩
  have hi := hb.2
  rw [integral_congr_ae hg] at hi
  exact hi

end RegularPointCoordinates

end

end OAI
