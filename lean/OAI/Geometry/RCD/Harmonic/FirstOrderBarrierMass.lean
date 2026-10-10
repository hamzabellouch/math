import OAI.Geometry.RCD.Harmonic.TransverseBarrierLocalization

namespace OAI

/-! # A supported original frame forces a quantitative lower Gram-error mass -/

open Set Filter MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_barrier_mass {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} {r ε : ℝ}
    (hr : 0<r) (hε : 0≤ε) (hε1 : ε≤1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hs : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v)
    (a : Euclidean n) (ha : ‖a‖=1)
    (hmetric : ∀ x∈ball p (r/48), |‖v x-v p‖/r-dist x p/r|≤1/4096)
    (hsupport : ∀ x∈ball p (r/48), ⟪v x-v p,a⟫_ℝ≤r/4096) :
    (r/4096)^2/2*(hausdorff n X).real (ball p (r/(16384*(n:ℝ)))) ≤
      ((r/4096)^2+(2*(n:ℝ)*r+r/4096)*2*((n:ℝ)+1)*(2*(n:ℝ)*r))*
        ∫ x in ball p (r/48), gramDefect (hausdorff n X) hX.quadratic u x ∂hausdorff n X := by
  have hn0 : (2:ℝ)≤n := by exact_mod_cast hn
  have hsmall : ∀ x∈ball p (r/48), -(r/4096)<⟪v x-v p,a⟫_ℝ →
      ‖v x-v p‖^2-⟪v x-v p,a⟫_ℝ^2<(r/4096)^2 → dist x p<r/384 := by
    intro x hx hW hS
    have hd : dist x p≤‖v x-v p‖+r/4096 := by
      have hh := (abs_le.mp (hmetric x hx)).1
      have hm := (le_div_iff₀ hr).mp (show (-1/4096:ℝ)≤(‖v x-v p‖-dist x p)/r by
        simpa only [sub_div,neg_div] using hh)
      linarith
    have hh := transverse_barrier_localization (v x-v p) a (by positivity : 0<r/4096)
      hd (hsupport x hx) hW hS
    linarith
  obtain ⟨hI,hupper⟩ := hX.first_order_transverse_barrier hn hr hε hε1 (sq_nonneg (r/4096))
    u v hs a ha hsmall
  let ρ := r/(16384*(n:ℝ))
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρR : ρ≤r/48 := by
    dsimp [ρ]
    apply (div_le_div_iff₀ (by positivity : 0<16384*(n:ℝ)) (by norm_num : (0:ℝ)<48)).mpr
    nlinarith
  have hsub : ball p ρ⊆ball p (r/48) := ball_subset_ball hρR
  have hV : ∀ x∈ball p ρ, ‖v x-v p‖≤(r/4096)/2 := by
    intro x hx
    have hs' : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (8*(2*r)) ε u v := by
      simpa only [show (8:ℝ)*(2*r)=16*r by ring] using hs
    have hL := hX.splitting_coordinate_lipschitz hn (by positivity : 0<2*r) hε hs'
    have hh := hL.dist_le_mul x (by
        change dist x p<2*r
        have hd : dist x p<ρ := hx
        linarith)
      p (by change dist p p<2*r; simp; positivity)
    have hC : (n:ℝ)*(1+ε)≤2*(n:ℝ) := by nlinarith
    have hd := (hh.trans (mul_le_mul_of_nonneg_right hC dist_nonneg)).trans
      (mul_le_mul_of_nonneg_left (le_of_lt hx) (by positivity : 0≤2*(n:ℝ)))
    rw [dist_eq_norm] at hd
    apply hd.trans
    dsimp [ρ]
    have hnne : (n:ℝ)≠0 := by linarith
    apply le_of_eq
    field_simp [hnne]
    ring
  have hlower := transverse_barrier_integral_lower (hausdorff n X) a ha (fun x => v x-v p)
    measurableSet_ball hsub (by positivity : 0<r/4096)
    (hX.finiteOnBounded _ isBounded_ball).ne hI hV
  have hb := hlower.trans hupper
  simpa only [abs_of_pos (by positivity : 0<r/4096)] using hb

end RegularPointCoordinates

end

end OAI
