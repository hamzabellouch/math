import OAI.Geometry.Convex.GeneralMahler.ShiftBound

namespace OAI
/-! Uniform cutoffs for the biased projections.
We strengthen the negative-tail estimate of the manuscript to an exact
cutoff (in z, depending linearly on |g|); this makes mixed-integrability
statements for the Jacobian fields simpler. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable (m : ℕ) [NeZero m] {K : ℝ}
namespace ProjField

def cutoffC (m : ℕ) (K : ℝ) := 1+2*K*(K+K*m*K^2/a 0)

theorem positive_exact (hk : 1 ≤ K) :
    let C := cutoffC m K
    1 ≤ C ∧ ∀ q : ProjField m, q.Bound K → ∀ (s:ℝ) x, C*(1+‖x‖)<s →
      q.Z x + q.shift s ∈ interior (q.C : Set (Rn m)) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < (m:ℝ) := m_pos
  let M := K*m*K^2/a 0
  have ha := a_pos 0
  have H : 0 ≤ M := by dsimp [M]; positivity
  let C := 1 + 2*K*(K+M)
  have hc : 1 ≤ C := by unfold C; nlinarith
  refine ⟨hc, fun q hq s x hs => ?_⟩
  change C*(1+‖x‖)<s at hs
  have hs' : 0 ≤ s := by nlinarith [norm_nonneg x]
  let w := ∫ x, q.YT s x ∂normal m
  have he : ‖w‖ ≤ M := calc
    _ ≤ _ := norm_integral_le_integral_norm _
    _ ≤ K*m*K^2/a s := positive_mean m q hq s
    _ ≤ M := by unfold M; gcongr; exact a_mono.monotone hs'
  have hz : q.shift s = a s • q.U - w := by dsimp [w]; rw [q.Y_mean]; abel
  have hw : ‖q.Z x - w‖ ≤ K*‖x‖+M :=
    (norm_sub_le ..).trans (add_le_add (hq.normZ _) he)
  have hb : K*(K*‖x‖+M) < a s := by
    have hh : p 0 ≤ p s := p_mono.monotone hs'
    rw [p_half] at hh
    dsimp only [C] at hs
    have hv : 0 ≤ K*M*‖x‖ := by positivity
    rw [a]; nlinarith [phi_pos s, norm_nonneg x]
  -- apply dual height criterion
  have heq : q.C = posDual q.D := (ProperCone.innerDual_innerDual _).symm
  rw [heq]
  have hid : q.Z x+q.shift s = a s • q.U+(q.Z x-w) := by rw [hz]; abel
  have hb' : 0 < a s/K - ‖q.Z x - w‖ := sub_pos.mpr (lt_div_iff₀ hp |>.mpr (by nlinarith))
  refine interior_dual_of_bound hb' (fun y hy => ?_)
  have h₁ := hq.inC _ hy
  have h₂ := abs_real_inner_le_norm (q.Z x - w) y
  rw [hid,inner_add_left, real_inner_smul_left, sub_mul]
  have hx₁ : a s / K * ‖y‖ ≤ a s * ⟪q.U,y⟫ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    have hi := mul_le_mul_of_nonneg_left h₁ (a_pos s).le
    linarith
  have h₃ := neg_le_of_abs_le h₂
  linarith

theorem positive_cutoff (hk : 1 ≤ K) :
    ∃ C ≥ (1:ℝ), ∀ q : ProjField m, q.Bound K → ∀ (s:ℝ) x, C*(1+‖x‖)<s →
      q.Z x + q.shift s ∈ interior (q.C : Set (Rn m)) :=
  ⟨_,positive_exact m hk⟩

theorem negative_cutoff (hk : 1 ≤ K) :
    ∃ C ≥ (1:ℝ), ∀ q : ProjField m, q.Bound K → ∀ (s:ℝ) x, C*(1+‖x‖)<s →
      -(q.Z x + q.shift (-s)) ∈ interior (q.D : Set (Rn m)) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < (m:ℝ) := m_pos
  let r := K⁻¹ -- shift center by 2
  have hr : 0 < r := inv_pos.mpr hp
  obtain ⟨c,hc,h₁⟩ := normal_ball_lower m hr
  let d := K*m*(√(2*π))⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  let L := |log c-log d|
  have hL : 0 ≤ L := abs_nonneg _
  let C := 2 + r + 2*K + L
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC, fun q hq s x hs => ?_⟩
  have hu : 0 ≤ s := by nlinarith [norm_nonneg x]
  by_contra hh
  obtain ⟨v,hv,hvn,hx⟩ := exists_ray_of_not_interior_dual hh
  rw [inner_neg_left] at hx
  let g := x+q.root.symm ((2:ℝ) • v)
  let S := closedBall g r
  have hgn : ‖g‖ ≤ ‖x‖+K*2 := by
    apply (norm_add_le ..).trans
    have hb : ‖(2:ℝ) • v‖ = 2 := by rw [norm_smul,hvn]; norm_num
    have he := q.root.symm.toContinuousLinearMap.le_opNorm ((2:ℝ) • v)
    rw [hb] at he
    apply add_le_add_right
    exact he.trans (mul_le_mul_of_nonneg_right hq.iS_le (by norm_num))
  have hnorm (y) (hy : y ∈ S) : 1 ≤ ‖q.XT (-s) y‖ := by
    have h₁ : ‖q.Z g - q.Z y‖ ≤ 1 := calc
      _ = ‖q.Z (g-y)‖ := by unfold Z; rw [_root_.map_sub]
      _ ≤ K*‖g-y‖ := hq.normZ _
      _ ≤ K*r := mul_le_mul_of_nonneg_left (by
          change dist y g ≤ r at hy; rwa [dist_comm, dist_eq_norm] at hy) hp.le
      _ = _ := mul_inv_cancel₀ hp.ne'
    have h₂ := real_inner_le_norm (q.Z g-q.Z y) v
    have he : q.Z g = q.Z x + (2:ℝ) • v := by simp only [g,Z,_root_.map_add,
      ContinuousLinearEquiv.apply_symm_apply]
    have hp : 0 ≤ ⟪v,q.XT (-s) y - (q.Z y + q.shift (-s))⟫ :=
      mem_posDual.mp (proj_residual_dual q.C _) hv
    rw [inner_sub_left, he, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq,hvn] at h₂
    have h₃ := real_inner_le_norm (q.XT (-s) y) v
    rw [real_inner_comm,inner_sub_left,inner_add_left] at hp
    rw [inner_add_left] at hx; rw [hvn] at h₃
    rw [he] at h₁
    nlinarith
  have hprob : (normal m).real S ≤ ∫ y, ‖q.XT (-s) y‖ ∂normal m := calc
    _ = ∫ y in S, (1:ℝ) ∂normal m := by simp
    _ ≤ ∫ y in S, ‖q.XT (-s) y‖ ∂normal m :=
      setIntegral_mono_on (integrable_const _).integrableOn (q.X_int _).norm.integrableOn
        measurableSet_closedBall hnorm
    _ ≤ _ := setIntegral_le_integral (q.X_int _).norm (ae_of_all _ fun y => norm_nonneg _)
  have hlt : c * Real.exp (-((‖g‖+r)^2)/2) ≤ d * Real.exp (-(s^2)/2) := calc
    _ ≤ _ := h₁ g
    _ ≤ _ := hprob
    _ ≤ K*m*a (-s) := hq.X_mean _
    _ ≤ K*m*phi s := mul_le_mul_of_nonneg_left (a_high s hu) (by positivity)
    _ = _ := by unfold d; rw [phi_apply]; ring
  have hll : log c - (‖g‖+r)^2/2 ≤ log d - s^2/2 := by
    have he : log (c * Real.exp (-((‖g‖+r)^2)/2)) ≤ log (d * Real.exp (-(s^2)/2)) :=
      Real.log_le_log (by positivity) hlt
    rw [Real.log_mul hc.ne' (by positivity),Real.log_mul hd.ne' (by positivity),
      Real.log_exp,Real.log_exp] at he
    linarith
  have he : ‖g‖+r+L+2 ≤ s := by
    have hi : C+‖x‖ ≤ s := by nlinarith [norm_nonneg x]
    unfold C at hi; linarith
  have ht := neg_abs_le (log c-log d)
  change -L ≤ _ at ht
  have hi : (‖g‖+r+L+2)^2 ≤ s^2 := by gcongr
  nlinarith [mul_nonneg hL (add_nonneg (norm_nonneg g) hr.le),norm_nonneg g]

end ProjField
end GeneralMahler

end

end OAI
