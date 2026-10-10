import OAI.Probability.ContinuumTransition.GridVolume

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def kacUpper (C R u : ℝ) (c d : Space) : ℝ :=
  if ‖c-d‖ ≤ R+4*u then scaledKernel R (c-d)+4*C*u/R^4 else 0

noncomputable def kacLower (C R u : ℝ) (c d : Space) : ℝ :=
  max 0 (scaledKernel R (c-d)-4*C*u/R^4)

theorem kacUpper_nonneg {C R u : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hu : 0 ≤ u) (c d : Space) :
    0 ≤ kacUpper C R u c d := by
  unfold kacUpper
  split_ifs
  · exact add_nonneg (scaledKernel_nonneg hR _) (by positivity)
  · rfl

theorem kacUpper_symm (C R u : ℝ) (c d : Space) : kacUpper C R u c d = kacUpper C R u d c := by
  unfold kacUpper
  rw [norm_sub_rev, ← neg_sub c d, scaledKernel_neg]

theorem kernel_pair_oscillation {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) {c d x y : Space} (hx : ‖x-c‖ ≤ 2*u) (hy : ‖y-d‖ ≤ 2*u) :
    |scaledKernel R (x-y)-scaledKernel R (c-d)| ≤ 4*(C : ℝ)*u/R^4 := by
  have hn : ‖(x-y)-(c-d)‖ ≤ 4*u := by
    rw [show (x-y)-(c-d)=(x-c)-(y-d) by abel]
    exact (norm_sub_le _ _).trans (by linarith)
  have hh := (scaledKernel_oscillation hC hR (x-y) (c-d)).trans
    (mul_le_mul_of_nonneg_left hn (by positivity))
  calc
    _ ≤ (C : ℝ)/R^4*(4*u) := hh
    _ = _ := by ring

theorem kac_pair_bounds {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) {c d x y : Space} (hx : ‖x-c‖ ≤ 2*u) (hy : ‖y-d‖ ≤ 2*u) :
    kacLower C R u c d ≤ scaledKernel R (x-y) ∧ scaledKernel R (x-y) ≤ kacUpper C R u c d := by
  have he := (abs_le.mp (kernel_pair_oscillation hC hR hx hy))
  constructor
  · exact max_le (scaledKernel_nonneg hR _) (by linarith [he.1])
  · unfold kacUpper
    split_ifs with hn
    · linarith [he.2]
    · have hc' : ‖c-d‖ ≤ 4*u+‖x-y‖ := by
        calc
          ‖c-d‖ ≤ ‖c-x‖+‖x-d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ‖c-x‖+(‖x-y‖+‖y-d‖) := add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub x y d)
          _ ≤ 4*u+‖x-y‖ := by rw [norm_sub_rev c x]; linarith
      rw [scaledKernel_zero hR (by linarith [lt_of_not_ge hn])]

theorem kernel_box_integral_upper {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (c : Space) (k : Lattice) :
    scaledKernel R (c-gridCenter u k)*u^3 ≤
      (∫ y in gridBox u k, scaledKernel R (c-y))+2*(C : ℝ)*u/R^4*u^3 := by
  have hfin : volume (gridBox u k) ≠ ⊤ := by rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top
  have hfun : Integrable (fun y : Space => scaledKernel R (c-y)) := (integrable_scaledKernel hR).comp_sub_left c
  have hcst : IntegrableOn (fun _ : Space => 2*(C : ℝ)*u/R^4) (gridBox u k) := integrableOn_const hfin
  have hmono := setIntegral_mono_on
    (integrableOn_const (C := scaledKernel R (c-gridCenter u k)) hfin)
    (hfun.integrableOn.add hcst) (measurableSet_gridBox u k) ?_
  swap
  · intro y hy
    have hh := scaledKernel_oscillation hC hR (c-gridCenter u k) (c-y)
    rw [show (c-gridCenter u k)-(c-y)=y-gridCenter u k by abel] at hh
    have he := hh.trans (mul_le_mul_of_nonneg_left (gridBox_center_distance hu hy) (by positivity))
    have he' := (abs_le.mp he).2
    have ha : (C : ℝ)/R^4*(2*u)=2*(C : ℝ)*u/R^4 := by ring
    rw [ha] at he'
    change scaledKernel R (c-gridCenter u k) ≤ scaledKernel R (c-y)+2*(C : ℝ)*u/R^4
    linarith only [he']
  simp only [Pi.add_apply] at hmono
  rw [integral_add hfun.integrableOn hcst, setIntegral_const, setIntegral_const,
    volume_real_gridBox hu.le, smul_eq_mul, smul_eq_mul] at hmono
  nlinarith only [hmono]

theorem kacUpper_row {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (c : Space) (s : Finset Lattice) :
    u^3*(∑ k ∈ s, kacUpper C R u c (gridCenter u k)) ≤
      1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3 := by
  let near := s.filter (fun k => ‖c-gridCenter u k‖ ≤ R+4*u)
  have heq : (∑ k ∈ s, kacUpper C R u c (gridCenter u k)) =
      ∑ k ∈ near, (scaledKernel R (c-gridCenter u k)+4*(C : ℝ)*u/R^4) := by
    simp only [near, Finset.sum_filter, kacUpper]
  rw [heq, Finset.mul_sum]
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ near) => by
    have hh := kernel_box_integral_upper hC hR hu c k
    show u^3*(scaledKernel R (c-gridCenter u k)+4*(C : ℝ)*u/R^4) ≤
      (∫ y in gridBox u k, scaledKernel R (c-y))+(6*(C : ℝ)*u/R^4)*u^3
    ring_nf at hh ⊢
    linarith only [hh])
  apply hb.trans
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hfun : Integrable (fun y : Space => scaledKernel R (c-y)) := (integrable_scaledKernel hR).comp_sub_left c
  have hi := integral_biUnion_finset near (fun _ _ => measurableSet_gridBox _ _)
    (fun _ _ _ _ hkl => gridBox_disjoint hu hkl) (fun _ _ => hfun.integrableOn)
  have hsum : (∑ k ∈ near, ∫ y in gridBox u k, scaledKernel R (c-y)) ≤ 1 := by
    rw [← hi]
    have hh := setIntegral_le_integral (s := ⋃ k ∈ near, gridBox u k) hfun (Eventually.of_forall (fun y => scaledKernel_nonneg hR (c-y)))
    have hint : (∫ y : Space, scaledKernel R (c-y)) = 1 := by
      rw [integral_sub_left_eq_self, integral_scaledKernel hR]
    rw [hint] at hh
    exact hh
  have hn := card_grid_near_bound hu (show 0 ≤ R+4*u by positivity) c near (fun k hk => by
    have hh := (Finset.mem_filter.mp hk).2
    rwa [norm_sub_rev] at hh)
  have herr := mul_le_mul_of_nonneg_left hn (show 0 ≤ 6*(C : ℝ)*u/R^4 by positivity)
  have harg : 2*(R+4*u+2*u)=2*(R+6*u) := by ring
  rw [harg] at herr
  nlinarith only [hsum, herr]

end ContinuumTemperature
end

end OAI
