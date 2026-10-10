import OAI.Probability.ContinuumTransition.KacRows

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem kernel_box_integral_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (c : Space) (k : Lattice) :
    (∫ y in gridBox u k, scaledKernel R (c-y)) ≤
      kacLower C R u c (gridCenter u k)*u^3+6*(C : ℝ)*u/R^4*u^3 := by
  have hfin : volume (gridBox u k) ≠ ⊤ := by rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top
  have hfun : Integrable (fun y : Space => scaledKernel R (c-y)) := (integrable_scaledKernel hR).comp_sub_left c
  have hmono := setIntegral_mono_on hfun.integrableOn
    (integrableOn_const (C := kacLower C R u c (gridCenter u k)+6*(C : ℝ)*u/R^4) hfin)
    (measurableSet_gridBox u k) ?_
  swap
  · intro y hy
    have hh := scaledKernel_oscillation hC hR (c-y) (c-gridCenter u k)
    rw [show (c-y)-(c-gridCenter u k)=-(y-gridCenter u k) by abel, norm_neg] at hh
    have he := hh.trans (mul_le_mul_of_nonneg_left (gridBox_center_distance hu hy) (by positivity))
    have he' := (abs_le.mp he).2
    have hk : scaledKernel R (c-gridCenter u k)-4*(C : ℝ)*u/R^4 ≤
        kacLower C R u c (gridCenter u k) := le_max_right _ _
    ring_nf at he' hk ⊢
    linarith only [he', hk]
  rw [setIntegral_const, volume_real_gridBox hu.le, smul_eq_mul] at hmono
  nlinarith only [hmono]

theorem kacLower_row {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (c : Space) (s : Finset Lattice)
    (hcover : ∀ y : Space, ‖c-y‖ < R → ∃ k ∈ s, y ∈ gridBox u k) :
    1-(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3 ≤
      u^3*(∑ k ∈ s, kacLower C R u c (gridCenter u k)) := by
  let near := s.filter (fun k => ‖c-gridCenter u k‖ ≤ R+4*u)
  have hnvol := card_grid_near_bound hu (show 0 ≤ R+4*u by positivity) c near (fun k hk => by
    have hh := (Finset.mem_filter.mp hk).2
    rwa [norm_sub_rev] at hh)
  have herr := mul_le_mul_of_nonneg_left hnvol (show 0 ≤ 6*(C : ℝ)*u/R^4 by positivity)
  have harg : 2*(R+4*u+2*u)=2*(R+6*u) := by ring
  rw [harg] at herr
  have hsums : (∑ k ∈ near, kacLower C R u c (gridCenter u k)) ≤
      ∑ k ∈ s, kacLower C R u c (gridCenter u k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro k _ _
    exact le_max_left _ _
  have hsums' := mul_le_mul_of_nonneg_left hsums (pow_pos hu 3).le
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ near) => kernel_box_integral_lower hC hR hu c k)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hb
  have hfun : Integrable (fun y : Space => scaledKernel R (c-y)) := (integrable_scaledKernel hR).comp_sub_left c
  have hi := integral_biUnion_finset near (fun _ _ => measurableSet_gridBox _ _)
    (fun _ _ _ _ hkl => gridBox_disjoint hu hkl) (fun _ _ => hfun.integrableOn)
  have hsum : (∑ k ∈ near, ∫ y in gridBox u k, scaledKernel R (c-y)) = 1 := by
    rw [← hi, setIntegral_eq_integral_of_forall_compl_eq_zero ?_, integral_sub_left_eq_self,
      integral_scaledKernel hR]
    intro y hy
    apply scaledKernel_zero hR
    by_contra! hh
    obtain ⟨k, hk, hyk⟩ := hcover y hh
    have hnear : k ∈ near := by
      apply Finset.mem_filter.mpr ⟨hk, ?_⟩
      have hl := norm_sub_le_norm_sub_add_norm_sub c y (gridCenter u k)
      have hd := gridBox_center_distance hu hyk
      linarith
    exact hy (Set.mem_iUnion₂.mpr ⟨k, hnear, hyk⟩)
  rw [hsum] at hb
  nlinarith only [hb, herr, hsums']

end ContinuumTemperature
end

end OAI
