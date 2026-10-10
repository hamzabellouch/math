import OAI.Geometry.NodalSets.Elliptic.UniformContact

namespace OAI

namespace Yau.Jets
open Set Filter
open scoped Topology ContDiff
noncomputable section

lemma second_taylor_bound {f : Coord → ℝ} (hf : ContDiff ℝ ∞ f)
    (h0 : f 0 = 0) (h1 : fderiv ℝ f 0 = 0) (x : Coord) (C : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 3 f (t • x)‖ ≤ C) :
    f x ≤ (1/2:ℝ) * iteratedFDeriv ℝ 2 f 0 (fun _ ↦ x) + C * ‖x‖^3 / 2 := by
  let g : ℝ → ℝ := fun t ↦ f (t • x)
  have hgf : ContDiff ℝ (3:ℕ) g :=
    (hf.of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top)).comp
      (contDiff_id.smul contDiff_const)
  have hi (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      iteratedDerivWithin k g (Icc (0:ℝ) 1) t =
        iteratedFDeriv ℝ k f (t • x) (fun _ ↦ x) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1))
      (hgf.of_le (by exact_mod_cast hk)).contDiffAt ht]
    simpa [g] using Yau.Waves.iteratedDeriv_line
      (hf.of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top)) hk (0:Coord) x t
  have htaylor : taylorWithinEval g 2 (Icc (0:ℝ) 1) 0 1 =
      (1/2:ℝ) * iteratedFDeriv ℝ 2 f 0 (fun _ ↦ x) := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hi 0 (by omega) 0 (by constructor <;> norm_num),
      hi 1 (by omega) 0 (by constructor <;> norm_num),
      hi 2 (by omega) 0 (by constructor <;> norm_num)]
    simp [h0, h1, iteratedFDeriv_one_apply]
  have hderiv : ∀ t ∈ Icc (0:ℝ) 1,
      ‖iteratedDerivWithin 3 g (Icc (0:ℝ) 1) t‖ ≤ C * ‖x‖^3 := by
    intro t ht
    rw [hi 3 le_rfl t ht]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hb t ht) (pow_nonneg (norm_nonneg x) 3))
  have h := taylor_mean_remainder_bound (by norm_num : (0:ℝ) ≤ 1)
    hgf.contDiffOn (by constructor <;> norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) hderiv
  rw [htaylor] at h
  norm_num [g] at h
  have hh := (le_abs_self (f x - (1/2:ℝ) * iteratedFDeriv ℝ 2 f 0 (fun _ ↦ x))).trans h
  linarith

variable {T : Type*} [TopologicalSpace T]

theorem uniform_contact_from_second_jet {s : Set T} (hs : IsCompact s)
    (f : T → Coord → ℝ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hc : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ 3 (f z.1) z.2))
    (eta : T → ℝ) (heta : ContinuousOn eta s) (hpos : ∀ t ∈ s, 0 < eta t)
    (h0 : ∀ t ∈ s, f t 0 = 0) (h1 : ∀ t ∈ s, fderiv ℝ (f t) 0 = 0)
    (h2 : ∀ t ∈ s, ∀ x : Coord,
      iteratedFDeriv ℝ 2 (f t) 0 (fun _ ↦ x) ≤ -eta t * ‖x‖^2) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) → f t x ≤ -c*‖x‖^2 := by
  obtain ⟨e, he, _, _, heB⟩ := compact_positive_bounds hs eta heta hpos
  obtain ⟨C, hC, hb⟩ := ((hs.prod (isCompact_closedBall (0:Coord) 1)).image hc).isBounded.exists_pos_norm_le
  have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div, mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
  have hsmall := ht.eventually (eventually_lt_nhds (lt_min (by norm_num : (0:ℝ) < 1)
    (div_pos he (mul_pos (by norm_num : (0:ℝ)<4) hC))))
  refine ⟨e/4, by positivity, ?_⟩
  filter_upwards [hsmall] with N hN
  intro t hts x hx
  have hx1 : ‖x‖ ≤ 1 := hx.trans (le_of_lt (lt_of_lt_of_le hN (min_le_left _ _)))
  have hxC : C * ‖x‖ ≤ e / 4 := by
    have hh := hx.trans (le_of_lt (lt_of_lt_of_le hN (min_le_right _ _)))
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hC)).mp hh
    nlinarith
  have hseg : ∀ r ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 3 (f t) (r • x)‖ ≤ C := by
    intro r hr
    apply hb _
    refine ⟨(t,r • x), ⟨hts, ?_⟩, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg x)).trans (by simpa using hx1)
  have htay := second_taylor_bound (hf t) (h0 t hts) (h1 t hts) x C hseg
  have htwo := h2 t hts x
  have heta' := mul_le_mul_of_nonneg_right (heB t hts).1 (sq_nonneg ‖x‖)
  apply Yau.Waves.quadratic_gap_of_cubic_remainder (norm_nonneg x) hxC
  nlinarith [mul_nonneg hC.le (pow_nonneg (norm_nonneg x) 3)]

end
end Yau.Jets

end OAI
