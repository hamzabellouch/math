import OAI.MathematicalPhysics.NavierStokes.Material.Clock

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open Filter

noncomputable section

def shiftedSum (a : ℝ → ℝ) (W : ℕ → Space → Space) : Field :=
  fun t x => ∑ᶠ n : ℕ, a (t - n) • W n x

theorem shiftedSum_eq_sum {a : ℝ → ℝ} (ha : ∀ s ≤ 0, a s = 0)
    (W : ℕ → Space → Space) (N : ℕ) {t : ℝ} (ht : t ≤ N) (x : Space) :
    shiftedSum a W t x = ∑ n ∈ Finset.range N, a (t - n) • W n x := by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hN
  have hN' : N ≤ n := by simpa using hN
  have hR : (N : ℝ) ≤ n := by exact_mod_cast hN'
  exact hn (by simp only [ha (t - n) (by linarith), zero_smul])

theorem shiftedSum_smooth {a : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (ha0 : ∀ s ≤ 0, a s = 0) (W : ℕ → Space → Space)
    (hW : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (shiftedSum a W)) := by
  apply contDiff_iff_contDiffAt.2
  intro tx
  obtain ⟨N, hN⟩ := exists_nat_gt tx.1
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space => ∑ n ∈ Finset.range N, a (p.1 - n) • W n p.2) := by
    apply ContDiff.sum
    intro n _hn
    exact (ha.comp (contDiff_fst.sub contDiff_const)).smul ((hW n).comp contDiff_snd)
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto tx).eventually (gt_mem_nhds hN)] with p hp
  exact shiftedSum_eq_sum ha0 W N hp.le p.2

theorem shiftedSum_supported {a : ℝ → ℝ} {K : Set Space} (W : ℕ → Space → Space)
    (hW : ∀ n x, x ∉ K → W n x = 0) : SupportedIn K (shiftedSum a W) := by
  intro t _ht x hx
  simp [shiftedSum, hW _ _ hx]

theorem shiftedSum_zero {a : ℝ → ℝ} (ha : ∀ s ≤ 0, a s = 0)
    (W : ℕ → Space → Space) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    shiftedSum a W t x = 0 := by
  simpa using shiftedSum_eq_sum ha W 0 (by simpa using ht) x

theorem divergence_sum {ι : Type*} (s : Finset ι) {u : ι → Space → Space}
    (hu : ∀ i ∈ s, Differentiable ℝ (u i)) (x : Space) :
    divergence (fun y => ∑ i ∈ s, u i y) x = ∑ i ∈ s, divergence (u i) x := by
  simp only [divergence, spatialD, fderiv_fun_sum (fun i hi => hu i hi x),
    sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_comm

theorem divergence_const_smul {u : Space → Space} (hu : Differentiable ℝ u)
    (c : ℝ) (x : Space) : divergence (fun y => c • u y) x = c * divergence u x := by
  simp only [divergence, spatialD, fderiv_fun_const_smul (hu x),
    smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem shiftedSum_divergence {a : ℝ → ℝ} (ha : ∀ s ≤ 0, a s = 0)
    (W : ℕ → Space → Space) (hW : ∀ n, Differentiable ℝ (W n))
    (hd : ∀ n x, divergence (W n) x = 0) (t : ℝ) (x : Space) :
    divergence (shiftedSum a W t) x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have he : shiftedSum a W t = fun x => ∑ n ∈ Finset.range N, a (t - n) • W n x := by
    funext x
    exact shiftedSum_eq_sum ha W N hN.le x
  rw [he]
  have hs : divergence (fun y => ∑ n ∈ Finset.range N, a (t - (n : ℝ)) • W n y) x =
      ∑ n ∈ Finset.range N, divergence (fun y => a (t - (n : ℝ)) • W n y) x := by
    apply divergence_sum
    intro n _hn
    exact (hW n).fun_const_smul (a (t - (n : ℝ)))
  rw [hs]
  simp only [divergence_const_smul (hW _), hd, mul_zero, Finset.sum_const_zero]

theorem clock_pulse_smooth : ContDiff ℝ (⊤ : ℕ∞) (deriv clock) :=
  (contDiff_infty_iff_deriv.mp clock_smooth).2

theorem clock_nonpos {t : ℝ} (ht : t ≤ 0) : clock t = 0 := clock_zero (by linarith)

theorem clock_pulse_nonpos {t : ℝ} (ht : t ≤ 0) : deriv clock t = 0 := by
  simpa using clock_deriv_collar 0 (Or.inl (by linarith : t < 1 / 4))

theorem clock_pulse_ge_one {t : ℝ} (ht : 1 ≤ t) : deriv clock t = 0 := by
  simpa using clock_deriv_collar 0 (Or.inr (by linarith : 3 / 4 < t))

theorem pulseSum_on_slot (W : ℕ → Space → Space) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (n : ℝ) (n + 1)) (x : Space) :
    shiftedSum (deriv clock) W t x = deriv clock (t - n) • W n x := by
  apply finsum_eq_single
  intro j hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · have hij : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    rw [clock_pulse_ge_one (by linarith [ht.1]), zero_smul]
  · have hij : (n : ℝ) + 1 ≤ j := by exact_mod_cast hj
    rw [clock_pulse_nonpos (by linarith [ht.2]), zero_smul]

def progressSum (d : ℕ → Space) (t : ℝ) : Space :=
  ∑ᶠ n : ℕ, clock (t - n) • d n

theorem progressSum_eq_sum (d : ℕ → Space) (N : ℕ) {t : ℝ} (ht : t ≤ N) :
    progressSum d t = ∑ n ∈ Finset.range N, clock (t - n) • d n :=
  shiftedSum_eq_sum (fun _ => clock_nonpos) (fun n _ => d n) N ht 0

theorem progressSum_on_slot (d : ℕ → Space) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (n : ℝ) (n + 1)) :
    progressSum d t = (∑ j ∈ Finset.range n, d j) + clock (t - n) • d n := by
  rw [progressSum_eq_sum d (n + 1) (by simpa using ht.2), Finset.sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hij : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hj
  rw [clock_one (by linarith [ht.1]), one_smul]

theorem progressSum_hasDerivAt (d : ℕ → Space) (t : ℝ) :
    HasDerivAt (progressSum d)
      (shiftedSum (deriv clock) (fun n _ => d n) t 0) t := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  rw [shiftedSum_eq_sum (fun _ => clock_pulse_nonpos) _ N hN.le]
  have hder : HasDerivAt
      (fun s : ℝ => ∑ n ∈ Finset.range N, clock (s - n) • d n)
      (∑ n ∈ Finset.range N, deriv clock (t - n) • d n) t := by
    apply HasDerivAt.fun_sum
    intro n _hn
    have hc := (clock_smooth.differentiable (by simp) (t - n)).hasDerivAt
    have hh := hc.comp t ((hasDerivAt_id t).sub_const (n : ℝ))
    simpa using hh.smul_const (d n)
  apply hder.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds hN] with s hs
  exact progressSum_eq_sum d N hs.le

end
end Alternating

end OAI
