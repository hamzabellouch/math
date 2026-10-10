import OAI.Probability.SLE.Loewner.TargetEulerInterpolation

namespace OAI

/-! The prescribed dyadic Euler definition converges to the bounded cutoff ODE.
Only continuity in time and a global Lipschitz bound in space are used. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

private def eulerSlope (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  cutoffField κ b j (((⌊t/mesh N⌋₊:ℕ):ℝ)*mesh N)
    (eulerSteps κ b j N z ⌊t/mesh N⌋₊)

private lemma euler_pairs_mem (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (L : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (T t : ℝ) (ht : t ∈ Icc 0 T) :
    (((⌊t/mesh N⌋₊:ℕ):ℝ)*mesh N,
      eulerSteps κ b j N z ⌊t/mesh N⌋₊) ∈ Icc (0:ℝ) T ×ˢ closedBall z (L*T) ∧
    (t,eulerFlow κ b j N z t) ∈ Icc (0:ℝ) T ×ˢ closedBall z (L*T) := by
  let k := ⌊t/mesh N⌋₊
  have hs0 : 0 ≤ (k:ℝ)*mesh N := mul_nonneg (Nat.cast_nonneg _) (mesh_pos N).le
  have hst : (k:ℝ)*mesh N ≤ t := (le_div_iff₀ (mesh_pos N)).1
    (Nat.floor_le (div_nonneg ht.1 (mesh_pos N).le))
  refine ⟨⟨⟨hs0,hst.trans ht.2⟩,?_⟩,⟨ht,?_⟩⟩
  · apply (eulerSteps_dist_le κ b j N z L hL k).trans
    calc
      (k:ℝ)*mesh N*L = L*((k:ℝ)*mesh N) := by ring
      _ ≤ L*T := mul_le_mul_of_nonneg_left (hst.trans ht.2) L.coe_nonneg
  · exact (eulerFlow_dist_initial_le κ b j N z L hL t ht.1).trans
      (mul_le_mul_of_nonneg_left ht.2 L.coe_nonneg)

private lemma euler_pairs_dist_lt (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (L : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (t δ : ℝ) (ht : 0 ≤ t) (hmesh : mesh N*(L+1)<δ) :
    dist ((((⌊t/mesh N⌋₊:ℕ):ℝ)*mesh N),
      eulerSteps κ b j N z ⌊t/mesh N⌋₊) (t,eulerFlow κ b j N z t) < δ := by
  let k := ⌊t/mesh N⌋₊
  have hst : (k:ℝ)*mesh N ≤ t := (le_div_iff₀ (mesh_pos N)).1
    (Nat.floor_le (div_nonneg ht (mesh_pos N).le))
  have hts : t-(k:ℝ)*mesh N < mesh N := by
    have hh := (div_lt_iff₀ (mesh_pos N)).1 (Nat.lt_floor_add_one (t/mesh N))
    change t < ((k:ℝ)+1)*mesh N at hh
    linarith
  rw [Prod.dist_eq]
  apply max_lt
  · rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hst)]
    have hh : mesh N ≤ mesh N*(L+1) := by nlinarith [mesh_pos N,L.coe_nonneg]
    exact hts.trans_le hh |>.trans hmesh
  · rw [dist_comm]
    have hh : L*mesh N < δ := by nlinarith [mesh_pos N]
    exact (eulerFlow_dist_grid_le κ b j N z L hL t ht).trans_lt hh

lemma eulerSlope_error_tendsto
    (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ)
    (L : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (T : ℝ) (_hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc 0 T,
      dist (eulerSlope κ b j N z t) (cutoffField κ b j t (eulerFlow κ b j N z t)) < ε := by
  let C := Icc (0:ℝ) T ×ˢ closedBall z (L*T)
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_closedBall z (L*T))
  obtain ⟨δ,hδ,huniform⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous (continuous_cutoffField κ b j hj).continuousOn) ε hε
  have hd : 0 < δ/(L+1) := div_pos hδ (by positivity)
  have hmesh : ∀ᶠ N : ℕ in atTop, mesh N < δ/(L+1) :=
    (tendsto_order.1 mesh_tendsto_zero).2 _ hd
  filter_upwards [hmesh] with N hN
  intro t ht
  obtain ⟨hgrid,hflow⟩ := euler_pairs_mem κ b j N z L hL T t ht
  have hhδ : mesh N*(L+1) < δ := (lt_div_iff₀ (by positivity : (0:ℝ)<L+1)).1 hN
  exact huniform
    ((((⌊t/mesh N⌋₊:ℕ):ℝ)*mesh N),eulerSteps κ b j N z ⌊t/mesh N⌋₊) hgrid
    (t,eulerFlow κ b j N z t) hflow (euler_pairs_dist_lt κ b j N z L hL t δ ht.1 hhδ)

lemma eulerFlow_tendsto_solution
    (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ)
    (L K : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (hK : ∀ t, LipschitzWith K (cutoffField κ b j t))
    (X : ℝ → ℂ) (hX : Continuous X) (hX0 : X 0=z)
    (hXd : ∀ t, 0 ≤ t → HasDerivWithinAt X (cutoffField κ b j t (X t)) (Ici 0) t)
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun N : ℕ => eulerFlow κ b j N z T) atTop (𝓝 (X T)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hcont : ContinuousAt (fun ε => gronwallBound 0 K ε T) 0 :=
    (gronwallBound_continuous_ε 0 K T).continuousAt
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousAt_iff.mp hcont ε hε
  let η := δ/2
  have hη : 0 < η := half_pos hδ
  have hbound : gronwallBound 0 K η T < ε := by
    have h := hsmall (show dist η 0 < δ by
      rw [Real.dist_eq,sub_zero,abs_of_pos hη]
      exact half_lt_self hδ)
    rw [gronwallBound_ε0_δ0,Real.dist_eq,sub_zero] at h
    exact (le_abs_self _).trans_lt h
  filter_upwards [eulerSlope_error_tendsto κ b j hj z L hL T hT η hη] with N hN
  have hestimate := dist_le_of_approx_trajectories_ODE (v := cutoffField κ b j)
    (f := eulerFlow κ b j N z) (g := X)
    (f' := eulerSlope κ b j N z) (g' := fun t => cutoffField κ b j t (X t))
    (a := 0) (b := T) (δ := 0) (εf := η) (εg := 0) hK
    (eulerFlow_continuousOn κ b j N z T)
    (fun t ht => eulerFlow_right_deriv κ b j N z t ht.1)
    (fun t ht => (hN t (Ico_subset_Icc_self ht)).le)
    hX.continuousOn
    (fun t ht => (hXd t ht.1).mono (Ici_subset_Ici.mpr ht.1))
    (fun _ _ => by simp)
    (by simp only [eulerFlow_zero,hX0,dist_self]; exact le_rfl) T ⟨hT,le_rfl⟩
  rw [add_zero,sub_zero] at hestimate
  exact hestimate.trans_lt hbound

lemma cutoffFlow_eq_solution
    (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ)
    (L K : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (hK : ∀ t, LipschitzWith K (cutoffField κ b j t))
    (X : ℝ → ℂ) (hX : Continuous X) (hX0 : X 0=z)
    (hXd : ∀ t, 0 ≤ t → HasDerivWithinAt X (cutoffField κ b j t (X t)) (Ici 0) t)
    (T : ℝ) (hT : 0 ≤ T) : cutoffFlow κ b j z T = X T := by
  exact (eulerFlow_tendsto_solution κ b j hj z L K hL hK X hX hX0 hXd T hT).limUnder_eq

end SLEExactGauge.Target

end

end OAI
