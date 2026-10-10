import OAI.Probability.SLE.Geometry.HyperbolicGuideCompactness

namespace OAI

/-! Compact confinement for the actual Lipschitz access guides. Local
conformal derivative bounds are integrated by continuous induction, so no
differentiability of the physical guide is required. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.LipschitzGuideConfinement

/-- A common local distance bound on a real interval is a global bound.
The proof uses continuous induction and applies to arbitrary metric targets. -/
theorem lipschitzOn_of_local_bound
    {E : Type*} [PseudoMetricSpace E] {f : ℝ → E} {a b K : ℝ}
    (hK : 0 ≤ K) (hf : ContinuousOn f (Icc a b))
    (hloc : ∀ t ∈ Icc a b, ∃ ε : ℝ, 0 < ε ∧
      ∀ u ∈ Icc a b, dist u t < ε → dist (f u) (f t) ≤ K * dist u t) :
    LipschitzOnWith ⟨K, hK⟩ f (Icc a b) := by
  have hsegment {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      dist (f t) (f s) ≤ K * (t - s) := by
    let S : Set ℝ := {x | dist (f x) (f s) ≤ K * (x - s)}
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hc : ContinuousOn (fun x => (dist (f x) (f s), K * (x - s))) (Icc s t) :=
      (continuous_dist.comp_continuousOn ((hf.mono hsub).prodMk continuousOn_const)).prodMk
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    have hclosed : IsClosed (S ∩ Icc s t) := by
      rw [inter_comm]
      exact hc.preimage_isClosed_of_isClosed isClosed_Icc
        OrderClosedTopology.isClosed_le'
    have hmem : Icc s t ⊆ S := hclosed.Icc_subset_of_forall_exists_gt
      (by change dist (f s) (f s) ≤ K * (s - s); simp) (by
        intro x hx y hy
        obtain ⟨ε, hε, hεbound⟩ := hloc x (hsub (Ico_subset_Icc_self hx.2))
        let z := min t (min y (x + ε / 2))
        have hxz : x < z := lt_min hx.2.2 (lt_min hy (by linarith))
        have hzt : z ≤ t := min_le_left _ _
        have hzy : z ≤ y := (min_le_right _ _).trans (min_le_left _ _)
        have hzx : z ≤ x + ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
        have hz : z ∈ Icc s t := ⟨hx.2.1.trans hxz.le, hzt⟩
        have hdist : dist z x < ε := by
          rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxz)]
          linarith
        have hlocal := hεbound z (hsub hz) hdist
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxz)] at hlocal
        refine ⟨z, ?_, hxz, hzy⟩
        change dist (f z) (f s) ≤ K * (z - s)
        calc
          dist (f z) (f s) ≤ dist (f z) (f x) + dist (f x) (f s) := dist_triangle _ _ _
          _ ≤ K * (z - x) + K * (x - s) := add_le_add hlocal hx.1
          _ = K * (z - s) := by ring)
    exact hmem ⟨hst, le_rfl⟩
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [dist_comm (f s), Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hsegment hs ht hst
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
    exact hsegment ht hs hts

theorem log_im_fderiv_bound
    {g : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball z r)) (hi : InjOn g (ball z r))
    (hH : MapsTo g (ball z r) upperHalfPlane) :
    DifferentiableAt ℝ (fun w => Real.log (g w).im) z ∧
      ‖fderiv ℝ (fun w => Real.log (g w).im) z‖ ≤ (128 * Real.pi) / r := by
  have hgd : DifferentiableAt ℂ g z := hg.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hzH : 0 < (g z).im := hH (mem_ball_self hr)
  have hd : HasFDerivAt (fun w => Real.log (g w).im)
      ((g z).im⁻¹ • Complex.imCLM.comp (fderiv ℝ g z)) z := by
    simpa only [Function.comp_apply, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp z (hgd.restrictScalars ℝ).hasFDerivAt).log hzH.ne'
  have hnorm : ‖fderiv ℝ g z‖ = ‖deriv g z‖ := by
    rw [hgd.fderiv_restrictScalars (𝕜 := ℝ), ContinuousLinearMap.norm_restrictScalars,
      ← norm_deriv_eq_norm_fderiv (𝕜 := ℂ)]
  have hb := HyperbolicGuideCompactness.inverse_chart_derivative_bound hr hg hi hH
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hzH]
  calc
    (g z).im⁻¹ * ‖Complex.imCLM.comp (fderiv ℝ g z)‖ ≤
        (g z).im⁻¹ * (‖Complex.imCLM‖ * ‖fderiv ℝ g z‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
    _ = (g z).im⁻¹ * ‖deriv g z‖ := by rw [Complex.imCLM_norm, one_mul, hnorm]
    _ ≤ (g z).im⁻¹ * (((128 * Real.pi) / r) * (g z).im) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (128 * Real.pi) / r := by field_simp

/-- The logarithm of the inverse-map height has bounded gradient on each
physical clearance ball. -/
theorem log_im_lipschitz_on_half_ball
    {g : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball z r)) (hi : InjOn g (ball z r))
    (hH : MapsTo g (ball z r) upperHalfPlane) :
    LipschitzOnWith ⟨(256 * Real.pi) / r, by positivity⟩
      (fun w => Real.log (g w).im) (ball z (r / 2)) := by
  have hbound (w : ℂ) (hw : w ∈ ball z (r / 2)) :
      DifferentiableAt ℝ (fun w => Real.log (g w).im) w ∧
        ‖fderiv ℝ (fun w => Real.log (g w).im) w‖ ≤ (256 * Real.pi) / r := by
    have hsub : ball w (r / 2) ⊆ ball z r := by
      intro u hu
      apply mem_ball.mpr
      have hh := (dist_triangle u w z).trans_lt (add_lt_add (mem_ball.mp hu) (mem_ball.mp hw))
      linarith
    have hh := log_im_fderiv_bound (by positivity : 0 < r / 2)
      (hg.mono hsub) (hi.mono hsub) (hH.mono_left hsub)
    refine ⟨hh.1, ?_⟩
    convert hh.2 using 1
    ring
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun w hw => (hbound w hw).1) _
    (convex_ball _ _)
  intro w hw
  exact_mod_cast (hbound w hw).2

/-- Lipschitz guides have a uniformly Lipschitz logarithmic inverse height,
even at their corners. -/
theorem log_height_lipschitz
    {g : ℂ → ℂ} {α : ℝ → ℂ} {δ T r : ℝ} (hr : 0 < r) (C : ℝ≥0)
    (hL : LipschitzOnWith C α (Icc δ T))
    (hg : ∀ t ∈ Icc δ T, DifferentiableOn ℂ g (ball (α t) r))
    (hi : ∀ t ∈ Icc δ T, InjOn g (ball (α t) r))
    (hH : ∀ t ∈ Icc δ T, MapsTo g (ball (α t) r) upperHalfPlane) :
    LipschitzOnWith ⟨(256 * Real.pi * C) / r, by positivity⟩
      (fun t => Real.log (g (α t)).im) (Icc δ T) := by
  have hc : ContinuousOn (fun t => Real.log (g (α t)).im) (Icc δ T) := by
    intro t ht
    have hh := log_im_fderiv_bound hr (hg t ht) (hi t ht) (hH t ht)
    exact hh.1.continuousAt.comp_continuousWithinAt (hL.continuousOn t ht)
  apply lipschitzOn_of_local_bound (by positivity) hc
  intro t ht
  refine ⟨r / (4 * (C + 1)), by positivity, ?_⟩
  intro u hu hdist
  have hαdist : dist (α u) (α t) < r / 2 := by
    have hb := hL.dist_le_mul u hu t ht
    have hm := (mul_lt_mul_of_pos_left hdist (show (0 : ℝ) < 4 * (C + 1) by positivity))
    have hm' : (4 * (C + 1)) * dist u t < r := by
      simpa only [mul_div_cancel₀ _ (ne_of_gt (show (0 : ℝ) < 4 * (C + 1) by positivity))] using hm
    have hd := dist_nonneg (x := u) (y := t)
    nlinarith
  have hlog := log_im_lipschitz_on_half_ball hr (hg t ht) (hi t ht) (hH t ht)
  have hb := hlog.dist_le_mul (α u) (mem_ball.mpr hαdist)
    (α t) (mem_ball_self (by positivity : 0 < r / 2))
  exact hb.trans (by
    change (256 * Real.pi / r) * dist (α u) (α t) ≤ _
    calc
      _ ≤ (256 * Real.pi / r) * (C * dist u t) :=
        mul_le_mul_of_nonneg_left (hL.dist_le_mul u hu t ht) (by positivity)
      _ = _ := by ring)

/-- A holomorphic derivative bounds the distance quotient from its center
in some neighborhood; no regularity of a curve composed with it is needed. -/
theorem holomorphic_local_distance_bound
    {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w, dist w z < ε →
      dist (g w) (g z) ≤ (‖deriv g z‖ + 1) * dist w z := by
  have he := hg.hasFDerivAt.isLittleO.bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε, hε, ?_⟩
  intro w hw
  have hh := hball (mem_ball.mpr hw)
  change ‖g w - g z - (fderiv ℂ g z) (w - z)‖ ≤ 1 * ‖w - z‖ at hh
  have hlin : ‖(fderiv ℂ g z) (w - z)‖ = ‖deriv g z‖ * ‖w - z‖ := by
    rw [fderiv_eq_smul_deriv, smul_eq_mul, norm_mul, mul_comm]
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖g w - g z‖ ≤ ‖g w - g z - (fderiv ℂ g z) (w - z)‖ +
        ‖(fderiv ℂ g z) (w - z)‖ := by
      simpa only [add_comm] using norm_le_insert' (g w - g z) ((fderiv ℂ g z) (w - z))
    _ ≤ 1 * ‖w - z‖ + ‖deriv g z‖ * ‖w - z‖ := by
      rw [hlin]
      exact add_le_add hh le_rfl
    _ = (‖deriv g z‖ + 1) * ‖w - z‖ := by ring

theorem height_bounds_from_waypoint
    {g : ℂ → ℂ} {α : ℝ → ℂ} {δ T tw r s : ℝ}
    (hr : 0 < r) (C : ℝ≥0) (hs : 0 < s) (htw : tw ∈ Icc δ T)
    (hL : LipschitzOnWith C α (Icc δ T))
    (hg : ∀ t ∈ Icc δ T, DifferentiableOn ℂ g (ball (α t) r))
    (hi : ∀ t ∈ Icc δ T, InjOn g (ball (α t) r))
    (hH : ∀ t ∈ Icc δ T, MapsTo g (ball (α t) r) upperHalfPlane)
    (hway : ‖g (α tw)‖ = 1) (hangle : s ≤ (g (α tw)).im) :
    ∀ t ∈ Icc δ T,
      s * Real.exp (-((256 * Real.pi * C) / r) * (T - δ)) ≤ (g (α t)).im ∧
      (g (α t)).im ≤ Real.exp (((256 * Real.pi * C) / r) * (T - δ)) := by
  let K := (256 * Real.pi * C) / r
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlog := log_height_lipschitz hr C hL hg hi hH
  have hpos (t : ℝ) (ht : t ∈ Icc δ T) : 0 < (g (α t)).im :=
    hH t ht (mem_ball_self hr)
  have hlogway : Real.log (g (α tw)).im ≤ 0 :=
    Real.log_nonpos (hpos tw htw).le ((Complex.im_le_norm _).trans_eq hway)
  have hlogs : Real.log s ≤ Real.log (g (α tw)).im := Real.log_le_log hs hangle
  intro t ht
  have hd := HyperbolicGuideCompactness.interval_dist_le_width ht htw
  have hh := hlog.dist_le_mul t ht tw htw
  change dist (Real.log (g (α t)).im) (Real.log (g (α tw)).im) ≤ K * dist t tw at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hd hK)
  rw [Real.dist_eq] at hh'
  have hlo : Real.log s + (-K * (T - δ)) ≤ Real.log (g (α t)).im := by
    linarith [(abs_le.mp hh').1]
  have hup : Real.log (g (α t)).im ≤ K * (T - δ) := by
    linarith [(abs_le.mp hh').2]
  constructor
  · calc
      s * Real.exp (-K * (T - δ)) = Real.exp (Real.log s + (-K * (T - δ))) := by
        rw [Real.exp_add, Real.exp_log hs]
      _ ≤ Real.exp (Real.log (g (α t)).im) := Real.exp_le_exp.mpr hlo
      _ = (g (α t)).im := Real.exp_log (hpos t ht)
  · simpa only [Real.exp_log (hpos t ht)] using Real.exp_le_exp.mpr hup

def euclideanSpeed (C r δ T : ℝ) : ℝ :=
  ((128 * Real.pi / r) * Real.exp (((256 * Real.pi * C) / r) * (T - δ)) + 1) * C

/-- Common clearance and a waypoint control the full inverse guide's speed
for Lipschitz physical guides, including guides with corners. -/
theorem inverse_guide_lipschitz
    {g : ℂ → ℂ} {α : ℝ → ℂ} {δ T tw r s : ℝ}
    (hr : 0 < r) (C : ℝ≥0) (hs : 0 < s) (htw : tw ∈ Icc δ T)
    (hL : LipschitzOnWith C α (Icc δ T))
    (hg : ∀ t ∈ Icc δ T, DifferentiableOn ℂ g (ball (α t) r))
    (hi : ∀ t ∈ Icc δ T, InjOn g (ball (α t) r))
    (hH : ∀ t ∈ Icc δ T, MapsTo g (ball (α t) r) upperHalfPlane)
    (hway : ‖g (α tw)‖ = 1) (hangle : s ≤ (g (α tw)).im) :
    LipschitzOnWith ⟨euclideanSpeed C r δ T, by dsimp [euclideanSpeed]; positivity⟩
      (g ∘ α) (Icc δ T) := by
  let M := (128 * Real.pi / r) * Real.exp (((256 * Real.pi * C) / r) * (T - δ)) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hheight := height_bounds_from_waypoint hr C hs htw hL hg hi hH hway hangle
  have hgd t (ht : t ∈ Icc δ T) : DifferentiableAt ℂ g (α t) :=
    (hg t ht).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hc : ContinuousOn (g ∘ α) (Icc δ T) := fun t ht =>
    (hgd t ht).continuousAt.comp_continuousWithinAt (hL.continuousOn t ht)
  apply lipschitzOn_of_local_bound (by dsimp [euclideanSpeed]; positivity) hc
  intro t ht
  obtain ⟨ε, hε, hlocal⟩ := holomorphic_local_distance_bound (hgd t ht)
  refine ⟨ε / (C + 1), by positivity, ?_⟩
  intro u hu hdist
  have hαdist : dist (α u) (α t) < ε := by
    have hm := (mul_lt_mul_of_pos_left hdist (show (0 : ℝ) < C + 1 by positivity))
    have hm' : (C + 1) * dist u t < ε := by
      simpa only [mul_div_cancel₀ _ (ne_of_gt (show (0 : ℝ) < C + 1 by positivity))] using hm
    have hb := hL.dist_le_mul u hu t ht
    nlinarith [dist_nonneg (x := u) (y := t)]
  have hder := HyperbolicGuideCompactness.inverse_chart_derivative_bound hr (hg t ht) (hi t ht) (hH t ht)
  have hderM : ‖deriv g (α t)‖ + 1 ≤ M := by
    dsimp [M]
    exact add_le_add (hder.trans (mul_le_mul_of_nonneg_left (hheight t ht).2 (by positivity))) le_rfl
  change dist (g (α u)) (g (α t)) ≤ _
  calc
    _ ≤ (‖deriv g (α t)‖ + 1) * dist (α u) (α t) := hlocal _ hαdist
    _ ≤ M * (C * dist u t) := mul_le_mul hderM (hL.dist_le_mul u hu t ht)
      (dist_nonneg) hM.le
    _ = euclideanSpeed C r δ T * dist u t := by simp only [euclideanSpeed, M, mul_assoc]

def confinementSet (C r s δ T : ℝ) : Set ℂ :=
  closedBall 0 (1 + euclideanSpeed C r δ T * (T - δ)) ∩
    {z | s * Real.exp (-((256 * Real.pi * C) / r) * (T - δ)) ≤ z.im}

theorem family_compact_containment
    (g : ℕ → ℂ → ℂ) (α : ℕ → ℝ → ℂ) {δ T tw r s : ℝ}
    (hr : 0 < r) (C : ℝ≥0) (hs : 0 < s) (htw : tw ∈ Icc δ T)
    (hL : ∀ n, LipschitzOnWith C (α n) (Icc δ T))
    (hg : ∀ n t, t ∈ Icc δ T → DifferentiableOn ℂ (g n) (ball (α n t) r))
    (hi : ∀ n t, t ∈ Icc δ T → InjOn (g n) (ball (α n t) r))
    (hH : ∀ n t, t ∈ Icc δ T → MapsTo (g n) (ball (α n t) r) upperHalfPlane)
    (hway : ∀ n, ‖g n (α n tw)‖ = 1) (hangle : ∀ n, s ≤ (g n (α n tw)).im) :
    ∃ Q : Set ℂ, IsCompact Q ∧ Q ⊆ upperHalfPlane ∧
      (∀ n, MapsTo (g n ∘ α n) (Icc δ T) Q) ∧
      UniformEquicontinuousOn (fun n => g n ∘ α n) (Icc δ T) := by
  have hLip n := inverse_guide_lipschitz hr C hs htw (hL n) (hg n) (hi n) (hH n)
    (hway n) (hangle n)
  refine ⟨confinementSet C r s δ T,
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im),
    ?_, ?_, LipschitzOnWith.uniformEquicontinuousOn _ _ hLip⟩
  · intro z hz
    exact (mul_pos hs (Real.exp_pos _)).trans_le hz.2
  · intro n t ht
    refine ⟨?_, (height_bounds_from_waypoint hr C hs htw (hL n) (hg n) (hi n) (hH n)
      (hway n) (hangle n) t ht).1⟩
    have hd := (hLip n).dist_le_mul t ht tw htw
    have hwidth := HyperbolicGuideCompactness.interval_dist_le_width ht htw
    have hspeed : 0 ≤ euclideanSpeed C r δ T := by dsimp [euclideanSpeed]; positivity
    have hh := hd.trans (mul_le_mul_of_nonneg_left hwidth hspeed)
    change dist (g n (α n t)) (g n (α n tw)) ≤ euclideanSpeed C r δ T * (T - δ) at hh
    have hn := norm_le_norm_add_const_of_dist_le hh
    simpa only [mem_closedBall, dist_zero_right, Function.comp_apply, hway n] using hn

end SLEExactGauge.LipschitzGuideConfinement

end

end OAI
