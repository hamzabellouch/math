import OAI.Geometry.EinsteinFour.JacobiNormalized

namespace OAI

/-! Uniform convergence of the normalized velocity gives positivity of all
discrete Jacobi ratios, including the first nodes next to zero. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

theorem inverse_product_error
    {R : Type*} [NormedRing R] {B b V v : R} {K M : ℝ}
    (hb : ‖Ring.inverse b‖ ≤ K) (hV : ‖V‖ ≤ M) :
    ‖v * Ring.inverse b - V * Ring.inverse B‖ ≤
      K * ‖v - V‖ + M * ‖Ring.inverse b - Ring.inverse B‖ := by
  have hid : v * Ring.inverse b - V * Ring.inverse B =
      (v - V) * Ring.inverse b + V * (Ring.inverse b - Ring.inverse B) := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(v - V) * Ring.inverse b‖ + ‖V * (Ring.inverse b - Ring.inverse B)‖ :=
      norm_add_le _ _
    _ ≤ ‖v - V‖ * ‖Ring.inverse b‖ + ‖V‖ * ‖Ring.inverse b - Ring.inverse B‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ K * ‖v - V‖ + M * ‖Ring.inverse b - Ring.inverse B‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (v - V)),
        mul_le_mul_of_nonneg_right hV (norm_nonneg (Ring.inverse b - Ring.inverse B))]

/-- Uniform approximation survives multiplication by the inverse on a
compact interval of invertible reference matrices. -/
theorem uniform_inverse_product_approximation
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {B V : ℝ → R} {t : ℝ}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {b v : ℕ → ℝ → R} {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0)) (hepos : ∀ N, 0 ≤ e N)
    (hb : ∀ᶠ N in atTop, ∀ s ∈ Set.Icc 0 t, ‖b N s - B s‖ ≤ e N)
    (hv : ∀ᶠ N in atTop, ∀ s ∈ Set.Icc 0 t, ‖v N s - V s‖ ≤ e N) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N in atTop, ∀ s ∈ Set.Icc 0 t,
      IsUnit (b N s) ∧
        ‖v N s * Ring.inverse (b N s) - V s * Ring.inverse (B s)‖ ≤ D * e N := by
  obtain ⟨K, hK, hinv⟩ := uniform_inverse_neighborhood hB hunit
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let D : ℝ := 2 * K + 2 * M * K ^ 2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [hb, hv, he.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * K)))] with N hbN hvN heN
  intro s hs
  obtain ⟨hbu, hbi, hbd⟩ := hinv s hs (b N s) ((hbN s hs).trans heN.le)
  refine ⟨hbu, ?_⟩
  calc
    _ ≤ (2 * K) * ‖v N s - V s‖ + M * ‖Ring.inverse (b N s) - Ring.inverse (B s)‖ :=
      inverse_product_error hbi ((hM₀ s hs).trans (le_max_left _ _))
    _ ≤ (2 * K) * e N + M * (2 * K ^ 2 * e N) := by
      gcongr
      · exact hvN s hs
      · exact hbd.trans (mul_le_mul_of_nonneg_left (hbN s hs) (by positivity))
    _ ≤ D * e N := by dsimp [D]; nlinarith [hepos N]

/-- Uniform convergence to a continuous coefficient whose initial value
is the identity gives a single mesh threshold for every positive node. -/
theorem eventually_mesh_ratio_positive
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {t : ℝ} (ht : 0 < t) {C : ℝ → F →L[ℝ] F}
    (hC : ContinuousOn C (Set.Icc 0 t)) (hC0 : C 0 = ContinuousLinearMap.id ℝ F)
    {P : ℕ → ℕ → F →L[ℝ] F} {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0))
    (happrox : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ ≤ e N) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N → ∀ x : F, x ≠ 0 →
      0 < inner ℝ ((ContinuousLinearMap.id ℝ F + ((1 : ℝ) / i) • P N i) x) x := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  let K : ℝ := max (M + 1) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousWithinAt_iff.mp
    (hC 0 ⟨le_rfl, ht.le⟩)) (1 / 2) (by norm_num)
  let η : ℝ := δ / 2
  have hη : 0 < η := half_pos hδ
  have hmesh : Tendsto (fun N : ℕ => (t / (N + 1)) * K) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat t).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using
      h.mul_const K
  filter_upwards [happrox, he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hmesh.eventually (gt_mem_nhds hη)] with N hN heN hmN
  intro i hi hiN x hx
  have hh : 0 < t / (N + 1 : ℝ) := div_pos ht (by positivity)
  have his : (i : ℝ) * (t / (N + 1)) ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · have hi' : (i : ℝ) ≤ N + 1 := by exact_mod_cast hiN.trans (Nat.le_succ N)
      calc
        _ ≤ (N + 1 : ℝ) * (t / (N + 1)) := mul_le_mul_of_nonneg_right hi' hh.le
        _ = t := by field_simp
  have hb : ‖P N i‖ ≤ K := by
    calc
      _ ≤ ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ +
          ‖C ((i : ℝ) * (t / (N + 1)))‖ := norm_le_norm_sub_add _ _
      _ ≤ e N + M := add_le_add (hN i hi hiN) (hM _ his)
      _ ≤ M + 1 := by linarith
      _ ≤ K := le_max_left _ _
  apply mesh_ratio_quadratic_pos hi hh hmN hb ?_ hx
  intro hs
  have hd : dist ((i : ℝ) * (t / (N + 1))) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg his.1]
    exact lt_of_le_of_lt hs (by dsimp [η]; linarith)
  have hc := hnear his hd
  rw [hC0, dist_eq_norm] at hc
  calc
    _ ≤ ‖P N i - C ((i : ℝ) * (t / (N + 1)))‖ +
        ‖C ((i : ℝ) * (t / (N + 1))) - ContinuousLinearMap.id ℝ F‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ e N + ‖C ((i : ℝ) * (t / (N + 1))) - ContinuousLinearMap.id ℝ F‖ :=
      add_le_add_left (hN i hi hiN) _
    _ < 1 := by linarith

end

end PositiveEinsteinFour.Jacobi

end OAI
