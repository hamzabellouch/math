import OAI.Geometry.EinsteinFour.JacobiRatioLimit

namespace OAI

/-! Uniform inverse control at every node of a preconjugate mesh. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

theorem isUnit_of_divided_time {R : Type*} [Ring R] [Algebra ℝ R]
    {X : R} {s : ℝ} (hs : s ≠ 0) (hX : IsUnit (s⁻¹ • X)) : IsUnit X := by
  have hu : IsUnit (algebraMap ℝ R s) :=
    (isUnit_iff_ne_zero.mpr hs).map (algebraMap ℝ R)
  have h := hu.mul hX
  simpa only [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hs, one_smul] using h

/-- Invertibility is uniform on the whole closed preconjugate interval;
the error threshold is independent of the mesh node. -/
theorem eventually_mesh_inverse_bounds
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {t : ℝ} (ht : 0 ≤ t) {B : ℝ → R}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {b : ℕ → ℕ → R} {e : ℕ → ℝ} (he : Tendsto e atTop (nhds 0))
    (herror : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      ‖b N i - B ((i : ℝ) * (t / (N + 1)))‖ ≤ e N) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      IsUnit (b N i) ∧ ‖Ring.inverse (b N i)‖ ≤ 2 * K ∧
        ‖Ring.inverse (b N i) - Ring.inverse (B ((i : ℝ) * (t / (N + 1))))‖ ≤
          2 * K ^ 2 * e N := by
  obtain ⟨K, hK, hb⟩ := uniform_inverse_neighborhood hB hunit
  refine ⟨K, hK, ?_⟩
  filter_upwards [herror, he.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * K)))] with N hN heN
  intro i hi
  have hh : 0 ≤ t / (N + 1 : ℝ) := div_nonneg ht (by positivity)
  have hs : (i : ℝ) * (t / (N + 1)) ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · calc
        _ ≤ (N + 1 : ℝ) * (t / (N + 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh
        _ = t := by field_simp
  obtain ⟨hu, hn, hd⟩ := hb _ hs (b N i) ((hN i hi).trans heN.le)
  exact ⟨hu, hn, hd.trans (mul_le_mul_of_nonneg_left (hN i hi) (by positivity))⟩

end

end PositiveEinsteinFour.Jacobi

end OAI
