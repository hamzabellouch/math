import OAI.Geometry.EinsteinFour.JacobiMeshInverse

namespace OAI

/-! Uniform approximation of the velocity times normalized-position inverse. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

theorem inverse_product_continuousOn
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {B V : ℝ → R} {t : ℝ}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s)) :
    ContinuousOn (fun s => V s * Ring.inverse (B s)) (Set.Icc 0 t) := by
  apply hV.mul
  intro s hs
  have hi : ContinuousAt (Ring.inverse : R → R) (B s) := by
    simpa using NormedRing.inverse_continuousAt (hunit s hs).unit
  exact hi.comp_continuousWithinAt (hB s hs)

theorem mesh_inverse_product_converges
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {t : ℝ} (ht : 0 ≤ t) {B V : ℝ → R}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {b v : ℕ → ℕ → R} {eB eV : ℕ → ℝ}
    (heB : Tendsto eB atTop (nhds 0)) (heV : Tendsto eV atTop (nhds 0))
    (hb : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      ‖b N i - B ((i : ℝ) * (t / (N + 1)))‖ ≤ eB N)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N →
      ‖v N i - V ((i : ℝ) * (t / (N + 1)))‖ ≤ eV N) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N → IsUnit (b N i) ∧
        ‖v N i * Ring.inverse (b N i) -
          V ((i : ℝ) * (t / (N + 1))) *
            Ring.inverse (B ((i : ℝ) * (t / (N + 1))))‖ ≤ e N := by
  obtain ⟨K, hK, hinv⟩ := eventually_mesh_inverse_bounds ht hB hunit heB hb
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let e : ℕ → ℝ := fun N => 2 * K * eV N + M * (2 * K ^ 2 * eB N)
  have he : Tendsto e atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (heV.const_mul (2 * K)).add ((heB.const_mul (2 * K ^ 2)).const_mul M)
  refine ⟨e, he, ?_⟩
  filter_upwards [hinv, hv] with N hN hvN
  intro i hi
  obtain ⟨hu, hn, hd⟩ := hN i (hi.trans (Nat.le_succ N))
  have hs : (i : ℝ) * (t / (N + 1)) ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · calc
        _ ≤ (N + 1 : ℝ) * (t / (N + 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi.trans (Nat.le_succ N))
            (div_nonneg ht (by positivity))
        _ = t := by field_simp
  refine ⟨hu, ?_⟩
  calc
    _ ≤ (2 * K) * ‖v N i - V ((i : ℝ) * (t / (N + 1)))‖ +
        M * ‖Ring.inverse (b N i) - Ring.inverse (B ((i : ℝ) * (t / (N + 1))))‖ :=
      inverse_product_error hn ((hM₀ _ hs).trans (le_max_left _ _))
    _ ≤ e N := by
      dsimp [e]
      gcongr
      · exact hvN i hi

end

end PositiveEinsteinFour.Jacobi

end OAI
