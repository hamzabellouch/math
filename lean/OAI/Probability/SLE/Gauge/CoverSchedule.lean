import OAI.Probability.SLE.Gauge.DenseVisitNumerics

namespace OAI

/-! The common deterministic physical mesh and geometric clock radii in
the explicit-gauge cover. The cutoff depends on the multiplicity and
radius, never on the stopped state or spatial center. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace SLEExactGauge

def coverRadius (T : ℝ) (j : ℕ) : ℝ := Real.exp (-T * (j : ℝ))

theorem coverRadius_pos (T : ℝ) (j : ℕ) : 0 < coverRadius T j := Real.exp_pos _

theorem coverRadius_antitone {T : ℝ} (hT : 0 ≤ T) : Antitone (coverRadius T) := by
  intro i j hij
  apply Real.exp_le_exp.mpr
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

theorem coverRadius_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (coverRadius T) atTop (𝓝 0) := by
  have he : Real.exp (-T) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-T)).le he using 1
  funext j
  simp only [coverRadius, ← Real.exp_nat_mul]
  congr 1
  ring

theorem coverRadius_third_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => coverRadius T (n / 3)) atTop (𝓝 0) := by
  apply (coverRadius_tendsto_zero hT).comp
  apply Filter.tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (3 * N)] with n hn
  omega

theorem coverRadius_window_upper {T : ℝ} (hT : 0 ≤ T) {n j : ℕ}
    (hj : j ∈ coverTestWindow n) : coverRadius T j ≤ coverRadius T (n / 3) :=
  coverRadius_antitone hT (Finset.mem_Icc.mp hj).1

/-- The one-unit angle test and the dense experiment both finish before
the next scheduled radius. -/
theorem coverRadius_next_below_dense_cutoff
    {T C₁ : ℝ} (hC₁ : 0 < C₁) (hgap : 1 + Real.log C₁ < T) (j : ℕ) :
    coverRadius T (j + 1) < Real.exp (-1) * coverRadius T j / C₁ := by
  have he : coverRadius T (j + 1) = coverRadius T j * Real.exp (-T) := by
    simp only [coverRadius, Nat.cast_add, Nat.cast_one, ← Real.exp_add]
    congr 1
    ring
  rw [he, mul_comm (Real.exp (-1)), mul_div_assoc]
  apply mul_lt_mul_of_pos_left _ (coverRadius_pos T j)
  rw [← Real.exp_log hC₁, ← Real.exp_sub]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- One sequence works at every test and every center. It has strict slack
below all dense-visit cutoffs, even though those cutoffs vary with `m_n`. -/
theorem exists_cover_physical_mesh
    (T c : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    ∃ v : ℕ → ℝ, (∀ n, 0 < v n) ∧
      Tendsto v atTop (𝓝 0) ∧ (∀ n, v (n + 1) ≤ v n / 2) ∧
      (∀ n, v n ≤ (2 : ℝ) ^ (-(n : ℝ))) ∧
      ∀ n j, j ∈ coverTestWindow n →
        v n < Real.exp (-1) * coverRadius T j * δ (coverMultiplicity c n) := by
  let cutoff := fun n j => Real.exp (-1) * coverRadius T j * δ (coverMultiplicity c n) / 2
  have hcut : ∀ n j, j ∈ coverTestWindow n → 0 < cutoff n j := by
    intro n j _
    dsimp only [cutoff]
    exact div_pos (mul_pos (mul_pos (Real.exp_pos _) (coverRadius_pos T j)) (hδ _))
      (by norm_num)
  obtain ⟨v, hv, hdyadic, hhalf, htest, hlim⟩ :=
    CoverMesh.exists_common_mesh coverTestWindow cutoff hcut
  refine ⟨v, hv, hlim, hhalf, hdyadic, ?_⟩
  intro n j hj
  refine (htest n j hj).trans_lt ?_
  have hp : 0 < Real.exp (-1) * coverRadius T j * δ (coverMultiplicity c n) :=
    mul_pos (mul_pos (Real.exp_pos _) (coverRadius_pos T j)) (hδ _)
  dsimp only [cutoff]
  linarith

/-- A common diameter bound for the selected enlarged disks and the fine
grid cells tends to zero. -/
theorem cover_diameter_tendsto_zero {T : ℝ} (hT : 0 < T) (A B : ℝ) :
    Tendsto (fun n => ENNReal.ofReal
      (max (A * coverRadius T (n / 3)) (B * coverRadius T n))) atTop (𝓝 0) := by
  have ht := ((coverRadius_third_tendsto_zero hT).const_mul A).max
    ((coverRadius_tendsto_zero hT).const_mul B)
  simpa only [Function.comp_def, mul_zero, max_self, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

end SLEExactGauge

end

end OAI
