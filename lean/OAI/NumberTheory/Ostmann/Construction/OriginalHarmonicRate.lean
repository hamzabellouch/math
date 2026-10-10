import OAI.NumberTheory.Ostmann.Construction.PrimeCellMassRate
import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellUpper

namespace OAI

/-! # The required real box mass under the original deleted prior -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

theorem deleted_prime_mass_relative_rate (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (S D : Finset ℕ) (T : ℝ),
      (D.card : ℝ) ≤ Real.exp (C * L) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ p ∈ S, Real.exp T ≤ (p : ℝ)) →
        (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ Real.exp (-C * L) / 4 := by
  filter_upwards [arithmetic_error_absorption 0 (39 / 10000) (2 / 1000) (C + 1) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    double_exp_below_original_mass (2 / 1000) C (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hrelative hL
  intro S D T hD hT hlow
  apply (bulk_deleted_reciprocal_mass_le S D T hlow).trans
  apply le_trans _ (hrate.trans hrelative)
  apply mul_le_mul
  · apply hD.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_one, zero_mul, Real.exp_zero, mul_one]
    have hL0 : 0 ≤ L := by linarith
    nlinarith [mul_nonneg hC hL0]
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_nonneg _
  · exact Real.exp_nonneg _

theorem PublishedProgressionInput.short_prime_cell_mass_two (P : PublishedProgressionInput) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ q a : ℕ, ∀ u v : ℝ, T ≤ u → v ≤ u + 1 →
      (∑ p ∈ primeLogCellSet q a u v, (p : ℝ)⁻¹) ≤ 2 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp P.prime_log_cell_upper
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro q a u v hu hv
  have hu1 : 1 ≤ u := (le_max_right T 1).trans hu
  have hsub : primeLogCellSet q a u v ⊆ primeLogCellSet 1 0 u (u + 1) := by
    intro p hp
    obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hp
    exact mem_primeLogCellSet_iff.mpr ⟨hpp, by simp only [Nat.modEq_one], hlo, hhi.trans hv⟩
  apply (hT u ((le_max_left T 1).trans hu) _ hsub).trans
  exact (div_le_iff₀ (by linarith : 0 < u)).mpr (by linarith)

/-- The three original-prior mass premises used by the signed bulk bound
hold simultaneously. No renormalization after idealization is introduced. -/
theorem PublishedProgressionInput.original_harmonic_box_rate (P : PublishedProgressionInput)
    (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (Cell : Type) [Fintype Cell] (Q : ℕ), 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      ∀ (u v : Cell → ℝ) (D : Finset ℕ),
      (∀ c, 1 ≤ u c) → (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u c) →
      (∀ c, u c ≤ v c) → (∀ c, v c ≤ u c + 1) →
      (∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c) →
      (D.card : ℝ) ≤ Real.exp (C * L) →
      let S := primeCellSupport 1 (fun _ : Cell => 0) u v
      Real.exp (-C * L) ≤ (∑ p ∈ S, (p : ℝ)⁻¹) →
        0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
        (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp ((C + 1) * L) ∧
        (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ *
          (∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹) ≤ 2 := by
  filter_upwards [P.short_cell_mass_error_relative C, deleted_prime_mass_relative_rate C (by linarith),
    retained_prime_normalizer_rate C hC] with L herror hdelete hnorm
  intro Cell _ Q hQ hlog hcard u v D hu hlow huv hshort hsep hD S hmass
  have hS (p) (hp : p ∈ S) : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpp, _, hplog, _⟩ := mem_primeLogCellSet_iff.mp hc
    exact (Real.le_log_iff_exp_le (by exact_mod_cast hpp.pos)).mp ((hlow c).trans hplog.le)
  have hdeleted := hdelete S D _ hD le_rfl hS
  have hm := hnorm S D _ hmass hD le_rfl hS
  refine ⟨hm.1, hm.2, ?_⟩
  exact P.original_harmonic_box_mass Q hQ u v hu huv hshort hsep D _ (Real.exp_pos _)
    hmass hdeleted (herror Cell Q hQ hlog hcard u hlow)

end Ostmann

end OAI
