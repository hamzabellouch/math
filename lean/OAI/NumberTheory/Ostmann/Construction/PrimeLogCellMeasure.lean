import OAI.NumberTheory.Ostmann.Tree.CoordinateAverages
import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellUpper
import OAI.NumberTheory.Ostmann.Construction.GiantLogMeasures

namespace OAI

/-! # The exact atomic measure of a harmonic prime cell -/

namespace Ostmann
open MeasureTheory Filter
open scoped BigOperators ENNReal BoundedContinuousFunction

instance finite_primeLogAtom (p : ℕ) :
    IsFiniteMeasure (ENNReal.ofReal ((p : ℝ)⁻¹) • Measure.dirac (Real.log p)) :=
  (Measure.dirac (Real.log p)).smul_finite ENNReal.ofReal_ne_top

noncomputable def primeLogCellMeasure (q a : ℕ) (u v : ℝ) : Measure ℝ :=
  ∑ p ∈ primeLogCellSet q a u v, ENNReal.ofReal ((p : ℝ)⁻¹) • Measure.dirac (Real.log p)

instance finite_primeLogCellMeasure (q a : ℕ) (u v : ℝ) :
    IsFiniteMeasure (primeLogCellMeasure q a u v) := by
  unfold primeLogCellMeasure
  infer_instance

theorem primeLogCellMeasure_integral (q a : ℕ) (u v : ℝ) (f : ℝ →ᵇ ℂ) :
    (∫ t, f t ∂primeLogCellMeasure q a u v) =
      ∑ p ∈ primeLogCellSet q a u v, f (Real.log p) * ((p : ℝ)⁻¹ : ℂ) := by
  unfold primeLogCellMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_comm]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro p _
    exact f.integrable _

theorem primeLogCellMeasure_mass (q a : ℕ) (u v : ℝ) :
    (primeLogCellMeasure q a u v).real Set.univ =
      ∑ p ∈ primeLogCellSet q a u v, (p : ℝ)⁻¹ := by
  have h := primeLogCellMeasure_integral q a u v (BoundedContinuousFunction.const ℝ (1 : ℂ))
  simp only [BoundedContinuousFunction.const_apply, integral_const, Complex.real_smul,
    mul_one, one_mul] at h
  exact_mod_cast h

/-- All residue classes and shorter cells obey the same eventual mass bound. -/
theorem PublishedProgressionInput.primeLogCellMeasure_mass_eventually (P : PublishedProgressionInput) :
    ∀ᶠ u : ℝ in atTop, ∀ q a : ℕ, ∀ v : ℝ, v ≤ u + 1 →
      (primeLogCellMeasure q a u v).real Set.univ ≤ 2 := by
  filter_upwards [P.prime_log_cell_upper, eventually_ge_atTop (1 : ℝ)] with u hu hu1 q a v hv
  rw [primeLogCellMeasure_mass]
  apply (hu _ ?_).trans
  · exact (div_le_iff₀ (by linarith : 0 < u)).mpr (by linarith)
  · intro p hp
    simp only [primeLogCellSet, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_le_floor (Real.exp_le_exp.mpr hv))⟩,
      hp.2.1, by simp only [Nat.ModEq, Nat.mod_one]⟩

end Ostmann

end OAI
