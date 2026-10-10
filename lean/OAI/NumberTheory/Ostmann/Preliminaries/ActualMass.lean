import OAI.NumberTheory.Ostmann.Preliminaries.ProjectedMass
import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem projected_A_supported (d : Decomposition) (p : ℕ) [NeZero p]
    (a : α → ℕ) (μ : α → ℝ)
    (hA : ∀ i, μ i ≠ 0 → a i ∈ d.A)
    (hlarge : ∀ i, μ i ≠ 0 → p + d.cutoff < a i) :
    ∀ r ∉ d.residueSupport p, projectedMass (fun i => (a i : ZMod p)) μ r = 0 := by
  intro r hr
  exact projectedMass_eq_zero _ μ _ (fun i hi =>
    (d.mem_residueSupport p _).mpr ⟨a i, hA i hi, hlarge i hi, rfl⟩) hr

theorem projected_neg_B_supported (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) (b : α → ℕ) (ν : α → ℝ)
    (hB : ∀ i, ν i ≠ 0 → b i ∈ d.B)
    (hlarge : ∀ i, ν i ≠ 0 → p + d.cutoff < b i) :
    ∀ r ∉ (d.residueSupport p)ᶜ, projectedMass (fun i => -(b i : ZMod p)) ν r = 0 := by
  intro r hr
  exact projectedMass_eq_zero _ ν _ (fun i hi =>
    d.negResidueSupport_subset_compl p hp
      ((d.mem_negResidueSupport p _).mpr ⟨b i, hB i hi, hlarge i hi, rfl⟩)) hr

theorem neg_projectedMass_energy_eq_pos {p : ℕ} [NeZero p] (b : α → ℕ) (ν : α → ℝ) :
    massEnergy (projectedMass (fun i => -(b i : ZMod p)) ν) =
      massEnergy (projectedMass (fun i => (b i : ZMod p)) ν) := by
  simp only [projectedMass_energy, neg_inj]

theorem actual_A_test_error (d : Decomposition) (p : ℕ) [NeZero p]
    (a : α → ℕ) (μ : α → ℝ) (f : ZMod p → ℂ)
    (hf : ∑ r, ‖f r‖ ^ 2 ≤ p) :
    ‖(∑ i, (μ i : ℂ) * f (a i)) -
      ∑ r, (uniformMass (d.residueSupport p) r : ℂ) * f r‖ ^ 2 ≤
      (p : ℝ) * uniformDefect (d.residueSupport p)
        (projectedMass (fun i => (a i : ZMod p)) μ) := by
  have h := test_error_sq_le_card_mul_defect (d.residueSupport p)
    (projectedMass (fun i => (a i : ZMod p)) μ) f (by simpa only [ZMod.card p] using hf)
  simp only [ZMod.card p, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    projectedMass_complex_test] at h
  exact h

theorem actual_neg_B_test_error (d : Decomposition) (p : ℕ) [NeZero p]
    (b : α → ℕ) (ν : α → ℝ) (f : ZMod p → ℂ)
    (hf : ∑ r, ‖f r‖ ^ 2 ≤ p) :
    ‖(∑ i, (ν i : ℂ) * f (-(b i : ZMod p))) -
      ∑ r, (uniformMass (d.residueSupport p)ᶜ r : ℂ) * f r‖ ^ 2 ≤
      (p : ℝ) * uniformDefect (d.residueSupport p)ᶜ
        (projectedMass (fun i => -(b i : ZMod p)) ν) := by
  have h := test_error_sq_le_card_mul_defect (d.residueSupport p)ᶜ
    (projectedMass (fun i => -(b i : ZMod p)) ν) f (by simpa only [ZMod.card p] using hf)
  simp only [ZMod.card p, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    projectedMass_complex_test] at h
  exact h

end Ostmann.Preliminaries

end OAI
