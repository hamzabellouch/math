import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor
import OAI.Combinatorics.Chromatic.Witness.WitnessTransport

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {A B:Type*} [Fintype A] [Fintype B]

lemma coefficient_energy_sum (M:ℕ) (E:A → ℕ) (k:ℕ) :
    (∑a,(↑(LaurentRay.vUnit^(2*(E a:ℤ)-(M:ℤ))):LaurentSeries ℚ)).coeff ((M:ℤ)-2*(k:ℤ))=
      (Fintype.card {a // E a=k}:ℚ) := by
  rw [HahnSeries.coeff_sum]
  simp only [LaurentRay.vUnit_zpow,HahnSeries.coeff_single]
  have he:∀a,((M:ℤ)-2*(k:ℤ)= -(2*(E a:ℤ)-(M:ℤ))) ↔ E a=k:=by intro a; omega
  simp_rw [he]
  rw [←Finset.sum_filter]
  simp [Fintype.card_subtype]

lemma fiber_card_of_energy_sum (M:ℕ) (EA:A → ℕ) (EB:B → ℕ)
    (h:(∑a,(↑(LaurentRay.vUnit^(2*(EA a:ℤ)-(M:ℤ))):LaurentSeries ℚ))=
      ∑b,(↑(LaurentRay.vUnit^(2*(EB b:ℤ)-(M:ℤ))):LaurentSeries ℚ)) (k:ℕ) :
    Fintype.card {a // EA a=k}=Fintype.card {b // EB b=k} := by
  have H:=congrArg (fun w:LaurentSeries ℚ=>w.coeff ((M:ℤ)-2*(k:ℤ))) h
  rw [coefficient_energy_sum,coefficient_energy_sum] at H
  exact_mod_cast H

def gradedEquivOfEnergySum (M:ℕ) (EA:A → ℕ) (EB:B → ℕ)
    (h:(∑a,(↑(LaurentRay.vUnit^(2*(EA a:ℤ)-(M:ℤ))):LaurentSeries ℚ))=
      ∑b,(↑(LaurentRay.vUnit^(2*(EB b:ℤ)-(M:ℤ))):LaurentSeries ℚ)) :
    ExactMasks.GradedEquiv EA EB :=
  ⟨Equiv.ofFiberEquiv (fun k=>Fintype.equivOfCardEq (fiber_card_of_energy_sum M EA EB h k)),
    Equiv.ofFiberEquiv_map _⟩
end
end ElementaryPositivity.LaurentPositive

end

end OAI
