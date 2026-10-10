import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedPrimitiveCharacters
open scoped BigOperators

theorem conductor_mul_of_coprime {N : ℕ} [NeZero N]
    (χ ψ : DirichletCharacter ℂ N) (h : Nat.Coprime χ.conductor ψ.conductor) :
    (χ*ψ).conductor = χ.conductor * ψ.conductor := by
  apply Nat.dvd_antisymm
  · exact (DirichletCharacter.conductor_mul_dvd_lcm_conductor χ ψ).trans (Nat.lcm_dvd_mul _ _)
  · apply h.mul_dvd_of_dvd_of_dvd
    · apply h.dvd_of_dvd_mul_right
      have he := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ*ψ) ψ⁻¹
      simp only [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at he
      exact he.trans (Nat.lcm_dvd_mul _ _)
    · apply h.symm.dvd_of_dvd_mul_right
      have he := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ*ψ) χ⁻¹
      have hc : (χ*ψ)*χ⁻¹ = ψ := by simp [mul_assoc]
      rw [hc, DirichletCharacter.conductor_inv] at he
      exact he.trans (Nat.lcm_dvd_mul _ _)

theorem conductor_prod_of_pairwise {ι : Type*} [DecidableEq ι] {N : ℕ} [NeZero N]
    (s : Finset ι) (χ : ι → DirichletCharacter ℂ N)
    (h : (s : Set ι).Pairwise (fun i j => Nat.Coprime (χ i).conductor (χ j).conductor)) :
    (∏ i ∈ s, χ i).conductor = ∏ i ∈ s, (χ i).conductor := by
  induction s using Finset.induction_on with
  | empty => simp [DirichletCharacter.conductor_one]
  | @insert a s ha ih =>
    have hs : (s : Set ι).Pairwise (fun i j => Nat.Coprime (χ i).conductor (χ j).conductor) :=
      h.mono (Finset.subset_insert a s)
    have hc : Nat.Coprime (χ a).conductor (∏ i ∈ s, (χ i).conductor) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro i hi
      apply h (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
      intro he
      exact ha (he.symm ▸ hi)
    rw [Finset.prod_insert ha, conductor_mul_of_coprime, ih hs, Finset.prod_insert ha]
    rw [ih hs]
    exact hc

theorem conductor_prime (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) :
    χ.conductor = if χ = 1 then 1 else p := by
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  by_cases hχ : χ = 1
  · rw [ite_eq_left hχ, hχ, DirichletCharacter.conductor_one]
  · rw [ite_eq_right hχ]
    rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with hc | hc
    · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc))
    · exact hc

end Ostmann.Supply.GroupedPrimitiveCharacters

end

end OAI
