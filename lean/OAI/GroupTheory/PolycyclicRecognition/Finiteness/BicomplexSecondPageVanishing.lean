import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexSecondPageFiniteness

namespace OAI

/-! # Vanishing from the finite second-page diagonal -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module Submodule.module
variable {R : Type} [CommRing R] (K : NatBicomplex R)

theorem bicomplex_total_homology_isZero_of_secondPage (n : ℕ)
    (hz : ∀ p j, p + j = n → Limits.IsZero ((rowHomologyComplex K j).homology p)) :
    Limits.IsZero ((K.total (ComplexShape.down ℕ)).homology n) := by
  have hf : ∀ p, p ≤ n + 1 → filteredTotalHomology K n p = ⊥ := by
    intro p
    induction p with
    | zero => intro _; exact filteredTotalHomology_zero K n
    | succ p ih =>
      intro hp
      have hpn : p ≤ n := by omega
      let j := n - p
      have hj : p + j = n := by dsimp [j]; omega
      let := (ModuleCat.isZero_iff_subsingleton).mp (hz p j hj)
      apply bot_unique
      rintro a ⟨x, rfl⟩
      have hx : boundedTotalSecondPageClass K n p j hj x = 0 := Subsingleton.elim _ _
      have hlow := zero_secondPage_class_lowers_filtration K n p j hj x hx
      rwa [ih (by omega)] at hlow
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have he (a : (K.total (ComplexShape.down ℕ)).homology n) : a = 0 := by
    have ha : a ∈ filteredTotalHomology K n (n + 1) := by
      rw [filteredTotalHomology_top K n (n + 1) (by omega)]
      trivial
    simpa only [hf (n + 1) le_rfl, Submodule.mem_bot] using ha
  exact ⟨fun a b => (he a).trans (he b).symm⟩

theorem bicomplex_total_homology_isZero_above_secondPage (a b : ℕ)
    (hz : ∀ p j, a < p ∨ b < j →
      Limits.IsZero ((rowHomologyComplex K j).homology p))
    (n : ℕ) (hn : a + b < n) :
    Limits.IsZero ((K.total (ComplexShape.down ℕ)).homology n) := by
  apply bicomplex_total_homology_isZero_of_secondPage K n
  intro p j hpj
  exact hz p j (by omega)

end PolycyclicRecognition

end

end OAI
