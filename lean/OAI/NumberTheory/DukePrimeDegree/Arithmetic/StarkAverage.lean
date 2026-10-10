import OAI.NumberTheory.DukePrimeDegree.Arithmetic.SubfieldOrders
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicGluing

namespace OAI

/-!
# Recovering the fixed-field zero order from cyclic averages

This is the scalar form of Stark's descent: the same cyclic indicator
coefficients recover both a class-function average and the zero order of
the corresponding fixed-field zeta function.
-/

noncomputable section
open scoped BigOperators Classical NumberField

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]
local instance : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _

theorem sum_eq_fixedFieldMultiplicity_of_cyclic_averages
    (f : (E ≃ₐ[F] E) → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[F] E), IsCyclic C →
      (∑ g : C, f g) = Fintype.card C * (fixedFieldMultiplicity β C : ℝ))
    (H : Subgroup (E ≃ₐ[F] E)) :
    (∑ g : H, f g) = Fintype.card H * (fixedFieldMultiplicity β H : ℝ) := by
  obtain ⟨a, ha⟩ := exists_cyclic_indicator_coefficients H
  have hs (C : CyclicSubgroups H) :
      (∑ g : C.val, f (g : H)) =
        Fintype.card (C.val.map H.subtype) *
          (fixedFieldMultiplicity β (C.val.map H.subtype) : ℝ) := by
    let e := C.val.equivMapOfInjective H.subtype H.subtype_injective
    have hC : IsCyclic (C.val.map H.subtype) := e.isCyclic.mp C.property
    rw [← hcyclic _ hC]
    exact Fintype.sum_equiv e.toEquiv (fun g : C.val => f (g : H))
      (fun g : C.val.map H.subtype => f g)
      (fun _ => rfl)
  rw [sum_real_eq_cyclic_sums a ha (fun h : H => f h)]
  simp_rw [hs]
  have hord := fixedFieldMultiplicity_cyclic_relation H
    (fun C => a C * Fintype.card (C.val.map H.subtype))
    (cyclic_permutation_character_identity_inside H a ha) hβ0 hβ1
  have hcast : (∑ C : CyclicSubgroups H,
      (a C : ℝ) * Fintype.card (C.val.map H.subtype) *
        (fixedFieldMultiplicity β (C.val.map H.subtype) : ℝ)) =
      Fintype.card H * (fixedFieldMultiplicity β H : ℝ) := by
    exact_mod_cast hord
  simpa only [mul_assoc] using hcast

/-- A cyclicly linear zero-order sign function cannot have average one
on an odd-index subgroup and average zero on the full Galois group. -/
theorem no_odd_index_zero_sign
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[F] E), IsCyclic C → ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[F] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0)
    (H : Subgroup (E ≃ₐ[F] E)) (hodd : Odd H.index)
    (hH : fixedFieldMultiplicity β H = 1)
    (hG : fixedFieldMultiplicity β (⊤ : Subgroup (E ≃ₐ[F] E)) = 0) : False := by
  let m : Subgroup (E ≃ₐ[F] E) → ℤ := fixedFieldMultiplicity β
  have havg (C : Subgroup (E ≃ₐ[F] E)) :
      (∑ g : C, (cyclicZeroSign m (g : E ≃ₐ[F] E) : ℝ)) =
        Fintype.card C * (m C : ℝ) := by
    apply sum_eq_fixedFieldMultiplicity_of_cyclic_averages
      (fun g : E ≃ₐ[F] E => (cyclicZeroSign m g : ℝ)) hβ0 hβ1 _ C
    intro D hD
    obtain ⟨χ, hχ, hprincipal⟩ := hcyclic D hD
    exact sum_cyclicZeroSign m D χ hχ hprincipal
  have htrivial := cyclicZeroSign_trivial_of_odd_average m
    (fun C a => fixedFieldMultiplicity_conjugate hβ0 hβ1 C a)
    (fun C hC => (hcyclic C hC).imp (fun _ h => h.1)) H hodd (by
      simpa only [m, hH, Int.cast_one, mul_one] using havg H)
  have htotal := havg (⊤ : Subgroup (E ≃ₐ[F] E))
  simp only [htrivial, Units.val_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, m, hG, Int.cast_zero, mul_zero] at htotal
  have hcard : (Fintype.card (⊤ : Subgroup (E ≃ₐ[F] E)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := (⊤ : Subgroup (E ≃ₐ[F] E)))
  exact hcard htotal

end DukePrimeDegree

end

end OAI
