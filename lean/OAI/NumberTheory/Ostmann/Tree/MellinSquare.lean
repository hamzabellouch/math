import OAI.NumberTheory.Ostmann.Tree.AffineEnergy
import OAI.NumberTheory.Ostmann.Tree.Mellin
import OAI.NumberTheory.Ostmann.Tree.UnitSums

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : Fintype (MulChar F ℂ) := Fintype.ofFinite _

theorem sum_units_mulChar (χ : MulChar F ℂ) :
    ∑ u : Fˣ, χ u = if χ=1 then (Fintype.card Fˣ:ℂ) else 0 := by
  classical
  by_cases hχ : χ=1
  · simp [hχ]
  · rw [sum_units_of_zero χ χ.map_zero]
    simpa only [hχ, ite_false] using MulChar.sum_eq_zero_of_ne_one hχ

theorem sum_units_character_kernel (χ ρ : MulChar F ℂ) :
    ∑ u : Fˣ, χ u*conj (ρ u) = if χ=ρ then (Fintype.card Fˣ:ℂ) else 0 := by
  classical
  have hs (u : Fˣ) : χ u*conj (ρ u)=(χ*ρ⁻¹) u := by
    rw [MulChar.mul_apply]
    congr 1
    exact MulChar.star_apply' ρ u
  simp_rw [hs]
  rw [sum_units_mulChar]
  simp only [mul_inv_eq_one]

theorem character_square_fiber_card (S : Finset (MulChar F ℂ)) (ρ : MulChar F ℂ)
    (hS : ∀ χ ∈ S, χ^2=ρ) : S.card ≤ 2 := by
  classical
  let e : MulChar F ℂ ≃* Fˣ := (MulChar.mulEquiv_units F ℂ).some
  by_cases he : S.Nonempty
  · obtain ⟨χ0,hχ0⟩ := he
    have hi : Set.InjOn e (↑S : Set (MulChar F ℂ)) := e.injective.injOn
    rw [← Finset.card_image_of_injOn hi]
    calc
      (S.image e).card ≤ ({e χ0,-e χ0} : Finset Fˣ).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨χ,hχ,rfl⟩ := Finset.mem_image.mp hz
        have hp : (e χ)^2=(e χ0)^2 := by
          rw [← map_pow, ← map_pow, hS χ hχ, hS χ0 hχ0]
        rcases Units.sq_eq_sq_iff_eq_or_eq_neg.mp hp with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

theorem mulChar_norm_unit (χ : MulChar F ℂ) (u : Fˣ) : ‖χ u‖=1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (MulChar.apply_mem_rootsOfUnity (χ := χ) u)

theorem mellin_square_expansion (c : MulChar F ℂ → ℂ) (K : Fˣ) (ρ : MulChar F ℂ) :
    mellin (fun z : Fˣ => ∑ χ : MulChar F ℂ, c χ*χ (K*z^2)) ρ =
      ∑ χ : MulChar F ℂ with χ^2=ρ, c χ*χ K := by
  classical
  unfold mellin
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro χ _
  have hval (z : Fˣ) : c χ*χ (K*z^2)*conj (ρ z) =
      (c χ*χ K)*((χ^2) z*conj (ρ z)) := by
    rw [map_mul, map_pow, MulChar.pow_apply_coe]
    ring
  simp_rw [hval]
  rw [← Finset.mul_sum, sum_units_character_kernel]
  have hN : (Fintype.card Fˣ:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  split_ifs <;> simp_all
  field_simp

theorem mellin_square_pullback (f : Fˣ → ℂ) (K : Fˣ) (ρ : MulChar F ℂ) :
    ‖mellin (fun z : Fˣ => f (K*z^2)) ρ‖^2 ≤
      2*∑ χ : MulChar F ℂ with χ^2=ρ, ‖mellin f χ‖^2 := by
  classical
  have he : (fun z : Fˣ => f (K*z^2)) =
      (fun z : Fˣ => ∑ χ : MulChar F ℂ, mellin f χ*χ (K*z^2)) := by
    funext z
    exact (mellin_inversion f (K*z^2)).symm
  rw [he, mellin_square_expansion]
  let S : Finset (MulChar F ℂ) := Finset.univ.filter (fun χ => χ^2=ρ)
  have hc : S.card ≤ 2 := character_square_fiber_card S ρ
    (fun χ hχ => (Finset.mem_filter.mp hχ).2)
  have hs := norm_sum_sq_le_card S (fun χ => mellin f χ*χ K)
  simp only [norm_mul, mulChar_norm_unit, mul_one] at hs
  have hcR : (S.card:ℝ)≤2 := by exact_mod_cast hc
  exact hs.trans (mul_le_mul_of_nonneg_right hcR (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end
end Ostmann.FiniteField

end OAI
