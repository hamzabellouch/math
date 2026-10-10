import OAI.NumberTheory.Ostmann.Characters.PrimitiveGaussFourier
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMatrixDuality
import OAI.NumberTheory.Ostmann.Arithmetic.ReducedFrequencyEnergy

namespace OAI

/-! # The additive-sieve majorant for one primitive character -/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem sum_units_eq_sum_ite {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, f u) = ∑ x : ZMod q, if IsUnit x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, f x := by
      apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q))
      · intro u _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact u.isUnit
      · intro u _ v _ huv
        exact Units.val_injective huv
      · intro x hx
        obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hx).2
        exact ⟨u, Finset.mem_univ _, hu⟩
      · intro _ _
        rfl
    _ = _ := by rw [Finset.sum_filter]

 theorem primitive_unit_gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (a : ZMod q) :
    (∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((u : ZMod q) * a)) =
      χ⁻¹ a * gaussSum χ ZMod.stdAddChar := by
  rw [sum_units_eq_sum_ite (fun x : ZMod q => χ x * ZMod.stdAddChar (x * a))]
  have he : (∑ x : ZMod q, if IsUnit x then χ x * ZMod.stdAddChar (x * a) else 0) =
      ∑ x : ZMod q, χ x * ZMod.stdAddChar (x * a) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : IsUnit x
    · rw [ite_eq_left hx]
    · rw [ite_eq_right hx, χ.map_nonunit hx, zero_mul]
  rw [he]
  have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ a
  simpa only [gaussSum, AddChar.mulShift_apply, mul_comm a] using hg

 theorem primitive_character_sieve {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (c : ι → ℂ) (a : ι → ZMod q) :
    ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  let U : (ZMod q)ˣ → ℂ := fun u => star (χ u)
  let V : (ZMod q)ˣ → ℂ := fun u => ∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)
  have hid : star U ⬝ᵥ V = (∑ j, c j * χ⁻¹ (a j)) * gaussSum χ ZMod.stdAddChar := by
    change (∑ u : (ZMod q)ˣ, star (star (χ u)) * ∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)) = _
    simp only [star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, c j * ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((u : ZMod q) * a j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by simp_rw [primitive_unit_gauss χ hχ]; rw [Finset.sum_mul]; congr 1; funext j; ring
  have hU : (∑ u, ‖U u‖ ^ 2) ≤ (q : ℝ) := by
    have hcard : Fintype.card (ZMod q)ˣ ≤ Fintype.card (ZMod q) :=
      Fintype.card_le_of_injective (fun u : (ZMod q)ˣ => (u : ZMod q)) Units.val_injective
    simp only [U, norm_star, χ.unit_norm_eq_one, one_pow, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast (hcard.trans_eq (ZMod.card q))
  have hh := finite_complex_cauchy_schwarz U V
  rw [hid, norm_mul, mul_pow, primitive_gauss_norm_sq χ hχ] at hh
  have hE : 0 ≤ ∑ u, ‖V u‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := hh.trans (mul_le_mul_of_nonneg_right hU hE)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_iff_right₀ hq).mp (by simpa only [mul_comm] using hm)

end Ostmann

end OAI
