import Mathlib.Tactic.FieldSimp
import OAI.Analysis.MutuallyUnbiased.Matrix.Definitions

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

theorem character_mul (x y : Coord → ℂ) (a : Charge) :
    character (x * y) a = character x a * character y a := by
  simp only [character, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem character_constant (z : ℂ) (hz : z ≠ 0) (a : Charge) (ha : Balanced a) :
    character (fun _ => z) a = 1 := by
  have hp (s : Finset Coord) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]
  rw [character, hp, ha, zpow_zero]

theorem g_row_phase (H : CMatrix) (u : Coord → ℂ) (a : Charge) :
    g (fun i j => u i * H i j) a = character u a * g H a := by
  simp only [g]
  simp_rw [show ∀ k, character (fun i => u i * H i k) a =
    character u a * character (fun i => H i k) a from
      fun k => character_mul u (fun i => H i k) a]
  rw [← Finset.mul_sum]
  ring

theorem g_column_phase (H : CMatrix) (v : Coord → ℂ) (hv : ∀ j, v j ≠ 0)
    (a : Charge) (ha : Balanced a) :
    g (fun i j => H i j * v j) a = g H a := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (character_mul (fun i => H i k) (fun _ => v k) a).trans
    (by rw [character_constant (v k) (hv k) a ha, mul_one])

theorem g_column_permutation (H : CMatrix) (π : Equiv.Perm Coord) (a : Charge) :
    g (fun i j => H i (π j)) a = g H a := by
  exact congrArg ((6 : ℂ)⁻¹ * ·) (Equiv.sum_comp π (fun k => character (fun i => H i k) a))

theorem character_permutation (x : Coord → ℂ) (π : Equiv.Perm Coord) (a : Charge) :
    character (x ∘ π) a = character x (permuteCharge π.symm a) := by
  unfold character permuteCharge
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun i => x i ^ a (π.symm i))

theorem g_row_permutation (H : CMatrix) (π : Equiv.Perm Coord) (a : Charge) :
    g (fun i j => H (π i) j) a = g H (permuteCharge π.symm a) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact character_permutation (fun i => H i k) π a

theorem equivalent_symm {H K : CMatrix} (h : Equivalent H K) : Equivalent K H := by
  rcases h with ⟨r, c, u, v, hu, hv, h⟩
  refine ⟨r.symm, c.symm, (fun i => (u (r.symm i))⁻¹),
    (fun j => (v (c.symm j))⁻¹), ?_, ?_, ?_⟩
  · intro i
    simp [hu]
  · intro j
    simp [hv]
  · intro i j
    rw [h]
    simp only [Equiv.apply_symm_apply]
    field_simp [unit_ne_zero (hu (r.symm i)), unit_ne_zero (hv (c.symm j))]

theorem equivalent_trans {H K L : CMatrix} (h₁ : Equivalent H K)
    (h₂ : Equivalent K L) : Equivalent H L := by
  rcases h₁ with ⟨r, c, u, v, hu, hv, h₁⟩
  rcases h₂ with ⟨r', c', u', v', hu', hv', h₂⟩
  refine ⟨r'.trans r, c'.trans c, (fun i => u' i * u (r' i)),
    (fun j => v (c' j) * v' j), ?_, ?_, ?_⟩
  · intro i
    simp [map_mul, hu, hu']
  · intro j
    simp [map_mul, hv, hv']
  · intro i j
    rw [h₂, h₁]
    simp [mul_assoc]

end MUB6

end

end OAI
