import OAI.Analysis.Cotype.BConvexQuantitative
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_sign_of_radius {n : ℕ} {δ : ℝ}
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    {R : ℝ} (hR : 0 ≤ R) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ R) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ R*((n : ℝ)-δ) := by
  by_cases hz : R = 0
  · have hx0 : ∀ i, x i = 0 := fun i => norm_eq_zero.mp (by have := hx i; rw [hz] at this; exact le_antisymm this (norm_nonneg _))
    exact ⟨fun _ => false, by simp [hz,rademacherSum,hx0]⟩
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
  let y : Fin n → X := fun i => R⁻¹ • x i
  have hy i : ‖y i‖ ≤ 1 := by
    rw [show y i = R⁻¹ • x i from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hRp)]
    exact (inv_mul_le_iff₀ hRp).mpr (by simpa using hx i)
  obtain ⟨ε,hε⟩ := h y hy
  have he : R • rademacherSum X y ε = rademacherSum X x ε := by
    simp only [y,rademacherSum,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    field_simp
  refine ⟨ε,?_⟩
  calc
    _ = ‖R • rademacherSum X y ε‖ := congrArg norm he.symm
    _ = R*‖rademacherSum X y ε‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR]
    _ ≤ _ := mul_le_mul_of_nonneg_left hε hR

theorem iterated_sign_deficit {n : ℕ} {δ : ℝ} (hδn : δ ≤ (n : ℝ))
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    (k : ℕ) (x : Fin (n^k) → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ε : Cube (n^k), ‖rademacherSum X x ε‖ ≤ ((n : ℝ)-δ)^k := by
  classical
  induction k with
  | zero =>
      revert x
      change ∀ x : Fin 1 → X, (∀ i, ‖x i‖ ≤ 1) →
        ∃ ε : Cube 1, ‖rademacherSum X x ε‖ ≤ 1
      intro x hx
      refine ⟨fun _ => false,?_⟩
      simpa [rademacherSum] using hx 0
  | succ k ih =>
      revert x
      rw [pow_succ']
      intro x hx
      let e : Fin n × Fin (n^k) ≃ Fin (n*n^k) := finProdFinEquiv
      let y : Fin n → Fin (n^k) → X := fun j i => x (e (j,i))
      have hh j : ∃ ε : Cube (n^k), ‖rademacherSum X (y j) ε‖ ≤ ((n : ℝ)-δ)^k :=
        ih (y j) (fun i => hx (e (j,i)))
      choose ε hε using hh
      let z : Fin n → X := fun j => rademacherSum X (y j) (ε j)
      obtain ⟨η,hη⟩ := exists_sign_of_radius h (pow_nonneg (sub_nonneg.mpr hδn) k) z hε
      let θ : Cube (n*n^k) := fun u => xor (η (e.symm u).1) (ε (e.symm u).1 (e.symm u).2)
      have hsign (a b : Bool) : sign (xor a b) = sign a*sign b := by cases a <;> cases b <;> norm_num
      have he : rademacherSum X x θ = rademacherSum X z η := by
        simp only [rademacherSum,z,y,Finset.smul_sum,smul_smul]
        rw [← e.sum_comp]
        simp only [Fintype.sum_prod_type,θ,e.symm_apply_apply,hsign]
      refine ⟨θ,?_⟩
      rw [he,pow_succ]
      exact hη

theorem not_uniformL1_of_bConvex (hb : BConvex X) : ¬ UniformL1 X := by
  obtain ⟨n,hn,δ,hδ,h⟩ := hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hδn : δ ≤ (n : ℝ) := by
    obtain ⟨ε,hε⟩ := h (fun _ => 0) (by simp)
    simpa [rademacherSum] using hε
  intro hu
  obtain ⟨c,hc,hcX⟩ := hu
  have hq : ((n : ℝ)-δ)/(n : ℝ) < 1 := (div_lt_one hn0).mpr (by linarith)
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hc hq
  obtain ⟨x,hx⟩ := hcX (n^k)
  obtain ⟨ε,hε⟩ := iterated_sign_deficit hδn h k x hx.1
  have hl := hx.2 (fun i => sign (ε i))
  have habs i : |sign (ε i)| = 1 := by cases ε i <;> norm_num
  simp only [habs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Nat.cast_pow] at hl
  change c*(n : ℝ)^k ≤ ‖rademacherSum X x ε‖ at hl
  have hkn : ((n : ℝ)-δ)^k < c*(n : ℝ)^k := by
    rw [div_pow] at hk
    exact (div_lt_iff₀ (pow_pos hn0 k)).mp hk
  linarith

theorem bConvex_iff_not_uniformL1 : BConvex X ↔ ¬ UniformL1 X :=
  ⟨not_uniformL1_of_bConvex,bConvex_of_not_uniformL1⟩

end Cotype

end

end OAI
