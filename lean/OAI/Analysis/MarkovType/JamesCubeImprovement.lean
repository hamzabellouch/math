import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

private def CoordinateCopies (c B : ℝ) : Prop :=
  ∀ n : ℕ, ∃ T : (Fin n → ℝ) →ₗ[ℝ] X,
    (∀ i : Fin n, c ≤ ‖T (Pi.single i 1)‖) ∧
    ∀ a, ‖T a‖ ≤ B * ‖a‖

private def cubeBlock {n m : ℕ} (e : Fin n × Fin m ≃ Fin (n * m))
    (i : Fin n) : (Fin m → ℝ) →ₗ[ℝ] (Fin (n * m) → ℝ) where
  toFun a k := if (e.symm k).1 = i then a (e.symm k).2 else 0
  map_add' a b := by
    ext k
    by_cases h : (e.symm k).1 = i <;> simp [h]
  map_smul' r a := by
    ext k
    by_cases h : (e.symm k).1 = i <;> simp [h]

private lemma cubeBlock_single {n m : ℕ}
    (e : Fin n × Fin m ≃ Fin (n * m)) (i : Fin n) (j : Fin m) :
    cubeBlock e i (Pi.single j 1) = Pi.single (e (i, j)) 1 := by
  ext k
  obtain ⟨⟨r, s⟩, rfl⟩ := e.surjective k
  change (if (e.symm (e (r, s))).1 = i then
      (Pi.single j 1 : Fin m → ℝ) (e.symm (e (r, s))).2 else 0) = _
  simp only [Equiv.symm_apply_apply]
  by_cases hr : r = i <;> by_cases hs : s = j <;>
    simp [e.injective.eq_iff, Prod.mk.injEq, hr, hs]

private def cubeBlend {n m : ℕ} (e : Fin n × Fin m ≃ Fin (n * m))
    (b : Fin n → Fin m → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n * m) → ℝ) where
  toFun a k := a (e.symm k).1 * b (e.symm k).1 (e.symm k).2
  map_add' a a' := by
    ext k
    exact add_mul _ _ _
  map_smul' r a := by
    ext k
    change (r * a (e.symm k).1) * b (e.symm k).1 (e.symm k).2 =
      r * (a (e.symm k).1 * b (e.symm k).1 (e.symm k).2)
    exact mul_assoc _ _ _

private lemma cubeBlend_single {n m : ℕ}
    (e : Fin n × Fin m ≃ Fin (n * m)) (b : Fin n → Fin m → ℝ)
    (i : Fin n) : cubeBlend e b (Pi.single i 1) = cubeBlock e i (b i) := by
  ext k
  change (Pi.single i 1 : Fin n → ℝ) (e.symm k).1 * b (e.symm k).1 (e.symm k).2 =
    if (e.symm k).1 = i then b i (e.symm k).2 else 0
  by_cases h : (e.symm k).1 = i <;> simp [h]

private lemma norm_cubeBlend_le {n m : ℕ}
    (e : Fin n × Fin m ≃ Fin (n * m)) (b : Fin n → Fin m → ℝ)
    (hb : ∀ i, ‖b i‖ ≤ 1) (a : Fin n → ℝ) : ‖cubeBlend e b a‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
  intro k
  change ‖a (e.symm k).1 * b (e.symm k).1 (e.symm k).2‖ ≤ ‖a‖
  rw [norm_mul]
  calc
    ‖a (e.symm k).1‖ * ‖b (e.symm k).1 (e.symm k).2‖ ≤
        ‖a (e.symm k).1‖ * 1 :=
      mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm (b (e.symm k).1) (e.symm k).2).trans (hb _))
        (norm_nonneg _)
    _ ≤ ‖a‖ := by simpa only [mul_one] using norm_le_pi_norm a (e.symm k).1

private lemma exists_cube_gain {m : ℕ} {g c : ℝ} (hc : 0 < c)
    (hbad : ¬ ∃ T : (Fin m → ℝ) →ₗ[ℝ] X,
      (∀ i : Fin m, 1 ≤ ‖T (Pi.single i 1)‖) ∧
      ∀ a, ‖T a‖ ≤ g * ‖a‖)
    (S : (Fin m → ℝ) →ₗ[ℝ] X)
    (hS : ∀ i : Fin m, c ≤ ‖S (Pi.single i 1)‖) :
    ∃ b : Fin m → ℝ, ‖b‖ ≤ 1 ∧ g * c ≤ ‖S b‖ := by
  have hfail : ¬ ∀ a, ‖S a‖ ≤ (g * c) * ‖a‖ := by
    intro hbound
    apply hbad
    let T : (Fin m → ℝ) →ₗ[ℝ] X := c⁻¹ • S
    have hT (a : Fin m → ℝ) : ‖T a‖ = ‖S a‖ / c := by
      change ‖c⁻¹ • S a‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), div_eq_mul_inv]
      exact mul_comm _ _
    refine ⟨T, ?_, ?_⟩
    · intro i
      rw [hT]
      exact (le_div_iff₀ hc).2 (by simpa only [one_mul] using hS i)
    · intro a
      rw [hT]
      apply (div_le_iff₀ hc).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound a
  obtain ⟨a, ha⟩ := not_forall.mp hfail
  have ha : (g * c) * ‖a‖ < ‖S a‖ := lt_of_not_ge ha
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  have haPos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b : Fin m → ℝ := ‖a‖⁻¹ • a
  have hb : ‖b‖ = 1 := by
    simp only [b, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr haPos),
      inv_mul_cancel₀ haPos.ne']
  have hSb : ‖S b‖ = ‖S a‖ / ‖a‖ := by
    dsimp only [b]
    rw [map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr haPos), div_eq_mul_inv]
    exact mul_comm _ _
  refine ⟨b, hb.le, ?_⟩
  rw [hSb]
  exact ((lt_div_iff₀ haPos).2 ha).le

private lemma coordinateCopies_amplify {m : ℕ} {g c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B)
    (hbad : ¬ ∃ T : (Fin m → ℝ) →ₗ[ℝ] X,
      (∀ i : Fin m, 1 ≤ ‖T (Pi.single i 1)‖) ∧
      ∀ a, ‖T a‖ ≤ g * ‖a‖)
    (hcopies : CoordinateCopies (X := X) c B) :
    CoordinateCopies (X := X) (g * c) B := by
  classical
  intro n
  obtain ⟨T, hcoord, hbound⟩ := hcopies (n * m)
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  have hrow (i : Fin n) :
      ∃ b : Fin m → ℝ, ‖b‖ ≤ 1 ∧ g * c ≤ ‖(T.comp (cubeBlock e i)) b‖ := by
    apply exists_cube_gain hc hbad
    intro j
    simpa only [LinearMap.comp_apply, cubeBlock_single] using hcoord (e (i, j))
  let b : Fin n → Fin m → ℝ := fun i => Classical.choose (hrow i)
  have hb (i : Fin n) : ‖b i‖ ≤ 1 := (Classical.choose_spec (hrow i)).1
  have hgain (i : Fin n) : g * c ≤ ‖(T.comp (cubeBlock e i)) (b i)‖ :=
    (Classical.choose_spec (hrow i)).2
  refine ⟨T.comp (cubeBlend e b), ?_, ?_⟩
  · intro i
    simpa only [LinearMap.comp_apply, cubeBlend_single] using hgain i
  · intro a
    exact (hbound (cubeBlend e b a)).trans
      (mul_le_mul_of_nonneg_left (norm_cubeBlend_le e b hb a) hB)

private lemma exists_coordinate_improvement {B g : ℝ} (hB : 0 ≤ B) (hg : 1 < g)
    (hcopies : CoordinateCopies (X := X) 1 B) (m : ℕ) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X,
      (∀ i : Fin m, 1 ≤ ‖T (Pi.single i 1)‖) ∧
      ∀ a, ‖T a‖ ≤ g * ‖a‖ := by
  classical
  by_contra hbad
  have hg0 : 0 < g := lt_trans zero_lt_one hg
  have hpowers : ∀ r : ℕ, CoordinateCopies (X := X) (g ^ r) B := by
    intro r
    induction r with
    | zero => simpa only [pow_zero] using hcopies
    | succ r hr =>
      have hnext := coordinateCopies_amplify (pow_pos hg0 r) hB hbad hr
      simpa only [pow_succ, mul_comm] using hnext
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt B hg
  obtain ⟨T, hcoord, hbound⟩ := hpowers r 1
  have hlo := hcoord (0 : Fin 1)
  have hhi : ‖T (Pi.single (0 : Fin 1) 1)‖ ≤ B := by
    simpa only [Pi.norm_single, norm_one, mul_one] using hbound (Pi.single (0 : Fin 1) 1)
  exact (not_le_of_gt hr) (hlo.trans hhi)

private lemma cube_lower_of_coordinate_bounds {n : ℕ} {g : ℝ} (hg : 0 ≤ g)
    (T : (Fin n → ℝ) →ₗ[ℝ] X)
    (hcoord : ∀ i : Fin n, 1 ≤ ‖T (Pi.single i 1)‖)
    (hbound : ∀ a, ‖T a‖ ≤ g * ‖a‖) (a : Fin n → ℝ) :
    (2 - g) * ‖a‖ ≤ ‖T a‖ := by
  have hpoint (i : Fin n) : 2 * |a i| ≤ ‖T a‖ + g * ‖a‖ := by
    let b : Fin n → ℝ := (2 * a i) • (Pi.single i 1 : Fin n → ℝ) - a
    have hb : ‖b‖ ≤ ‖a‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
      intro j
      change ‖(2 * a i) * (Pi.single i 1 : Fin n → ℝ) j - a j‖ ≤ ‖a‖
      by_cases hji : j = i
      · subst j
        rw [Pi.single_eq_same, mul_one, show 2 * a i - a i = a i by ring]
        exact norm_le_pi_norm a i
      · rw [Pi.single_eq_of_ne hji, mul_zero, zero_sub, norm_neg]
        exact norm_le_pi_norm a j
    have heq : T a + T b = (2 * a i) • T (Pi.single i 1) := by
      dsimp only [b]
      rw [map_sub, map_smul]
      abel
    have hnorm : 2 * |a i| ≤ ‖(2 * a i) • T (Pi.single i 1)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hcoord i)
          (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a i)))
    calc
      2 * |a i| ≤ ‖T a + T b‖ := by simpa only [heq] using hnorm
      _ ≤ ‖T a‖ + ‖T b‖ := norm_add_le _ _
      _ ≤ ‖T a‖ + g * ‖a‖ :=
        add_le_add le_rfl ((hbound b).trans (mul_le_mul_of_nonneg_left hb hg))
  have hnonneg : 0 ≤ (‖T a‖ + g * ‖a‖) / 2 :=
    div_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hg (norm_nonneg _))) (by norm_num)
  have hnorm : ‖a‖ ≤ (‖T a‖ + g * ‖a‖) / 2 := by
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro i
    rw [Real.norm_eq_abs]
    linarith [hpoint i]
  nlinarith

theorem james_cube_improvement
    (L : ℝ) (hL : 1 ≤ L)
    (hcopies : ∀ n : ℕ, ∃ T : (Fin n → ℝ) →ₗ[ℝ] X,
      ∀ a, ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ L * ‖a‖)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ T : (Fin n → ℝ) →ₗ[ℝ] X,
      ∀ a, ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * ‖a‖ := by
  have hbase : CoordinateCopies (X := X) 1 L := by
    intro m
    obtain ⟨T, hT⟩ := hcopies m
    refine ⟨T, ?_, fun a => (hT a).2⟩
    intro i
    simpa only [Pi.norm_single, norm_one] using (hT (Pi.single i 1)).1
  let δ : ℝ := min (η / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδη : δ ≤ η / 4 := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδ1 : δ < 1 := lt_of_le_of_lt hδhalf (by linarith)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  obtain ⟨T, hcoord, hbound⟩ :=
    exists_coordinate_improvement (le_trans zero_le_one hL) (by linarith : 1 < 1 + δ) hbase n
  have hlo (a : Fin n → ℝ) : (1 - δ) * ‖a‖ ≤ ‖T a‖ := by
    have h := cube_lower_of_coordinate_bounds (by linarith : 0 ≤ 1 + δ) T hcoord hbound a
    nlinarith
  let S : (Fin n → ℝ) →ₗ[ℝ] X := (1 - δ)⁻¹ • T
  have hS (a : Fin n → ℝ) : ‖S a‖ = ‖T a‖ / (1 - δ) := by
    change ‖(1 - δ)⁻¹ • T a‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
    exact mul_comm _ _
  have hratio : (1 + δ) / (1 - δ) ≤ 1 + η := by
    apply (div_le_iff₀ hden).2
    have hprod := mul_le_mul_of_nonneg_left hδhalf hη.le
    nlinarith
  refine ⟨S, fun a => ?_⟩
  rw [hS]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [hlo a]
  · calc
      ‖T a‖ / (1 - δ) ≤ ((1 + δ) * ‖a‖) / (1 - δ) :=
        (div_le_div_iff_of_pos_right hden).2 (hbound a)
      _ = ((1 + δ) / (1 - δ)) * ‖a‖ := by ring
      _ ≤ (1 + η) * ‖a‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg a)

end MarkovSuperreflexivity

end

end OAI
