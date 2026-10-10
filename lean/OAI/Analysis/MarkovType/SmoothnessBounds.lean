import OAI.Analysis.MarkovType.RenormingBasic
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Set

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

def SymmetricPowerSmooth (p : Seminorm ℝ X) (q A : ℝ) : Prop :=
  ∀ x y : X, (p (x + y) ^ q + p (x - y) ^ q) / 2 ≤
    p x ^ q + A * p y ^ q

def PowerSmooth (p : Seminorm ℝ X) (q C : ℝ) : Prop :=
  ∀ x y : X, p x = 1 → p y = 1 → ∀ t : ℝ, 0 ≤ t →
    (p (x + t • y) + p (x - t • y)) / 2 ≤ 1 + C * t ^ q

def smoothnessDeviations (p : Seminorm ℝ X) (t : ℝ) : Set ℝ :=
  {d | ∃ x y : X, p x = 1 ∧ p y = 1 ∧
    d = (p (x + t • y) + p (x - t • y)) / 2 - 1}

def smoothnessModulus (p : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sSup (insert 0 (smoothnessDeviations p t))

theorem mean_le_root_le_one_add {a b q z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 1 ≤ q) (hz : 0 ≤ z)
    (hpow : (a ^ q + b ^ q) / 2 ≤ 1 + z) :
    (a + b) / 2 ≤ (1 + z) ^ (1 / q) ∧
      (1 + z) ^ (1 / q) ≤ 1 + z := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmean : 0 ≤ (a + b) / 2 :=
    div_nonneg (add_nonneg ha hb) (by norm_num)
  have hbase : 0 ≤ 1 + z := add_nonneg zero_le_one hz
  have hhalf (v w : ℝ) :
      (1 / 2 : ℝ) * v + (1 / 2 : ℝ) * w = (v + w) / 2 := by ring
  have hJ : ((a + b) / 2) ^ q ≤ (a ^ q + b ^ q) / 2 := by
    have hconv := (convexOn_rpow hq).2
    have hj := hconv ha hb
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simpa only [smul_eq_mul, hhalf] using hj
  constructor
  · simpa only [one_div] using
      (Real.le_rpow_inv_iff_of_pos hmean hbase hqpos).2 (hJ.trans hpow)
  · simpa only [one_div] using
      Real.rpow_le_self_of_one_le (show 1 ≤ 1 + z by linarith)
        (inv_le_one_of_one_le₀ hq)

theorem SymmetricPowerSmooth.powerSmooth {p : Seminorm ℝ X} {q A : ℝ}
    (h : SymmetricPowerSmooth p q A) (hq : 1 ≤ q) (hA : 0 ≤ A) :
    PowerSmooth p q A := by
  intro x y hx hy t ht
  have hty : p (t • y) = t := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht, hy, mul_one]
  have hpow := h x (t • y)
  rw [hx, Real.one_rpow, hty] at hpow
  have hroot := mean_le_root_le_one_add
    (apply_nonneg p (x + t • y)) (apply_nonneg p (x - t • y))
    hq (mul_nonneg hA (Real.rpow_nonneg ht q)) hpow
  exact hroot.1.trans hroot.2

theorem seminorm_le_symmetric_average (p : Seminorm ℝ X) (x z : X) :
    p x ≤ (p (x + z) + p (x - z)) / 2 := by
  have hid : (x + z) + (x - z) = (2 : ℝ) • x := by
    rw [two_smul ℝ]
    abel
  have h := map_add_le_add p (x + z) (x - z)
  rw [hid, map_smul_eq_mul] at h
  norm_num at h
  linarith

theorem smoothnessDeviation_nonneg (p : Seminorm ℝ X) (t : ℝ)
    {x y : X} (hx : p x = 1) :
    0 ≤ (p (x + t • y) + p (x - t • y)) / 2 - 1 := by
  have h := seminorm_le_symmetric_average p x (t • y)
  rw [hx] at h
  linarith

theorem smoothnessDeviation_le_abs (p : Seminorm ℝ X) (t : ℝ)
    {x y : X} (hx : p x = 1) (hy : p y = 1) :
    (p (x + t • y) + p (x - t • y)) / 2 - 1 ≤ |t| := by
  have hty : p (t • y) = |t| := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, hy, mul_one]
  have hp := map_add_le_add p x (t • y)
  have hm := map_sub_le_add p x (t • y)
  rw [hx, hty] at hp hm
  linarith

theorem smoothnessDeviations_bddAbove (p : Seminorm ℝ X) (t : ℝ) :
    BddAbove (smoothnessDeviations p t) := by
  refine ⟨|t|, ?_⟩
  rintro d ⟨x, y, hx, hy, rfl⟩
  exact smoothnessDeviation_le_abs p t hx hy

theorem smoothnessDeviations_insert_bddAbove (p : Seminorm ℝ X) (t : ℝ) :
    BddAbove (insert 0 (smoothnessDeviations p t)) := by
  refine ⟨|t|, ?_⟩
  intro d hd
  rcases Set.mem_insert_iff.mp hd with rfl | hd
  · exact abs_nonneg t
  · obtain ⟨x, y, hx, hy, rfl⟩ := hd
    exact smoothnessDeviation_le_abs p t hx hy

theorem smoothnessModulus_nonneg (p : Seminorm ℝ X) (t : ℝ) :
    0 ≤ smoothnessModulus p t :=
  le_csSup (smoothnessDeviations_insert_bddAbove p t)
    (Set.mem_insert 0 (smoothnessDeviations p t))

theorem smoothnessModulus_le (p : Seminorm ℝ X) (t : ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (hpair : ∀ x y : X, p x = 1 → p y = 1 →
      (p (x + t • y) + p (x - t • y)) / 2 - 1 ≤ B) :
    smoothnessModulus p t ≤ B := by
  apply csSup_le (Set.insert_nonempty 0 (smoothnessDeviations p t))
  intro d hd
  rcases Set.mem_insert_iff.mp hd with rfl | hd
  · exact hB
  · obtain ⟨x, y, hx, hy, rfl⟩ := hd
    exact hpair x y hx hy

theorem smoothnessModulus_le_abs (p : Seminorm ℝ X) (t : ℝ) :
    smoothnessModulus p t ≤ |t| :=
  smoothnessModulus_le p t (abs_nonneg t)
    (fun _ _ hx hy => smoothnessDeviation_le_abs p t hx hy)

@[simp] theorem smoothnessModulus_zero (p : Seminorm ℝ X) :
    smoothnessModulus p 0 = 0 := by
  apply le_antisymm
  · simpa only [abs_zero] using smoothnessModulus_le_abs p 0
  · exact smoothnessModulus_nonneg p 0

theorem smoothnessDeviation_le_modulus (p : Seminorm ℝ X) (t : ℝ)
    {x y : X} (hx : p x = 1) (hy : p y = 1) :
    (p (x + t • y) + p (x - t • y)) / 2 - 1 ≤ smoothnessModulus p t := by
  apply le_csSup (smoothnessDeviations_insert_bddAbove p t)
  exact Set.mem_insert_of_mem 0 ⟨x, y, hx, hy, rfl⟩

theorem PowerSmooth.smoothnessModulus_le {p : Seminorm ℝ X} {q C : ℝ}
    (h : PowerSmooth p q C) (hC : 0 ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    smoothnessModulus p t ≤ C * t ^ q := by
  apply MarkovSuperreflexivity.smoothnessModulus_le p t (mul_nonneg hC (Real.rpow_nonneg ht q))
  intro x y hx hy
  have hxy := h x y hx hy t ht
  linarith

theorem powerSmooth_iff_smoothnessModulus_le {p : Seminorm ℝ X} {q C : ℝ}
    (hC : 0 ≤ C) :
    PowerSmooth p q C ↔ ∀ t : ℝ, 0 ≤ t → smoothnessModulus p t ≤ C * t ^ q := by
  constructor
  · intro h t ht
    exact h.smoothnessModulus_le hC ht
  · intro h x y hx hy t ht
    have hxy := (smoothnessDeviation_le_modulus p t hx hy).trans (h t ht)
    linarith

theorem SymmetricPowerSmooth.smoothnessModulus_le
    {p : Seminorm ℝ X} {q A : ℝ} (h : SymmetricPowerSmooth p q A)
    (hq : 1 ≤ q) (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) :
    smoothnessModulus p t ≤ A * t ^ q :=
  (h.powerSmooth hq hA).smoothnessModulus_le hA ht

theorem smoothnessModulus_eq_standard_of_exists_unit (p : Seminorm ℝ X)
    (hunit : ∃ x : X, p x = 1) (t : ℝ) :
    smoothnessModulus p t =
      sSup {d : ℝ | ∃ x y : X, p x = 1 ∧ p y = 1 ∧
        d = (p (x + t • y) + p (x - t • y)) / 2 - 1} := by
  obtain ⟨x, hx⟩ := hunit
  let d := (p (x + t • x) + p (x - t • x)) / 2 - 1
  have hd : d ∈ smoothnessDeviations p t := ⟨x, x, hx, hx, rfl⟩
  have hs : 0 ≤ sSup (smoothnessDeviations p t) :=
    le_csSup_of_le (smoothnessDeviations_bddAbove p t) hd
      (smoothnessDeviation_nonneg p t hx)
  change sSup (insert 0 (smoothnessDeviations p t)) =
    sSup (smoothnessDeviations p t)
  rw [csSup_insert (smoothnessDeviations_bddAbove p t) ⟨d, hd⟩]
  exact sup_eq_right.mpr hs

theorem exists_seminorm_unit_of_pos (p : Seminorm ℝ X) {x : X}
    (hx : 0 < p x) : ∃ y : X, p y = 1 := by
  refine ⟨(p x)⁻¹ • x, ?_⟩
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
    inv_mul_cancel₀ hx.ne']

theorem exists_seminorm_unit_of_definite [Nontrivial X] (p : Seminorm ℝ X)
    (hp : ∀ x : X, p x = 0 → x = 0) : ∃ x : X, p x = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hpos : 0 < p x := by
    by_contra h
    apply hx
    exact hp x (le_antisymm (le_of_not_gt h) (apply_nonneg p x))
  exact exists_seminorm_unit_of_pos p hpos

theorem smoothnessModulus_eq_standard_of_definite [Nontrivial X]
    (p : Seminorm ℝ X) (hp : ∀ x : X, p x = 0 → x = 0) (t : ℝ) :
    smoothnessModulus p t =
      sSup {d : ℝ | ∃ x y : X, p x = 1 ∧ p y = 1 ∧
        d = (p (x + t • y) + p (x - t • y)) / 2 - 1} :=
  smoothnessModulus_eq_standard_of_exists_unit p
    (exists_seminorm_unit_of_definite p hp) t

theorem smoothnessModulus_eq_zero_of_no_unit (p : Seminorm ℝ X)
    (hunit : ¬∃ x : X, p x = 1) (t : ℝ) : smoothnessModulus p t = 0 := by
  apply le_antisymm ?_ (smoothnessModulus_nonneg p t)
  apply smoothnessModulus_le p t le_rfl
  intro x y hx hy
  exact (hunit ⟨x, hx⟩).elim

@[simp] theorem smoothnessModulus_eq_zero_of_subsingleton [Subsingleton X]
    (p : Seminorm ℝ X) (t : ℝ) : smoothnessModulus p t = 0 := by
  apply smoothnessModulus_eq_zero_of_no_unit p ?_ t
  rintro ⟨x, hx⟩
  have hxzero : x = 0 := Subsingleton.elim _ _
  rw [hxzero, map_zero] at hx
  exact zero_ne_one hx

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem PowerSmooth.uniformSmooth {p : Seminorm ℝ Y} {q C : ℝ}
    (h : PowerSmooth p q C) (hq : 1 < q) (hC : 0 ≤ C) : UniformSmooth p := by
  intro ε hε
  have hCpos : 0 < C + 1 := by linarith
  have hrpos : 0 < q - 1 := sub_pos.mpr hq
  have hbase : 0 < ε / (C + 1) := div_pos hε hCpos
  let δ : ℝ := (ε / (C + 1)) ^ (q - 1)⁻¹
  have hδ : 0 < δ := Real.rpow_pos_of_pos hbase _
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd x y hx hy
  have hpower : t ^ (q - 1) < ε / (C + 1) := by
    have htq := Real.rpow_lt_rpow ht.le htd hrpos
    simpa only [δ, Real.rpow_inv_rpow hbase.le hrpos.ne'] using htq
  have hscaled : t ^ (q - 1) * (C + 1) < ε :=
    (lt_div_iff₀ hCpos).mp hpower
  have hpnonneg := Real.rpow_nonneg ht.le (q - 1)
  have hfactor : C * t ^ (q - 1) ≤ ε := by nlinarith
  have hsplit : t ^ q = t ^ (q - 1) * t := by
    calc
      t ^ q = t ^ ((q - 1) + 1) := by congr 1 ; ring
      _ = t ^ (q - 1) * t ^ (1 : ℝ) := Real.rpow_add ht _ _
      _ = t ^ (q - 1) * t := by rw [Real.rpow_one]
  have hbound : C * t ^ q ≤ ε * t := by
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfactor ht.le
  exact (h x y hx hy t ht.le).trans (add_le_add (le_refl (1 : ℝ)) hbound)

theorem SymmetricPowerSmooth.uniformSmooth {p : Seminorm ℝ Y} {q A : ℝ}
    (h : SymmetricPowerSmooth p q A) (hq : 1 < q) (hA : 0 ≤ A) : UniformSmooth p :=
  (h.powerSmooth hq.le hA).uniformSmooth hq hA

theorem EquivalentNorm.smoothnessModulus_eq_standard [Nontrivial Y]
    (N : EquivalentNorm Y) (t : ℝ) :
    smoothnessModulus N.p t =
      sSup {d : ℝ | ∃ x y : Y, N.p x = 1 ∧ N.p y = 1 ∧
        d = (N.p (x + t • y) + N.p (x - t • y)) / 2 - 1} :=
  smoothnessModulus_eq_standard_of_definite N.p
    (fun x hx => (N.eq_zero_iff x).mp hx) t

end MarkovSuperreflexivity

end

end OAI
