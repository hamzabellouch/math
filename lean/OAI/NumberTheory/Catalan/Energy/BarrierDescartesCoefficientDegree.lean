import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierDescartesTransform {R : Type*} [CommRing R] (p : R[X])
    (d : ℕ) (a b : R) : R[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (p.coeff k) * (C a + C b * X) ^ k * (1 + X) ^ (d - k)

theorem barrierDescartesTransform_eval {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t =
      (1 + t) ^ d * p.eval ((a + b * t) / (1 + t)) := by
  unfold barrierDescartesTransform
  rw [eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : (1 + t) ^ (d - k) = (1 + t) ^ d / (1 + t) ^ k := by
    apply (eq_div_iff (pow_ne_zero k ht)).2
    rw [← pow_add, Nat.sub_add_cancel hkd]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rw [hp, div_pow]
  ring

theorem barrierDescartesTransform_eval_eq_zero_iff {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t = 0 ↔
      p.eval ((a + b * t) / (1 + t)) = 0 := by
  rw [barrierDescartesTransform_eval p d a b t hd ht]
  simp [pow_ne_zero d ht]

theorem barrierMobius_inverse {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    0 < (x - a) / (b - x) ∧
      (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) = x := by
  have hp : 0 < (x - a) / (b - x) :=
    div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hb : b - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have h1 : 1 + (x - a) / (b - x) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨hp, ?_⟩
  apply (div_eq_iff h1).2
  field_simp [hb]
  ring

theorem barrierDescartesTransform_root_of_interval (p : ℝ[X]) (d : ℕ)
    {a b x : ℝ} (hd : p.natDegree ≤ d) (hx : x ∈ Set.Ioo a b)
    (hp : p.eval x = 0) :
    0 < (x - a) / (b - x) ∧
      (barrierDescartesTransform p d a b).eval ((x - a) / (b - x)) = 0 := by
  obtain ⟨ht, heq⟩ := barrierMobius_inverse hx
  refine ⟨ht, ?_⟩
  apply (barrierDescartesTransform_eval_eq_zero_iff p d a b _ hd
    (ne_of_gt (by linarith))).2
  rw [heq]
  exact hp

theorem barrier_coeff_affine_pow {R : Type*} [CommRing R]
    (a b : R) (j k : ℕ) :
    ((C a + C b * X) ^ j).coeff k =
      (j.choose k : R) * a ^ (j - k) * b ^ k := by
  calc
    ((C a + C b * X) ^ j).coeff k =
        (((X + C a) ^ j).comp (C b * X)).coeff k := by
      rw [pow_comp, add_comp, X_comp, C_comp,
        add_comm (C b * X) (C a)]
    _ = ((X + C a) ^ j).coeff k * b ^ k := comp_C_mul_X_coeff
    _ = _ := by
      rw [coeff_X_add_C_pow]
      ac_rfl

theorem barrierDescartesTransform_coeff {R : Type*} [CommRing R]
    (p : R[X]) (d : ℕ) (a b : R) (h : ℕ) :
    (barrierDescartesTransform p d a b).coeff h =
      ∑ j ∈ Finset.range (d + 1), p.coeff j *
        ∑ k ∈ Finset.range (h + 1),
          (j.choose k : R) * a ^ (j - k) * b ^ k *
            ((d - j).choose (h - k) : R) := by
  unfold barrierDescartesTransform
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, coeff_C_mul, coeff_mul]
  have hanti :
      (∑ x ∈ Finset.antidiagonal h,
        Polynomial.coeff ((C a + C b * X : R[X]) ^ j) x.1 *
          Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) x.2) =
      ∑ k ∈ Finset.range (h + 1),
        Polynomial.coeff ((C a + C b * X : R[X]) ^ j) k *
          Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) (h - k) :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun (k l : ℕ) => Polynomial.coeff ((C a + C b * X : R[X]) ^ j) k *
        Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) l) h
  rw [hanti]
  simp only [barrier_coeff_affine_pow, coeff_one_add_X_pow]

def barrierDescartesCoeffRat (c : ℕ → ℚ) (d : ℕ) (a b : ℚ) (h : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (d + 1), c j *
    ∑ k ∈ Finset.range (h + 1),
      (j.choose k : ℚ) * a ^ (j - k) * b ^ k *
        ((d - j).choose (h - k) : ℚ)

theorem barrierDescartesTransform_coeff_rat (p : ℚ[X]) (c : ℕ → ℚ)
    (d : ℕ) (a b : ℚ) (h : ℕ)
    (hc : ∀ j, j < d + 1 → p.coeff j = c j) :
    (barrierDescartesTransform (p.map (Rat.castHom ℝ)) d (a : ℝ) (b : ℝ)).coeff h =
      (barrierDescartesCoeffRat c d a b h : ℝ) := by
  change (barrierDescartesTransform (p.map (Rat.castHom ℝ)) d
      ((Rat.castHom ℝ) a) ((Rat.castHom ℝ) b)).coeff h =
    (Rat.castHom ℝ) (barrierDescartesCoeffRat c d a b h)
  rw [barrierDescartesTransform_coeff]
  simp only [barrierDescartesCoeffRat, map_sum, map_mul, map_pow, map_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.coeff_map, hc j (Finset.mem_range.mp hj)]

end

section

open Polynomial

theorem barrierDescartes_interval_roots_card_le (p : ℝ[X]) (d : ℕ) (a b : ℝ)
    (hd : p.natDegree ≤ d)
    (hne : barrierDescartesTransform p d a b ≠ 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Set.Ioo a b ∧ p.eval x = 0) :
    s.card ≤ (barrierDescartesTransform p d a b).signVariations := by
  classical
  let Q := barrierDescartesTransform p d a b
  let t := (Q.roots.filter (fun x => 0 < x)).toFinset
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℝ => (x - a) / (b - x))
    · intro x hx
      obtain ⟨hpos, hroot⟩ := barrierDescartesTransform_root_of_interval p d hd
        (hs x hx).1 (hs x hx).2
      apply Multiset.mem_toFinset.mpr
      exact Multiset.mem_filter.mpr
        ⟨(Polynomial.mem_roots hne).mpr hroot, hpos⟩
    · intro x hx y hy hxy
      change (x - a) / (b - x) = (y - a) / (b - y) at hxy
      have hix := (barrierMobius_inverse (hs x hx).1).2
      have hiy := (barrierMobius_inverse (hs y hy).1).2
      calc
        x = (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) := hix.symm
        _ = (a + b * ((y - a) / (b - y))) / (1 + (y - a) / (b - y)) := by rw [hxy]
        _ = y := hiy
  have htcard : t.card ≤ Q.roots.countP (fun x => 0 < x) := by
    simpa only [t, Multiset.countP_eq_card_filter] using
      Multiset.toFinset_card_le (Q.roots.filter (fun x => 0 < x))
  exact hcard.trans (htcard.trans (Polynomial.roots_countP_pos_le_signVariations Q))

end

section

open Filter Polynomial
open scoped Topology

theorem barrierDescartesTransform_derivative_eval_eq_zero
    (p : ℝ[X]) (d : ℕ) (a b t : ℝ) (hd : p.natDegree ≤ d)
    (ht : 1 + t ≠ 0)
    (hp : p.eval ((a + b * t) / (1 + t)) = 0)
    (hp' : p.derivative.eval ((a + b * t) / (1 + t)) = 0) :
    (barrierDescartesTransform p d a b).derivative.eval t = 0 := by
  have hden : HasDerivAt (fun u : ℝ => 1 + u) 1 t :=
    (hasDerivAt_id t).const_add 1
  have hnum : HasDerivAt (fun u : ℝ => a + b * u) b t := by
    convert! ((hasDerivAt_id t).const_mul b).const_add a using 1
    simp only [mul_one]
  have hmob := hnum.fun_div hden ht
  have hcomp : HasDerivAt
      (fun u : ℝ => p.eval ((a + b * u) / (1 + u))) 0 t := by
    convert! (p.hasDerivAt ((a + b * t) / (1 + t))).comp t hmob using 1
    simp only [hp', zero_mul]
  have hprod : HasDerivAt
      (fun u : ℝ => (1 + u) ^ d * p.eval ((a + b * u) / (1 + u))) 0 t := by
    convert! (hden.pow d).mul hcomp using 1
    simp only [Pi.pow_apply, hp, mul_zero, add_zero]
  have heval :
      (fun u : ℝ => (barrierDescartesTransform p d a b).eval u) =ᶠ[𝓝 t]
        (fun u : ℝ => (1 + u) ^ d * p.eval ((a + b * u) / (1 + u))) := by
    exact (hden.continuousAt.eventually_ne ht).mono fun u hu =>
      barrierDescartesTransform_eval p d a b u hd hu
  exact ((barrierDescartesTransform p d a b).hasDerivAt t).unique
    (hprod.congr_of_eventuallyEq heval)

theorem barrierDescartesTransform_simple_root_pullback
    (p : ℝ[X]) (d : ℕ) (a b t : ℝ) (hd : p.natDegree ≤ d)
    (ht : 1 + t ≠ 0) (hpne : p ≠ 0)
    (hp : p.eval ((a + b * t) / (1 + t)) = 0)
    (hsimple : (barrierDescartesTransform p d a b).rootMultiplicity t = 1) :
    p.rootMultiplicity ((a + b * t) / (1 + t)) = 1 ∧
      p.derivative.eval ((a + b * t) / (1 + t)) ≠ 0 := by
  have hQne : barrierDescartesTransform p d a b ≠ 0 := by
    intro hzero
    simp [hzero] at hsimple
  have hQroot : (barrierDescartesTransform p d a b).IsRoot t :=
    (barrierDescartesTransform_eval_eq_zero_iff p d a b t hd ht).mpr hp
  have hpderiv : p.derivative.eval ((a + b * t) / (1 + t)) ≠ 0 := by
    intro hzero
    have hQderiv :=
      barrierDescartesTransform_derivative_eval_eq_zero p d a b t hd ht hp hzero
    have hgt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hQne).mpr
      ⟨hQroot, hQderiv⟩
    rw [hsimple] at hgt
    exact (Nat.lt_irrefl 1) hgt
  refine ⟨le_antisymm ?_ ((Polynomial.rootMultiplicity_pos hpne).mpr hp), hpderiv⟩
  by_contra hle
  have hgt : 1 < p.rootMultiplicity ((a + b * t) / (1 + t)) :=
    Nat.lt_of_not_ge hle
  exact hpderiv ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hpne).mp hgt).2

theorem barrierDescartesTransform_interval_simple_root_pullback
    (p : ℝ[X]) (d : ℕ) {a b x : ℝ} (hd : p.natDegree ≤ d)
    (hpne : p ≠ 0) (hx : x ∈ Set.Ioo a b) (hp : p.eval x = 0)
    (hsimple : (barrierDescartesTransform p d a b).rootMultiplicity
      ((x - a) / (b - x)) = 1) :
    p.rootMultiplicity x = 1 ∧ p.derivative.eval x ≠ 0 := by
  obtain ⟨ht, heq⟩ := barrierMobius_inverse hx
  have hden : 1 + (x - a) / (b - x) ≠ 0 := ne_of_gt (by linarith)
  have hroot :
      p.eval ((a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x))) = 0 := by
    rw [heq]
    exact hp
  simpa only [heq] using
    barrierDescartesTransform_simple_root_pullback p d a b ((x - a) / (b - x))
      hd hden hpne hroot hsimple

theorem barrierDescartesTransform_rootMultiplicity_one_of_interval
    (p : ℝ[X]) (d : ℕ) {a b x : ℝ} (hd : p.natDegree ≤ d)
    (hx : x ∈ Set.Ioo a b) (hp : p.eval x = 0)
    (hQ : (barrierDescartesTransform p d a b).rootMultiplicity
      ((x - a) / (b - x)) = 1) :
    p.rootMultiplicity x = 1 := by
  have hpne : p ≠ 0 := by
    intro hzero
    simp [hzero, barrierDescartesTransform] at hQ
  exact (barrierDescartesTransform_interval_simple_root_pullback p d hd hpne hx hp hQ).1

end

open Polynomial
open scoped BigOperators

theorem barrierDescartesTransform_coeff_zero_above {R : Type*} [CommRing R]
    (p : R[X]) (d : ℕ) (a b : R) {h : ℕ} (hh : d < h) :
    (barrierDescartesTransform p d a b).coeff h = 0 := by
  rw [barrierDescartesTransform_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  suffices hsum :
      (∑ k ∈ Finset.range (h + 1),
        (j.choose k : R) * a ^ (j - k) * b ^ k *
          ((d - j).choose (h - k) : R)) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : k ≤ j
  · have hchoose : d - j < h - k := by omega
    rw [Nat.choose_eq_zero_of_lt hchoose, Nat.cast_zero, mul_zero]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkj), Nat.cast_zero]
    simp only [zero_mul]

end InternalCatalan

end

end OAI
