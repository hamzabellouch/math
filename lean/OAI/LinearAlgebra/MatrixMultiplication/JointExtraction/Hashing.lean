import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexModularSeparation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

namespace MatrixMultiplication.JointHashing

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {P R : Type*} [Fintype P] [CommRing R]

def dot (v w : P → R) : R := ∑ i, v i * w i

@[simp] theorem dot_add_right (v w u : P → R) : dot v (w + u) = dot v w + dot v u := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_sub_right (v w u : P → R) : dot v (w - u) = dot v w - dot v u := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem dot_add_left (v w u : P → R) : dot (v + w) u = dot v u + dot w u := by
  simp [dot, add_mul, Finset.sum_add_distrib]

@[simp] theorem dot_sub_left (v w u : P → R) : dot (v - w) u = dot v u - dot w u := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

abbrev Sample (P R : Type*) := (P → R) × R × R

def xHash (s : Sample P R) (I : P → R) := s.2.1 + dot s.1 I
def yHash (s : Sample P R) (J : P → R) := s.2.2 + dot s.1 J

def zHash (two : Rˣ) (s : Sample P R) (S K : P → R) :=
  (↑(two⁻¹) : R) * (s.2.1 + s.2.2 + dot s.1 (S - K))

def Survives (U : Set R) (I J : P → R) (s : Sample P R) : Prop :=
  xHash s I = yHash s J ∧ xHash s I ∈ U

def survivalEquiv (U : Set R) (I J : P → R) :
    {s : Sample P R // Survives U I J s} ≃ (P → R) × U where
  toFun s := (s.val.1, ⟨xHash s.val I, s.property.2⟩)
  invFun vt := ⟨(vt.1, vt.2.val - dot vt.1 I, vt.2.val - dot vt.1 J), by
    simp [Survives, xHash, yHash, vt.2.property]⟩
  left_inv s := by
    apply Subtype.ext
    rcases s with ⟨⟨v, a, b⟩, hs⟩
    dsimp [Survives, xHash, yHash] at hs ⊢
    congr 1
    apply Prod.ext
    · ring
    · linear_combination hs.1
  right_inv vt := by
    rcases vt with ⟨v, t, ht⟩
    simp [xHash]

theorem hash_relation (two : Rˣ) (htwo : (two : R) = 2)
    (s : Sample P R) (I J K S : P → R) (hs : I + J + K = S) :
    xHash s I + yHash s J = 2 * zHash two s S K := by
  have hSK : S - K = I + J := by rw [← hs]; abel
  rw [zHash, ← htwo, ← mul_assoc]
  rw [Units.mul_inv, one_mul, hSK, dot_add_right]
  simp only [xHash, yHash]
  ring

theorem full_survival_iff (two : Rˣ) (htwo : (two : R) = 2)
    (U : Set R)
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample P R) (I J K S : P → R) (hs : I + J + K = S) :
    (xHash s I ∈ U ∧ yHash s J ∈ U ∧ zHash two s S K ∈ U) ↔
      Survives U I J s := by
  have hr := hash_relation two htwo s I J K S hs
  constructor
  · rintro ⟨hx, hy, hz⟩
    obtain ⟨h1, h2⟩ := hAP _ hx _ hy _ hz hr
    exact ⟨h1.trans h2.symm, hx⟩
  · rintro ⟨hxy, hx⟩
    have hz : zHash two s S K = xHash s I := by
      have hh : (two : R) * zHash two s S K = (two : R) * xHash s I := by
        rw [htwo, ← hr, hxy]; ring
      exact two.isUnit.mul_left_cancel hh
    exact ⟨hx, hxy ▸ hx, hz ▸ hx⟩

theorem survival_card [Fintype R] (U : Finset R) (I J : P → R) :
    Fintype.card {s : Sample P R // Survives (U : Set R) I J s} =
      Fintype.card R ^ Fintype.card P * U.card := by
  classical
  rw [Fintype.card_congr (survivalEquiv (U : Set R) I J)]
  simp

omit [CommRing R] in
@[simp] theorem sample_card [Fintype R] :
    Fintype.card (Sample P R) = Fintype.card R ^ Fintype.card P * Fintype.card R ^ 2 := by
  simp [Sample, pow_two]

theorem shared_x_collision_iff (U : Set R) (I J J' : P → R)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I J' s ↔ dot s.1 (J' - J) = 0 := by
  rcases hs with ⟨heq, hU⟩
  simp only [Survives, dot_sub_right]
  constructor
  · intro h
    dsimp [xHash, yHash] at heq h
    linear_combination heq - h.1
  · intro h
    refine ⟨?_, hU⟩
    dsimp [xHash, yHash] at heq ⊢
    linear_combination heq - h

theorem shared_y_collision_iff (U : Set R) (I I' J : P → R)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I' J s ↔ dot s.1 (I' - I) = 0 := by
  rcases hs with ⟨heq, hU⟩
  simp only [Survives, dot_sub_right]
  constructor
  · intro h
    dsimp [xHash, yHash] at heq h
    linear_combination h.1 - heq
  · intro h
    have hx : xHash s I' = xHash s I := by
      dsimp [xHash]
      linear_combination h
    exact ⟨hx.trans heq, hx ▸ hU⟩

def pivot [DecidableEq P] (i : P) (u : Rˣ) (t : R) : P → R :=
  Pi.single i ((↑(u⁻¹) : R) * t)

@[simp] theorem dot_pivot [DecidableEq P] (d : P → R) (i : P)
    (u : Rˣ) (hu : d i = u) (t : R) : dot (pivot i u t) d = t := by
  simp [dot, pivot, Pi.single_apply, hu, mul_comm, mul_left_comm]

def linearSplitEquiv [DecidableEq P] (d : P → R) (i : P)
    (u : Rˣ) (hu : d i = u) :
    (P → R) ≃ R × {v : P → R // dot v d = 0} where
  toFun v := (dot v d, ⟨v - pivot i u (dot v d), by simp [hu]⟩)
  invFun t := t.2.val + pivot i u t.1
  left_inv v := by simp
  right_inv t := by
    rcases t with ⟨t, v, hv⟩
    apply Prod.ext
    · simp [hv, hu]
    · apply Subtype.ext
      simp [hv, hu]

theorem linear_zero_fiber_card [Fintype R]
    (d : P → R) (i : P) (u : Rˣ) (hu : d i = u) :
    Fintype.card R * Fintype.card {v : P → R // dot v d = 0} =
      Fintype.card R ^ Fintype.card P := by
  classical
  have h := Fintype.card_congr (linearSplitEquiv d i u hu)
  simpa only [Fintype.card_prod, Fintype.card_fun] using h.symm

def collisionEquiv (U : Set R) (I J d : P → R) :
    {s : Sample P R // Survives U I J s ∧ dot s.1 d = 0} ≃
      {v : P → R // dot v d = 0} × U where
  toFun s := (⟨s.val.1, s.property.2⟩, ⟨xHash s.val I, s.property.1.2⟩)
  invFun vt := ⟨(vt.1.val, vt.2.val - dot vt.1.val I, vt.2.val - dot vt.1.val J), by
    exact ⟨by simp [Survives, xHash, yHash, vt.2.property], vt.1.property⟩⟩
  left_inv s := by
    apply Subtype.ext
    exact congrArg (fun t : {s : Sample P R // Survives U I J s} => t.val)
      ((survivalEquiv U I J).left_inv ⟨s.val, s.property.1⟩)
  right_inv vt := by
    rcases vt with ⟨⟨v, hv⟩, ⟨t, ht⟩⟩
    simp [xHash]

theorem collision_card_mul [Fintype R]
    (U : Finset R) (I J d : P → R) (i : P) (u : Rˣ) (hu : d i = u) :
    Fintype.card R *
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 d = 0} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  have hcard : Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ dot s.1 d = 0} =
      Fintype.card {v : P → R // dot v d = 0} * U.card := by
    simpa using Fintype.card_congr (collisionEquiv (U : Set R) I J d)
  calc
    _ = Fintype.card R * (Fintype.card {v : P → R // dot v d = 0} * U.card) :=
      congrArg (fun n : ℕ => Fintype.card R * n) hcard
    _ = (Fintype.card R * Fintype.card {v : P → R // dot v d = 0}) * U.card :=
      (mul_assoc _ _ _).symm
    _ = (Fintype.card R ^ Fintype.card P) * U.card :=
      congrArg (fun n : ℕ => n * U.card) (linear_zero_fiber_card d i u hu)
    _ = _ := (survival_card U I J).symm

theorem shared_x_collision_card_mul [Fintype R]
    (U : Finset R) (I J J' : P → R) (i : P) (u : Rˣ)
    (hu : J' i - J i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I J' s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I J' s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (J' - J) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_x_collision_iff (U : Set R) I J J' s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (J' - J) i u hu

theorem shared_y_collision_card_mul [Fintype R]
    (U : Finset R) (I I' J : P → R) (i : P) (u : Rˣ)
    (hu : I' i - I i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I' J s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I' J s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (I' - I) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_y_collision_iff (U : Set R) I I' J s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (I' - I) i u hu

theorem survival_fraction [Fintype R] (U : Finset R) (I J : P → R) :
    (Fintype.card {s : Sample P R // Survives (U : Set R) I J s} : ℝ) /
      Fintype.card (Sample P R) = (U.card : ℝ) / (Fintype.card R : ℝ) ^ 2 := by
  have hR : (Fintype.card R : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [survival_card, sample_card]
  push_cast
  field_simp

theorem collision_fraction [Fintype R]
    (U : Finset R) (hU : U.Nonempty) (I J d : P → R)
    (i : P) (u : Rˣ) (hu : d i = u) :
    (Fintype.card {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 d = 0} : ℝ) /
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} =
        1 / (Fintype.card R : ℝ) := by
  have hR : (Fintype.card R : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hS : (Fintype.card {s : Sample P R // Survives (U : Set R) I J s} : ℝ) ≠ 0 := by
    obtain ⟨t, ht⟩ := hU
    let : Nonempty {s : Sample P R // Survives (U : Set R) I J s} :=
      ⟨(survivalEquiv (U : Set R) I J).symm (0, ⟨t, ht⟩)⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_div_iff hS hR).mpr
  simpa only [Nat.cast_mul, one_mul, mul_one, mul_comm] using
    (congrArg (fun n : ℕ => (n : ℝ)) (collision_card_mul U I J d i u hu))

theorem small_nat_isUnit (k n : ℕ) (hn : 0 < n) (hn16 : n ≤ 16) :
    IsUnit (n : ZMod (37 ^ k)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr
  intro h
  have := Nat.le_of_dvd hn h
  omega

theorem coarse_difference_isUnit (k : ℕ) (a b : Fin 17) (hab : a ≠ b) :
    IsUnit ((a.val : ZMod (37 ^ k)) - (b.val : ZMod (37 ^ k))) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hu := small_nat_isUnit k (b.val - a.val) (Nat.sub_pos_of_lt h) (by omega)
    rw [Nat.cast_sub h.le] at hu
    simpa only [neg_sub] using hu.neg
  · have hu := small_nat_isUnit k (a.val - b.val) (Nat.sub_pos_of_lt h) (by omega)
    rwa [Nat.cast_sub h.le] at hu

theorem coarse_words_unit_coordinate (k : ℕ) (I J : P → Fin 17) (hIJ : I ≠ J) :
    ∃ i : P, IsUnit (((I i : ℕ) : ZMod (37 ^ k)) - ((J i : ℕ) : ZMod (37 ^ k))) := by
  classical
  have hi : ∃ i, I i ≠ J i := by
    by_contra h
    push Not at h
    exact hIJ (funext h)
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, coarse_difference_isUnit k (I i) (J i) hi⟩

theorem shared_z_collision_iff (two : Rˣ) (htwo : (two : R) = 2)
    (U : Set R) (I I' J J' : P → R) (hIJ : I' + J' = I + J)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I' J' s ↔ dot s.1 (I' - I) = 0 := by
  have hsum : dot s.1 I' + dot s.1 J' = dot s.1 I + dot s.1 J := by
    simpa using congrArg (dot s.1) hIJ
  rcases hs with ⟨heq, hU⟩
  rw [dot_sub_right]
  constructor
  · rintro ⟨heq', _⟩
    dsimp [xHash, yHash] at heq heq'
    have hz : (two : R) * (dot s.1 I' - dot s.1 I) = (two : R) * 0 := by
      rw [htwo]
      linear_combination heq' - heq + hsum
    exact two.isUnit.mul_left_cancel hz
  · intro hd
    have hx : xHash s I' = xHash s I := by
      dsimp [xHash]
      linear_combination hd
    have hy : yHash s J' = yHash s J := by
      dsimp [yHash]
      linear_combination hsum - hd
    exact ⟨hx.trans (heq.trans hy.symm), hx ▸ hU⟩

theorem shared_z_collision_card_mul [Fintype R]
    (two : Rˣ) (htwo : (two : R) = 2)
    (U : Finset R) (I I' J J' : P → R) (hIJ : I' + J' = I + J)
    (i : P) (u : Rˣ) (hu : I' i - I i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I' J' s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I' J' s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (I' - I) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_z_collision_iff two htwo (U : Set R) I I' J J' hIJ s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (I' - I) i u hu

end MatrixMultiplication.JointHashing

end OAI
