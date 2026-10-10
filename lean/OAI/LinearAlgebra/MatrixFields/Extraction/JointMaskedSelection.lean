import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointLossCounts
import OAI.LinearAlgebra.MatrixFields.Entropy.JointExtractionRates

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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





noncomputable section

namespace MatrixMultiplication.JointCoarseHashing

attribute [local instance] Classical.propDecidable

abbrev Word (P : Type*) := P → Fin 17
abbrev Triple (P : Type*) := Word P × Word P × Word P

variable {P : Type*}

def HasSupportSum (S : P → ℕ) (e : Triple P) : Prop :=
  ∀ p, (e.1 p).val + (e.2.1 p).val + (e.2.2 p).val = S p

theorem eq_of_shared_xy (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hy : e.2.1 = f.2.1) : e = f := by
  have hz : e.2.2 = f.2.2 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hy] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_shared_xz (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hz : e.2.2 = f.2.2) : e = f := by
  have hy : e.2.1 = f.2.1 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hz] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_shared_yz (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hy : e.2.1 = f.2.1) (hz : e.2.2 = f.2.2) : e = f := by
  have hx : e.1 = f.1 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hy, hz] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

def castWord (k : ℕ) (w : Word P) : P → ZMod (37 ^ k) :=
  fun p => (w p).val

def twoUnit (k : ℕ) : (ZMod (37 ^ k))ˣ :=
  (JointHashing.small_nat_isUnit k 2 (by decide) (by decide)).unit

theorem twoUnit_coe (k : ℕ) : (twoUnit k : ZMod (37 ^ k)) = 2 := by
  exact (JointHashing.small_nat_isUnit k 2 (by decide) (by decide)).unit_spec

theorem supportSum_cast (k : ℕ) (S : P → ℕ) (e : Triple P)
    (he : HasSupportSum S e) :
    castWord k e.1 + castWord k e.2.1 + castWord k e.2.2 =
      fun p => (S p : ZMod (37 ^ k)) := by
  funext p
  have h := congrArg (fun n : ℕ => (n : ZMod (37 ^ k))) (he p)
  simpa only [Nat.cast_add, Pi.add_apply, castWord] using h

theorem shared_z_cast_sum (k : ℕ) (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hz : f.2.2 = e.2.2) :
    castWord k f.1 + castWord k f.2.1 = castWord k e.1 + castWord k e.2.1 := by
  have h := (supportSum_cast k S f hf).trans (supportSum_cast k S e he).symm
  rw [hz] at h
  exact add_right_cancel h

section FiniteHashing

variable [Fintype P]

abbrev Sample (P : Type*) (k : ℕ) := JointHashing.Sample P (ZMod (37 ^ k))

def Survives (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) (s : Sample P k) : Prop :=
  JointHashing.Survives (U : Set (ZMod (37 ^ k))) (castWord k e.1) (castWord k e.2.1) s

theorem full_survival_iff (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (s : Sample P k) :
    (JointHashing.xHash s (castWord k e.1) ∈ U ∧
      JointHashing.yHash s (castWord k e.2.1) ∈ U ∧
      JointHashing.zHash (twoUnit k) s (fun p => (S p : ZMod (37 ^ k)))
        (castWord k e.2.2) ∈ U) ↔ Survives k U e s := by
  exact JointHashing.full_survival_iff (twoUnit k) (twoUnit_coe k)
    (U : Set (ZMod (37 ^ k))) hAP s (castWord k e.1) (castWord k e.2.1)
    (castWord k e.2.2) (fun p => (S p : ZMod (37 ^ k))) (supportSum_cast k S e he)

theorem survival_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    Fintype.card {s : Sample P k // Survives k U e s} =
      (37 ^ k) ^ Fintype.card P * U.card := by
  have hcard := JointHashing.survival_card U (castWord k e.1) (castWord k e.2.1)
  simp only [ZMod.card] at hcard
  simp only [Fintype.card_eq_nat_card] at hcard ⊢
  exact hcard

theorem shared_x_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hx : f.1 = e.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hy : f.2.1 ≠ e.2.1 := fun hy => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.2.1 e.2.1 hy
  have h := JointHashing.shared_x_collision_card_mul U (castWord k e.1)
    (castWord k e.2.1) (castWord k f.2.1) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [Survives, hx] using h

theorem shared_y_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hy : f.2.1 = e.2.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_y_collision_card_mul U (castWord k e.1)
    (castWord k f.1) (castWord k e.2.1) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [Survives, hy] using h

theorem shared_z_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hz : f.2.2 = e.2.2) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xz S f e hf he hx hz)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_z_collision_card_mul (twoUnit k) (twoUnit_coe k)
    U (castWord k e.1) (castWord k f.1) (castWord k e.2.1) (castWord k f.2.1)
    (shared_z_cast_sum k S e f he hf hz) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h

def SharesSide (e f : Triple P) : Prop :=
  f.1 = e.1 ∨ f.2.1 = e.2.1 ∨ f.2.2 = e.2.2

theorem pair_survival_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  rcases hshare with hx | hy | hz
  · exact shared_x_card_mul k U S e f he hf hne hx
  · exact shared_y_card_mul k U S e f he hf hne hy
  · exact shared_z_card_mul k U S e f he hf hne hz

def ownEvent (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) : Finset (Sample P k) :=
  Finset.univ.filter (Survives k U e)

theorem ownEvent_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    (ownEvent k U e).card = (37 ^ k) ^ Fintype.card P * U.card := by
  simpa only [ownEvent, Fintype.card_subtype] using survival_card k U e

theorem pair_event_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter (Survives k U f)).card = (ownEvent k U e).card := by
  simpa only [ownEvent, Finset.filter_filter, Fintype.card_subtype] using
    pair_survival_card_mul k U S e f he hf hne hshare

theorem competitor_union_card_mul_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter
      (fun s => ∃ f ∈ competitors, Survives k U f s)).card ≤
        competitors.card * (ownEvent k U e).card := by
  apply JointLossCounts.competitor_union_card_mul_le
  intro f hf'
  exact (pair_event_card_mul k U S e f he (hf f hf') (hne f hf') (hshare f hf')).le

theorem competitor_union_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      ((competitors.card : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U e).card : ℝ) := by
  have hM : (0 : ℝ) < ((37 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by decide : 0 < (37 : ℕ)) k)
  have h := competitor_union_card_mul_le k U S e he competitors hf hne hshare
  have hR : ((37 ^ k : ℕ) : ℝ) *
      (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      (competitors.card : ℝ) * ((ownEvent k U e).card : ℝ) := by exact_mod_cast h
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hM).2 (by simpa only [mul_comm] using hR)

theorem pair_survival_fraction (k : ℕ) (U : Finset (ZMod (37 ^ k))) (hU : U.Nonempty)
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (((ownEvent k U e).filter (Survives k U f)).card : ℝ) / ((ownEvent k U e).card : ℝ) =
      1 / ((37 ^ k : ℕ) : ℝ) := by
  have hM : (0 : ℕ) < 37 ^ k := pow_pos (by decide) k
  have hS : 0 < (ownEvent k U e).card := by
    rw [ownEvent_card]
    exact Nat.mul_pos (pow_pos hM _) (Finset.card_pos.mpr hU)
  apply (div_eq_div_iff (by exact_mod_cast Nat.ne_of_gt hS)
    (by exact_mod_cast Nat.ne_of_gt hM)).2
  have h := congrArg (fun n : ℕ => (n : ℝ)) (pair_event_card_mul k U S e f he hf hne hshare)
  simpa only [Nat.cast_mul, one_mul, mul_comm] using h

end FiniteHashing

end MatrixMultiplication.JointCoarseHashing






namespace MatrixMultiplication.JointOrdinarySelection

open JointCoarseHashing JointExtractionRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {P E : Type*}

def neighbors (ambient : Finset (Triple P)) (e : Triple P) : Finset (Triple P) :=
  ambient.filter (fun f => f ≠ e ∧ SharesSide e f)

@[simp] theorem mem_neighbors (ambient : Finset (Triple P)) (e f : Triple P) :
    f ∈ neighbors ambient e ↔ f ∈ ambient ∧ f ≠ e ∧ SharesSide e f := by
  simp only [neighbors, Finset.mem_filter]

section Finite

variable [Fintype P]

def Bad (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) (s : Sample P k) : Prop :=
  ∃ f ∈ neighbors ambient e, Survives k U f s

def Good (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) (s : Sample P k) : Prop :=
  Survives k U e s ∧ ¬ Bad k U ambient e s

def goodEvent (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) : Finset (Sample P k) :=
  (ownEvent k U e).filter (fun s => ¬ Bad k U ambient e s)

@[simp] theorem mem_goodEvent (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e : Triple P) (s : Sample P k) :
    s ∈ goodEvent k U ambient e ↔ Good k U ambient e s := by
  simp only [goodEvent, ownEvent, Finset.mem_filter, Finset.mem_univ, true_and, Good]

theorem good_excludes_neighbor (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e f : Triple P) (s : Sample P k)
    (hg : Good k U ambient e s) (hf : f ∈ ambient) (hne : f ≠ e)
    (hshare : SharesSide e f) : ¬ Survives k U f s := by
  intro hs
  exact hg.2 ⟨f, (mem_neighbors ambient e f).2 ⟨hf, hne, hshare⟩, hs⟩

theorem good_no_shared_side (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e f : Triple P) (s : Sample P k)
    (he : Good k U ambient e s) (hf : Good k U ambient f s)
    (hmem : f ∈ ambient) (hne : f ≠ e) : ¬ SharesSide e f := by
  intro hshare
  exact good_excludes_neighbor k U ambient e f s he hmem hne hshare hf.1

theorem ownEvent_card_real (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    ((ownEvent k U e).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  rw [ownEvent_card, JointHashing.sample_card, ZMod.card]
  push_cast
  field_simp

theorem bad_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (e : Triple P) (he : e ∈ ambient) :
    (((ownEvent k U e).filter (Bad k U ambient e)).card : ℝ) ≤
      ((neighbors ambient e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) *
        ((ownEvent k U e).card : ℝ) := by
  have hset : (ownEvent k U e).filter (Bad k U ambient e) =
      (ownEvent k U e).filter (fun s => ∃ f ∈ neighbors ambient e, Survives k U f s) := by
    ext s
    simp only [Finset.mem_filter, Bad]
  rw [hset]
  apply competitor_union_card_le k U S e (hsupport e he) (neighbors ambient e)
  · intro f hf
    exact hsupport f ((mem_neighbors ambient e f).mp hf).1
  · intro f hf
    exact ((mem_neighbors ambient e f).mp hf).2.1
  · intro f hf
    exact ((mem_neighbors ambient e f).mp hf).2.2

theorem goodEvent_card_lower (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (e : Triple P) (he : e ∈ ambient) (D : ℕ)
    (hdegree : (neighbors ambient e).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (goodEvent k U ambient e).card := by
  have hM : (0 : ℝ) ≤ ((37 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdeg : ((neighbors ambient e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hdegree) hM).trans hsmall
  have hb : (((ownEvent k U e).filter (Bad k U ambient e)).card : ℝ) ≤
      (1 / 2) * ((ownEvent k U e).card : ℝ) :=
    (bad_card_le k U ambient S hsupport e he).trans
      (mul_le_mul_of_nonneg_right hdeg (Nat.cast_nonneg _))
  have hg := JointLossCounts.good_card_lower (ownEvent k U e) (Bad k U ambient e)
    (1 / 2) hb
  rw [ownEvent_card_real] at hg
  change _ ≤ ((goodEvent k U ambient e).card : ℝ) at hg
  convert hg using 1
  ring

theorem goodIncidence_eq (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (coarse : E → Triple P) (e : E) :
    goodIncidence (fun s e => Good k U ambient (coarse e) s) e =
      (goodEvent k U ambient (coarse e)).card := by
  unfold goodIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodEvent]

theorem exists_selection_of_degree_bound [Fintype E]
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ) (coarse : E → Triple P)
    (hinj : Function.Injective coarse)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (htarget : ∀ e, coarse e ∈ ambient) (D : ℕ)
    (hdegree : ∀ e, (neighbors ambient (coarse e)).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2)
    (K : ℕ) (hK : (K : ℝ) ≤ (Fintype.card E : ℝ) *
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)) :
    ∃ (s : Sample P k) (G : Finset E), G.card = K ∧
      (∀ e ∈ G, Good k U ambient (coarse e) s) ∧
      (G : Set E).Pairwise (fun e f => ¬ SharesSide (coarse e) (coarse f)) := by
  classical
  have hi (e : E) :
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample P k) : ℝ) ≤
      (goodIncidence (fun s e => Good k U ambient (coarse e) s) e : ℝ) := by
    rw [goodIncidence_eq]
    exact goodEvent_card_lower k U ambient S hsupport (coarse e) (htarget e) D
      (hdegree e) hsmall
  obtain ⟨s, hs⟩ := exists_goodCount_ge (fun s e => Good k U ambient (coarse e) s) _ hi
  have hk : K ≤ goodCount (fun s e => Good k U ambient (coarse e) s) s := by
    exact_mod_cast hK.trans hs
  obtain ⟨G, hcard, hgood⟩ := exists_good_subfamily
    (fun s e => Good k U ambient (coarse e) s) s K hk
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact good_no_shared_side k U ambient (coarse e) (coarse f) s
    (hgood e he) (hgood f hf) (htarget f) (fun h => hne (hinj h).symm)

theorem exists_selection_floor [Fintype E]
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ) (coarse : E → Triple P)
    (hinj : Function.Injective coarse)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (htarget : ∀ e, coarse e ∈ ambient) (D : ℕ)
    (hdegree : ∀ e, (neighbors ambient (coarse e)).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2) :
    ∃ (s : Sample P k) (G : Finset E),
      G.card = ⌊(Fintype.card E : ℝ) *
        ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)⌋₊ ∧
      (∀ e ∈ G, Good k U ambient (coarse e) s) ∧
      (G : Set E).Pairwise (fun e f => ¬ SharesSide (coarse e) (coarse f)) := by
  apply exists_selection_of_degree_bound k U ambient S coarse hinj hsupport htarget D
    hdegree hsmall _ (Nat.floor_le ?_)
  positivity

end Finite

def hashLevel (H : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) * H / Real.log 37⌋₊ + 1

def hashSet (H : ℝ) (N : ℕ) : Finset (ZMod (37 ^ hashLevel H N)) :=
  JointAPFree.modularSet (hashModulus H N)

theorem hashSet_AP (H : ℝ) (N : ℕ) :
    ∀ x ∈ hashSet H N, ∀ y ∈ hashSet H N, ∀ z ∈ hashSet H N,
      x + y = 2 * z → x = z ∧ y = z :=
  JointAPFree.modularSet_hashAP (hashModulus H N)

theorem eventually_exists_selection
    {P E : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (ambient : ∀ N, Finset (Triple (P N))) (S : ∀ N, P N → ℕ)
    (coarse : ∀ N, E N → Triple (P N))
    (hinj : ∀ N, Function.Injective (coarse N))
    (hsupport : ∀ N, ∀ f ∈ ambient N, HasSupportSum (S N) f)
    (htarget : ∀ N e, coarse N e ∈ ambient N)
    (degree : ℕ → ℕ)
    (hdegree : ∀ N e, (neighbors (ambient N) (coarse N e)).card ≤ degree N)
    {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, Good (hashLevel H N) (hashSet H N) (ambient N) (coarse N e) s) ∧
      (G : Set (E N)).Pairwise (fun e f => ¬ SharesSide (coarse N e) (coarse N f)) := by
  classical
  let c : ℝ := (H - D) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hclt : c < H - D := by dsimp [c]; linarith
  have hratio := eventually_degree_div_hashModulus_le_exp hH hdegreeRate hclt
  have hsmall : ∀ᶠ N in atTop,
      (degree N : ℝ) / (hashModulus H N : ℝ) ≤ 1 / 2 := by
    apply eventually_error_le_half 1 0 hc
    simpa only [pow_zero, one_mul] using hratio
  let good := fun N (s : Sample (P N) (hashLevel H N)) (e : E N) =>
    Good (hashLevel H N) (hashSet H N) (ambient N) (coarse N e) s
  have hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample (P N) (hashLevel H N)) : ℝ) ≤
          (goodIncidence (good N) e : ℝ) := by
    filter_upwards [hsmall] with N hN e
    rw [show goodIncidence (good N) e =
        (goodEvent (hashLevel H N) (hashSet H N) (ambient N) (coarse N e)).card from
      goodIncidence_eq _ _ _ _ _]
    exact goodEvent_card_lower (hashLevel H N) (hashSet H N) (ambient N) (S N)
      (hsupport N) (coarse N e) (htarget N e) (degree N) (hdegree N e) hN
  have hyield := eventually_exists_many_good_explicit good hH hpos hinc hE hε
  have hselection := eventually_exists_good_subfamily good
    (fun N => ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊) hyield
  filter_upwards [hselection] with N hN
  obtain ⟨s, G, hcard, hgood⟩ := hN
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact good_no_shared_side (hashLevel H N) (hashSet H N) (ambient N)
    (coarse N e) (coarse N f) s (hgood e he) (hgood f hf) (htarget N f)
    (fun h => hne ((hinj N) h).symm)

end MatrixMultiplication.JointOrdinarySelection






namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

structure OrbitData (P E O V : Type*) where
  ambient : Finset (Triple P)
  support : P → ℕ
  coarse : E → Triple P
  support_ambient : ∀ f ∈ ambient, HasSupportSum support f
  target_mem : ∀ e, coarse e ∈ ambient
  orbits : E → Finset O
  full : E → O → Finset V
  passing : E → O → Finset V
  full_pos : ∀ e, ∀ o ∈ orbits e, 0 < (full e o).card
  passing_subset : ∀ e, ∀ o ∈ orbits e, passing e o ⊆ full e o
  competitors : E → O → V → Finset (Triple P)
  competitor_mem : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, f ∈ ambient
  competitor_ne : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, f ≠ coarse e
  competitor_shares : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, SharesSide (coarse e) f

namespace OrbitData

def eligibilityCompetitors (d : OrbitData P E O V) (e : E) : Finset (Triple P) :=
  d.ambient.filter (fun f => f ≠ d.coarse e ∧ f.1 = (d.coarse e).1)

@[simp] theorem mem_eligibilityCompetitors (d : OrbitData P E O V) (e : E) (f : Triple P) :
    f ∈ d.eligibilityCompetitors e ↔
      f ∈ d.ambient ∧ f ≠ d.coarse e ∧ f.1 = (d.coarse e).1 := by
  simp only [eligibilityCompetitors, Finset.mem_filter]

section Finite

variable [Fintype P]

def variableBad (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (e : E) (o : O) (v : V) (s : Sample P k) : Prop :=
  ∃ f ∈ d.competitors e o v, Survives k U f s

def eligibilityGood (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (e : E) (s : Sample P k) : Prop :=
  ¬ ∃ f ∈ d.eligibilityCompetitors e, Survives k U f s

def Failure (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) (s : Sample P k) : Prop :=
  JointLossCounts.targetBad (d.orbits e) (d.full e) (d.passing e)
    (d.variableBad k U e) (d.eligibilityGood k U e) N s

def Good (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) (s : Sample P k) : Prop :=
  Survives k U (d.coarse e) s ∧ ¬ d.Failure k U N e s

def goodEvent (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) : Finset (Sample P k) :=
  (ownEvent k U (d.coarse e)).filter (fun s => ¬ d.Failure k U N e s)

@[simp] theorem mem_goodEvent (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k) :
    s ∈ d.goodEvent k U N e ↔ d.Good k U N e s := by
  simp only [goodEvent, ownEvent, Finset.mem_filter, Finset.mem_univ, true_and, Good]

theorem variableBad_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) (o : O) (ho : o ∈ d.orbits e)
    (v : V) (hv : v ∈ d.passing e o) (D : ℕ)
    (hdegree : (d.competitors e o v).card ≤ D) :
    (((ownEvent k U (d.coarse e)).filter (d.variableBad k U e o v)).card : ℝ) ≤
      ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U (d.coarse e)).card : ℝ) := by
  have h := competitor_union_card_le k U d.support (d.coarse e)
    (d.support_ambient _ (d.target_mem e)) (d.competitors e o v)
    (fun f hf => d.support_ambient f (d.competitor_mem e o ho v hv f hf))
    (d.competitor_ne e o ho v hv) (d.competitor_shares e o ho v hv)
  have hdegreeR : ((d.competitors e o v).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdegree
  have hfilter : (ownEvent k U (d.coarse e)).filter (d.variableBad k U e o v) =
      (ownEvent k U (d.coarse e)).filter
        (fun s => ∃ f ∈ d.competitors e o v, Survives k U f s) := by
    ext s
    simp only [Finset.mem_filter, variableBad]
  rw [hfilter]
  exact h.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hdegreeR (Nat.cast_nonneg _))
    (Nat.cast_nonneg _))

theorem eligibilityFailure_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) :
    (((ownEvent k U (d.coarse e)).filter (fun s => ¬ d.eligibilityGood k U e s)).card : ℝ) ≤
      (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ)) *
        ((ownEvent k U (d.coarse e)).card : ℝ) := by
  have h := competitor_union_card_le k U d.support (d.coarse e)
    (d.support_ambient _ (d.target_mem e)) (d.eligibilityCompetitors e)
    (fun f hf => d.support_ambient f ((d.mem_eligibilityCompetitors e f).1 hf).1)
    (fun f hf => ((d.mem_eligibilityCompetitors e f).1 hf).2.1)
    (fun f hf => Or.inl ((d.mem_eligibilityCompetitors e f).1 hf).2.2)
  simpa only [eligibilityGood, not_not] using h

theorem failure_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D) :
    (((ownEvent k U (d.coarse e)).filter (d.Failure k U N e)).card : ℝ) ≤
      (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
        ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ))) *
          ((ownEvent k U (d.coarse e)).card : ℝ) := by
  exact JointLossCounts.targetBad_card_le (ownEvent k U (d.coarse e))
    (d.orbits e) (d.full e) (d.passing e) (d.variableBad k U e)
    (d.eligibilityGood k U e) ((D : ℝ) / ((37 ^ k : ℕ) : ℝ))
    (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ)) N
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hN (d.full_pos e)
    (d.passing_subset e)
    (fun o ho v hv => d.variableBad_card_le k U e o ho v hv D (hdegree o ho v hv))
    (d.eligibilityFailure_card_le k U e)

theorem ownEvent_card_real (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) :
    ((ownEvent k U (d.coarse e)).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  exact JointOrdinarySelection.ownEvent_card_real k U (d.coarse e)

theorem goodEvent_card_lower (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D)
    (hsmall : ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
      ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (d.goodEvent k U N e).card := by
  have hb : (((ownEvent k U (d.coarse e)).filter (d.Failure k U N e)).card : ℝ) ≤
      (1 / 2) * ((ownEvent k U (d.coarse e)).card : ℝ) :=
    (d.failure_card_le k U N hN e D hdegree).trans
      (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _))
  have hg := JointLossCounts.good_card_lower (ownEvent k U (d.coarse e))
    (d.Failure k U N e) (1 / 2) hb
  rw [d.ownEvent_card_real] at hg
  change _ ≤ ((d.goodEvent k U N e).card : ℝ) at hg
  convert hg using 1
  ring

theorem goodIncidence_eq (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) :
    goodIncidence (fun s e => d.Good k U N e s) e = (d.goodEvent k U N e).card := by
  unfold goodIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodEvent]

theorem good_eligibility (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s) : d.eligibilityGood k U e s := by
  by_contra h
  exact hg.2 (Or.inl h)

theorem good_no_shared_x (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e f : E) (s : Sample P k)
    (he : d.Good k U N e s) (hf : d.Good k U N f s)
    (hne : d.coarse f ≠ d.coarse e) : (d.coarse f).1 ≠ (d.coarse e).1 := by
  intro hx
  exact d.good_eligibility k U N e s he
    ⟨d.coarse f, (d.mem_eligibilityCompetitors e _).2 ⟨d.target_mem f, hne, hx⟩, hf.1⟩

theorem good_missingFraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (C₀ N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s)
    (hdet : ∀ o ∈ d.orbits e,
      JointLossCounts.deterministicLossFraction (d.full e o) (d.passing e o) ≤ C₀ / N)
    (o : O) (ho : o ∈ d.orbits e) :
    JointLossCounts.missingFraction (d.full e o) (d.passing e o)
      (d.variableBad k U e o) s ≤ (C₀ + 1) / N :=
  JointLossCounts.good_missingFraction_le (d.orbits e) (d.full e) (d.passing e)
    (d.variableBad k U e) (d.eligibilityGood k U e) C₀ N s hg.2
    (d.passing_subset e) hdet o ho

theorem exists_selection [Fintype E] (d : OrbitData P E O V)
    (hinj : Function.Injective d.coarse) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (C₀ N : ℝ) (hN : 0 < N) (D K : ℕ)
    (hdegree : ∀ e, ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o,
      (d.competitors e o v).card ≤ D)
    (hsmall : ∀ e, ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
      ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2)
    (hdet : ∀ e, ∀ o ∈ d.orbits e,
      JointLossCounts.deterministicLossFraction (d.full e o) (d.passing e o) ≤ C₀ / N)
    (hK : (K : ℝ) ≤ (Fintype.card E : ℝ) *
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)) :
    ∃ (s : Sample P k) (G : Finset E), G.card = K ∧
      (∀ e ∈ G, d.Good k U N e s) ∧
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → (d.coarse e).1 ≠ (d.coarse f).1) ∧
      ∀ e ∈ G, ∀ o ∈ d.orbits e,
        JointLossCounts.missingFraction (d.full e o) (d.passing e o)
          (d.variableBad k U e o) s ≤ (C₀ + 1) / N := by
  classical
  have hi (e : E) :
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample P k) : ℝ) ≤
      (goodIncidence (fun s e => d.Good k U N e s) e : ℝ) := by
    rw [d.goodIncidence_eq]
    exact d.goodEvent_card_lower k U N hN e D (hdegree e) (hsmall e)
  obtain ⟨s, hs⟩ := exists_goodCount_ge (fun s e => d.Good k U N e s) _ hi
  have hk : K ≤ goodCount (fun s e => d.Good k U N e s) s := by exact_mod_cast hK.trans hs
  obtain ⟨G, hcard, hgood⟩ := exists_good_subfamily (fun s e => d.Good k U N e s) s K hk
  refine ⟨s, G, hcard, hgood, ?_, ?_⟩
  · intro e he f hf hne
    exact d.good_no_shared_x k U N f e s (hgood f hf) (hgood e he)
      (fun h => hne (hinj h))
  · intro e he o ho
    exact d.good_missingFraction_le k U C₀ N e s (hgood e he) (hdet e) o ho

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end
end

end MatrixAllFields

end OAI
