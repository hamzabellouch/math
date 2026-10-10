import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.FiniteCover
import OAI.LinearAlgebra.MatrixFields.Tensors.ComplexDotPairing

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.ExactRecovery

variable {K X Y Z I A B C : Type*} [CommSemiring K]

def delete (Q : Tensor K X Y Z) (px : X → Prop) (py : Y → Prop)
    (pz : Z → Prop) [DecidablePred px] [DecidablePred py] [DecidablePred pz] :
    Tensor K X Y Z := fun x y z => if px x ∧ py y ∧ pz z then Q x y z else 0

def presence [Fintype I] [DecidableEq I] (p : I → X → Prop)
    [∀ i, DecidablePred (p i)] (x : X) : Finset I :=
  Finset.univ.filter fun i => p i x

@[simp] theorem mem_presence [Fintype I] [DecidableEq I] (p : I → X → Prop)
    [∀ i, DecidablePred (p i)] (x : X) (i : I) :
    i ∈ presence p x ↔ p i x := by simp [presence]

theorem restrict_rectangles
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Q H : Tensor K X Y Z) (cx : X → A) (cy : Y → B) (cz : Z → C)
    (fx : A × B × C → X → X) (fy : A × B × C → Y → Y)
    (fz : A × B × C → Z → Z)
    (h : ∀ x y z, H (fx (cx x, cy y, cz z) x)
      (fy (cx x, cy y, cz z) y) (fz (cx x, cy y, cz z) z) = Q x y z) :
    Tensor.restrict
      (fun x s => if cx x = s.1.1 ∧ s.2 = fx s.1 x then (1 : K) else 0)
      (fun y s => if cy y = s.1.2.1 ∧ s.2 = fy s.1 y then (1 : K) else 0)
      (fun z s => if cz z = s.1.2.2 ∧ s.2 = fz s.1 z then (1 : K) else 0)
      (Tensor.directSum (fun _ : A × B × C => H)) = Q := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, h]

theorem repair_of_cover
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I] [DecidableEq I] [Nonempty I]
    (Q H : Tensor K X Y Z)
    (px : I → X → Prop) (py : I → Y → Prop) (pz : I → Z → Prop)
    (fx : I → X → X) (fy : I → Y → Y) (fz : I → Z → Z)
    (hshift : ∀ i x y z, H (fx i x) (fy i y) (fz i z) =
      @delete K X Y Z _ Q (px i) (py i) (pz i)
        (Classical.decPred _) (Classical.decPred _) (Classical.decPred _) x y z)
    (hcover : ∀ x y z, Q x y z ≠ 0 → ∃ i, px i x ∧ py i y ∧ pz i z) :
    ∃ (a : X → ((Finset I × Finset I × Finset I) × X) → K)
      (b : Y → ((Finset I × Finset I × Finset I) × Y) → K)
      (c : Z → ((Finset I × Finset I × Finset I) × Z) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : Finset I × Finset I × Finset I => H)) = Q := by
  classical
  let pick : Finset I × Finset I × Finset I → I := fun r =>
    if h : ∃ i, i ∈ r.1 ∧ i ∈ r.2.1 ∧ i ∈ r.2.2 then Classical.choose h
    else Classical.choice inferInstance
  have hpick (r : Finset I × Finset I × Finset I)
      (hr : ∃ i, i ∈ r.1 ∧ i ∈ r.2.1 ∧ i ∈ r.2.2) :
      pick r ∈ r.1 ∧ pick r ∈ r.2.1 ∧ pick r ∈ r.2.2 := by
    simpa [pick, hr] using Classical.choose_spec hr
  let cx := presence px
  let cy := presence py
  let cz := presence pz
  have hrect (x : X) (y : Y) (z : Z) :
      H (fx (pick (cx x, cy y, cz z)) x)
        (fy (pick (cx x, cy y, cz z)) y)
        (fz (pick (cx x, cy y, cz z)) z) = Q x y z := by
    rw [hshift]
    by_cases hq : Q x y z = 0
    · simp [delete, hq]
    · rcases hcover x y z hq with ⟨i, hix, hiy, hiz⟩
      have hp := hpick (cx x, cy y, cz z)
        ⟨i, by simpa [cx] using hix, by simpa [cy] using hiy,
          by simpa [cz] using hiz⟩
      have hpx : px (pick (cx x, cy y, cz z)) x := by simpa [cx] using hp.1
      have hpy : py (pick (cx x, cy y, cz z)) y := by simpa [cy] using hp.2.1
      have hpz : pz (pick (cx x, cy y, cz z)) z := by simpa [cz] using hp.2.2
      simp [delete, hpx, hpy, hpz]
  exact ⟨_, _, _, restrict_rectangles Q H cx cy cz
    (fun r => fx (pick r)) (fun r => fy (pick r)) (fun r => fz (pick r)) hrect⟩

theorem card_mask_rectangles [Fintype I] :
    Fintype.card (Finset I × Finset I × Finset I) = 2 ^ (3 * Fintype.card I) := by
  classical
  simp only [Fintype.card_prod, Fintype.card_finset]
  rw [Nat.mul_comm 3 (Fintype.card I), pow_mul]
  simp [pow_succ, mul_assoc]

theorem repair_of_counting
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq I]
    (Q H : Tensor K X Y Z)
    (px : I → X → Prop) (py : I → Y → Prop) (pz : I → Z → Prop)
    (fx : I → X → X) (fy : I → Y → Y) (fz : I → Z → Z)
    (hshift : ∀ i x y z, H (fx i x) (fy i y) (fz i z) =
      @delete K X Y Z _ Q (px i) (py i) (pz i)
        (Classical.decPred _) (Classical.decPred _) (Classical.decPred _) x y z)
    (t L : ℕ) (hL : 0 < L)
    (hbad : ∀ x y z, Q x y z ≠ 0 →
      (@Finset.filter I (fun i => ¬(px i x ∧ py i y ∧ pz i z))
        (Classical.decPred _) Finset.univ).card ≤ t)
    (hbudget : (@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card * t ^ L <
        Fintype.card I ^ L) :
    ∃ (a : X → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × X) → K)
      (b : Y → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Y) → K)
      (c : Z → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Z) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : Finset (Fin L) × Finset (Fin L) × Finset (Fin L) => H)) = Q := by
  classical
  let support : Finset (X × Y × Z) := @Finset.filter (X × Y × Z)
    (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ
  let good (i : I) (p : X × Y × Z) : Prop := px i p.1 ∧ py i p.2.1 ∧ pz i p.2.2
  have hbad' : ∀ p ∈ support, (Finset.univ.filter fun i => ¬good i p).card ≤ t := by
    intro p hp
    have heq : (Finset.univ.filter fun i => ¬good i p) =
        @Finset.filter I (fun i => ¬(px i p.1 ∧ py i p.2.1 ∧ pz i p.2.2))
          (Classical.decPred _) Finset.univ := by
      ext i
      simp only [Finset.mem_filter, good]
    rw [heq]
    apply hbad p.1 p.2.1 p.2.2
    simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  obtain ⟨f, hf⟩ := FiniteCover.exists_cover support good t L hbad' hbudget
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  exact repair_of_cover Q H (fun i => px (f i)) (fun i => py (f i))
    (fun i => pz (f i)) (fun i => fx (f i)) (fun i => fy (f i))
    (fun i => fz (f i)) (fun i => hshift (f i))
    (fun x y z hq => hf (x, y, z) (by simp [support, hq]))

end MatrixMultiplication.ExactRecovery

end




section
open scoped BigOperators

namespace MatrixMultiplication.OrbitCounting

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

def orbitSet (x : X) : Finset X := Finset.univ.image fun g : G => g • x

@[simp] theorem smul_mem_orbitSet (x : X) (g : G) : g • x ∈ orbitSet (G := G) x := by
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

theorem card_fiber_eq (x y : X) (hy : y ∈ orbitSet (G := G) x) :
    Fintype.card {g : G // g • x = y} = Fintype.card {g : G // g • x = x} := by
  classical
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hy
  let e : {g : G // g • x = y} ≃ {g : G // g • x = x} :=
    { toFun := fun g => ⟨r⁻¹ * g.1, by
        rw [mul_smul, g.2, ← hr, inv_smul_smul]⟩
      invFun := fun g => ⟨r * g.1, by
        rw [mul_smul, g.2, hr]⟩
      left_inv := by intro g; apply Subtype.ext; simp
      right_inv := by intro g; apply Subtype.ext; simp }
  exact Fintype.card_congr e

theorem card_group (x : X) :
    Fintype.card G = (orbitSet (G := G) x).card *
      Fintype.card {g : G // g • x = x} := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquiv (fun g : G => g • x)
    (fun y => y ∈ orbitSet (G := G) x) (smul_mem_orbitSet x)
  calc
    Fintype.card G = Fintype.card (Σ y : {y // y ∈ orbitSet (G := G) x},
        {g : G // g • x = y.1}) := (Fintype.card_congr e).symm
    _ = ∑ y : {y // y ∈ orbitSet (G := G) x},
        Fintype.card {g : G // g • x = y.1} := Fintype.card_sigma
    _ = ∑ _y : {y // y ∈ orbitSet (G := G) x},
        Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_fiber_eq x y.1 y.2
    _ = _ := by simp

theorem bad_shift_count (x : X) (bad : X → Prop) [DecidablePred bad] :
    (Finset.univ.filter fun g : G => bad (g • x)).card =
      ((orbitSet (G := G) x).filter bad).card *
        Fintype.card {g : G // g • x = x} := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (fun g : G => g • x)
    (p := fun g => bad (g • x))
    (q := fun y => y ∈ (orbitSet (G := G) x).filter bad)
    (fun g => by simp)
  calc
    (Finset.univ.filter fun g : G => bad (g • x)).card =
        Fintype.card {g : G // bad (g • x)} := (Fintype.card_subtype _).symm
    _ = Fintype.card (Σ y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        {g : G // g • x = y.1}) := (Fintype.card_congr e).symm
    _ = ∑ y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        Fintype.card {g : G // g • x = y.1} := Fintype.card_sigma
    _ = ∑ _y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_fiber_eq x y.1 (Finset.mem_filter.mp y.2).1
    _ = _ := by simp

theorem bad_shift_bound (x : X) (bad : X → Prop) [DecidablePred bad] (N C : ℕ)
    (h : N * ((orbitSet (G := G) x).filter bad).card ≤ C * (orbitSet (G := G) x).card) :
    N * (Finset.univ.filter fun g : G => bad (g • x)).card ≤ C * Fintype.card G := by
  rw [bad_shift_count, card_group (G := G) x]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right
    (Fintype.card {g : G // g • x = x}) h

theorem bad_shift_fraction (x : X) (bad : X → Prop) [DecidablePred bad] :
    ((Finset.univ.filter fun g : G => bad (g • x)).card : ℝ) / Fintype.card G =
      (((orbitSet (G := G) x).filter bad).card : ℝ) / (orbitSet (G := G) x).card := by
  have hsNat : 0 < Fintype.card {g : G // g • x = x} :=
    Fintype.card_pos_iff.mpr ⟨⟨1, one_smul G x⟩⟩
  have hs : (Fintype.card {g : G // g • x = x} : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsNat)
  rw [bad_shift_count, card_group (G := G) x]
  simp only [Nat.cast_mul]
  exact mul_div_mul_right _ _ hs

end MatrixMultiplication.OrbitCounting

end




section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.OrbitRecovery

variable {G X Y Z : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def badShifts (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (x : X) (y : Y) (z : Z) : Finset G :=
  Finset.univ.filter fun g => ¬(px (g • x) ∧ py (g • y) ∧ pz (g • z))

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem badShifts_card_le (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (x : X) (y : Y) (z : Z) :
    (badShifts (G := G) px py pz x y z).card ≤
      (Finset.univ.filter fun g : G => ¬px (g • x)).card +
      (Finset.univ.filter fun g : G => ¬py (g • y)).card +
      (Finset.univ.filter fun g : G => ¬pz (g • z)).card := by
  classical
  have heq : badShifts (G := G) px py pz x y z =
      (Finset.univ.filter fun g : G => ¬px (g • x)) ∪
      ((Finset.univ.filter fun g : G => ¬py (g • y)) ∪
        (Finset.univ.filter fun g : G => ¬pz (g • z))) := by
    ext g
    by_cases hx : px (g • x) <;> by_cases hy : py (g • y) <;>
      by_cases hz : pz (g • z) <;> simp [badShifts, hx, hy, hz]
  rw [heq]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add_left (Finset.card_union_le _ _) _).trans (le_of_eq (Nat.add_assoc _ _ _).symm))

theorem badShifts_fraction_le_at (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (γ : ℝ) (x : X) (y : Y) (z : Z)
    (hx : (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ γ)
    (hy : (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ γ)
    (hz : (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ γ)
    :
    ((badShifts (G := G) px py pz x y z).card : ℝ) / Fintype.card G ≤ 3 * γ := by
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hx' := hx
  have hy' := hy
  have hz' := hz
  rw [← OrbitCounting.bad_shift_fraction (G := G) x (fun v => ¬px v)] at hx'
  rw [← OrbitCounting.bad_shift_fraction (G := G) y (fun v => ¬py v)] at hy'
  rw [← OrbitCounting.bad_shift_fraction (G := G) z (fun v => ¬pz v)] at hz'
  have hxc := (div_le_iff₀ hg).mp hx'
  have hyc := (div_le_iff₀ hg).mp hy'
  have hzc := (div_le_iff₀ hg).mp hz'
  have hc : ((badShifts (G := G) px py pz x y z).card : ℝ) ≤
      ((Finset.univ.filter fun g : G => ¬px (g • x)).card : ℝ) +
      ((Finset.univ.filter fun g : G => ¬py (g • y)).card : ℝ) +
      ((Finset.univ.filter fun g : G => ¬pz (g • z)).card : ℝ) := by
    exact_mod_cast badShifts_card_le (G := G) px py pz x y z
  apply (div_le_iff₀ hg).mpr
  linarith

theorem floor_loss_fraction (γ : ℝ) (hγ : 0 ≤ γ) :
    (Nat.floor (3 * γ * Fintype.card G) : ℝ) / Fintype.card G ≤ 3 * γ := by
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hg).mpr
  exact Nat.floor_le (by positivity)

theorem repair_from_orbit_loss
    {K : Type*} [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]
    (Q : Tensor K X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    (γ : ℝ)
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ γ)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ γ)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ γ)
    (L : ℕ) (hL : 0 < L)
    (hbudget : (@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card *
        Nat.floor (3 * γ * Fintype.card G) ^ L < Fintype.card G ^ L) :
    ∃ (a : X → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × X) → K)
      (b : Y → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Y) → K)
      (c : Z → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Z) → K),
      Tensor.restrict a b c (Tensor.directSum
        (fun _ : Finset (Fin L) × Finset (Fin L) × Finset (Fin L) =>
          ExactRecovery.delete Q px py pz)) = Q := by
  classical
  apply ExactRecovery.repair_of_counting (I := G) Q (ExactRecovery.delete Q px py pz)
    (fun g x => px (g • x)) (fun g y => py (g • y)) (fun g z => pz (g • z))
    (fun g x => g • x) (fun g y => g • y) (fun g z => g • z)
    (fun g x y z => by simp [ExactRecovery.delete, hpreserve])
    (Nat.floor (3 * γ * Fintype.card G)) L hL ?_ hbudget
  intro x y z hq
  have heq : (@Finset.filter G
      (fun g => ¬(px (g • x) ∧ py (g • y) ∧ pz (g • z)))
      (Classical.decPred _) Finset.univ) = badShifts (G := G) px py pz x y z := by
    ext g
    simp only [badShifts, Finset.mem_filter]
  rw [heq]
  apply Nat.le_floor
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  exact (div_le_iff₀ hg).mp (badShifts_fraction_le_at (G := G) px py pz γ x y z
    (hx x ⟨y, z, hq⟩) (hy y ⟨x, z, hq⟩) (hz z ⟨x, y, hq⟩))

end MatrixMultiplication.OrbitRecovery

end




section
noncomputable section

namespace MatrixMultiplication.RecoveryGrowth

open Filter
open scoped Topology BigOperators

def shiftCount (b C : ℝ) (N : ℕ) : ℕ :=
  ⌈(b + 1) * (N : ℝ) / Real.log ((N : ℝ) / (3 * C))⌉₊

def replicationCount (b C : ℝ) (N : ℕ) : ℕ :=
  2 ^ (3 * shiftCount b C N)

theorem shiftCount_pos {b C : ℝ} {N : ℕ}
    (hb : 0 ≤ b) (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    0 < shiftCount b C N := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  exact Nat.ceil_pos.2 (div_pos (mul_pos (by linarith) hN0) hlog)

theorem support_loss_bound {b C : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    Real.exp (b * N) * (3 * C / (N : ℝ)) ^ shiftCount b C N ≤
      Real.exp (-(N : ℝ)) := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have hceil : (b + 1) * (N : ℝ) ≤
      (shiftCount b C N : ℝ) * Real.log ((N : ℝ) / (3 * C)) := by
    exact (div_le_iff₀ hlog).1 (Nat.le_ceil _)
  have hbase : 3 * C / (N : ℝ) =
      Real.exp (-Real.log ((N : ℝ) / (3 * C))) := by
    rw [Real.exp_neg, Real.exp_log (div_pos hN0 hC3)]
    simp
  rw [hbase, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem cardinal_budget {b C : ℝ} {N S t g : ℕ}
    (hC : 0 < C) (hN : 3 * C < (N : ℝ)) (hg : 0 < g)
    (hS : (S : ℝ) ≤ Real.exp (b * N))
    (ht : (t : ℝ) / (g : ℝ) ≤ 3 * C / (N : ℝ)) :
    S * t ^ shiftCount b C N < g ^ shiftCount b C N := by
  have hgr : 0 < (g : ℝ) := by exact_mod_cast hg
  have hN0 : 0 < (N : ℝ) := by linarith
  have hpow := pow_le_pow_left₀
    (div_nonneg (Nat.cast_nonneg t) hgr.le) ht (shiftCount b C N)
  have hprob : (S : ℝ) * ((t : ℝ) / (g : ℝ)) ^ shiftCount b C N < 1 := by
    calc
      (S : ℝ) * ((t : ℝ) / (g : ℝ)) ^ shiftCount b C N ≤
          Real.exp (b * N) * (3 * C / (N : ℝ)) ^ shiftCount b C N :=
        mul_le_mul hS hpow (pow_nonneg (div_nonneg (Nat.cast_nonneg t) hgr.le) _)
          (Real.exp_pos _).le
      _ ≤ Real.exp (-(N : ℝ)) := support_loss_bound hC hN
      _ < 1 := by rw [Real.exp_lt_one_iff]; linarith
  rw [div_pow, ← mul_div_assoc] at hprob
  have hreal := (div_lt_iff₀ (pow_pos hgr (shiftCount b C N))).1 hprob
  simp only [one_mul] at hreal
  exact_mod_cast hreal

theorem exists_cover {M G : Type*} [Fintype G] [Nonempty G]
    [DecidableEq G] [DecidableEq M]
    (s : Finset M) (good : G → M → Prop) [∀ g, DecidablePred (good g)]
    {b C : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 * C < (N : ℝ))
    (hs : (s.card : ℝ) ≤ Real.exp (b * N))
    (hbad : ∀ m ∈ s,
      ((Finset.univ.filter fun g => ¬good g m).card : ℝ) / Fintype.card G ≤
        3 * C / (N : ℝ)) :
    ∃ f : Fin (shiftCount b C N) → G, ∀ m ∈ s, ∃ i, good (f i) m := by
  let t := ⌊(3 * C / (N : ℝ)) * Fintype.card G⌋₊
  have hg : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have harg : 0 ≤ (3 * C / (N : ℝ)) * Fintype.card G := by
    exact mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg N)) hg.le
  apply FiniteCover.exists_cover s good t (shiftCount b C N)
  · intro m hm
    exact Nat.le_floor ((div_le_iff₀ hg).1 (hbad m hm))
  · apply cardinal_budget hC hN Fintype.card_pos hs
    exact (div_le_iff₀ hg).2 (Nat.floor_le harg)

theorem shiftCount_div_nat_le {b C : ℝ} {N : ℕ}
    (hb : 0 < b) (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    (shiftCount b C N : ℝ) / (N : ℝ) ≤
      (b + 1) / Real.log ((N : ℝ) / (3 * C)) + 1 / (N : ℝ) := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have harg : 0 ≤ (b + 1) * (N : ℝ) / Real.log ((N : ℝ) / (3 * C)) :=
    div_nonneg (mul_nonneg (by linarith) hN0.le) hlog.le
  have hceil := div_le_div_of_nonneg_right (Nat.ceil_lt_add_one harg).le hN0.le
  change (shiftCount b C N : ℝ) / (N : ℝ) ≤ _ at hceil
  convert hceil using 1
  field_simp [hN0.ne', hlog.ne']

theorem tendsto_shiftCount_div_nat {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun N : ℕ => (shiftCount b C N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / (3 * C))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hnat.atTop_div_const (by linarith))
  have hmain : Tendsto (fun N : ℕ =>
      (b + 1) / Real.log ((N : ℝ) / (3 * C))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have herr : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hmain.add herr)
  · exact Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hnat.eventually_gt_atTop (3 * C)] with N hN
    exact shiftCount_div_nat_le hb hC hN

theorem eventually_shiftCount_div_nat_le_log {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, (shiftCount b C N : ℝ) / (N : ℝ) ≤
      (2 * b + 3) / Real.log (N : ℝ) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlognat := Real.tendsto_log_atTop.comp hnat
  filter_upwards [hnat.eventually_gt_atTop (3 * C), hnat.eventually_gt_atTop 1,
    hlognat.eventually_ge_atTop (2 * Real.log (3 * C))] with N hN hN1 hlarge
  change 2 * Real.log (3 * C) ≤ Real.log (N : ℝ) at hlarge
  have hN0 : 0 < (N : ℝ) := lt_trans zero_lt_one hN1
  have hC3 : 0 < 3 * C := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hden : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have hhalf : Real.log (N : ℝ) ≤ 2 * Real.log ((N : ℝ) / (3 * C)) := by
    rw [Real.log_div hN0.ne' hC3.ne']
    linarith
  have hmain : (b + 1) / Real.log ((N : ℝ) / (3 * C)) ≤
      (2 * (b + 1)) / Real.log (N : ℝ) := by
    apply (div_le_div_iff₀ hden hlog).2
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ b + 1 by linarith)]
  have herr : 1 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) :=
    div_le_div_of_nonneg_left zero_le_one hlog (Real.log_le_self hN0.le)
  calc
    (shiftCount b C N : ℝ) / (N : ℝ) ≤
        (b + 1) / Real.log ((N : ℝ) / (3 * C)) + 1 / (N : ℝ) :=
      shiftCount_div_nat_le hb hC hN
    _ ≤ (2 * (b + 1)) / Real.log (N : ℝ) + 1 / Real.log (N : ℝ) :=
      add_le_add hmain herr
    _ = (2 * b + 3) / Real.log (N : ℝ) := by ring

theorem log_replicationCount (b C : ℝ) (N : ℕ) :
    Real.log (replicationCount b C N : ℝ) =
      (3 * Real.log 2) * (shiftCount b C N : ℝ) := by
  simp only [replicationCount, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem eventually_log_replicationCount_div_nat_le_log {b C : ℝ}
    (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, Real.log (replicationCount b C N : ℝ) / (N : ℝ) ≤
      (3 * Real.log 2 * (2 * b + 3)) / Real.log (N : ℝ) := by
  filter_upwards [eventually_shiftCount_div_nat_le_log hb hC] with N hN
  have hlog2 : 0 ≤ 3 * Real.log 2 :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  simpa only [log_replicationCount, mul_div_assoc] using
    mul_le_mul_of_nonneg_left hN hlog2

theorem tendsto_log_replicationCount_div_nat {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun N : ℕ => Real.log (replicationCount b C N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have h := (tendsto_shiftCount_div_nat hb hC).const_mul (3 * Real.log 2)
  simp only [mul_zero] at h
  convert h using 1
  ext N
  simp only [log_replicationCount]
  ring

theorem eventually_replicationCount_le_exp {b C ε : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (replicationCount b C N : ℝ) ≤ Real.exp (ε * N) := by
  filter_upwards [(tendsto_log_replicationCount_div_nat hb hC).eventually_lt_const hε,
    eventually_gt_atTop (0 : ℕ)] with N hrate hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrep : 0 < (replicationCount b C N : ℝ) := by
    simp only [replicationCount, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_pos (by norm_num) _
  exact (Real.log_le_iff_le_exp hrep).1 ((div_lt_iff₀ hN0).1 hrate).le

theorem tendsto_log_prod_div_nat {J : Type*} (s : Finset J)
    {r : J → ℕ → ℕ}
    (hr : ∀ j ∈ s, ∀ N, 0 < r j N)
    (hlim : ∀ j ∈ s, Tendsto (fun N => Real.log (r j N : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N => Real.log ((∏ j ∈ s, r j N : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum s hlim
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr
  intro N
  rw [Nat.cast_prod, Real.log_prod
    (fun j hj => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hr j hj N)))]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.RecoveryGrowth

end
end




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.InverseLinearRecovery

abbrev MaskRectangles (L : ℕ) := Finset (Fin L) × Finset (Fin L) × Finset (Fin L)

def RecoveredBy {K X Y Z : Type*} [CommSemiring K]
    [Fintype X] [Fintype Y] [Fintype Z]
    (Q H : Tensor K X Y Z) (L : ℕ) : Prop :=
  ∃ (a : X → (MaskRectangles L × X) → K)
    (b : Y → (MaskRectangles L × Y) → K)
    (c : Z → (MaskRectangles L × Z) → K),
    Tensor.restrict a b c (Tensor.directSum (fun _ : MaskRectangles L => H)) = Q

theorem repair_inverse_linear
    {K G X Y Z : Type*} [CommSemiring K] [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (Q : Tensor K X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    {b C : ℝ} {N : ℕ} (hb : 0 ≤ b) (hC : 0 < C) (hN : 3 * C < (N : ℝ))
    (hsupport : ((@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card : ℝ) ≤
      Real.exp (b * N))
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ C / N)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ C / N)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ C / N) :
    RecoveredBy Q (ExactRecovery.delete Q px py pz) (RecoveryGrowth.shiftCount b C N) := by
  classical
  apply OrbitRecovery.repair_from_orbit_loss Q px py pz hpreserve (C / N) hx hy hz
    (RecoveryGrowth.shiftCount b C N) (RecoveryGrowth.shiftCount_pos hb hC hN)
  apply RecoveryGrowth.cardinal_budget hC hN Fintype.card_pos hsupport
  simpa only [mul_div_assoc] using
    OrbitRecovery.floor_loss_fraction (G := G) (C / N)
      (div_nonneg hC.le (Nat.cast_nonneg N))

theorem card_recovery_copies (b C : ℝ) (N : ℕ) :
    Fintype.card (MaskRectangles (RecoveryGrowth.shiftCount b C N)) =
      RecoveryGrowth.replicationCount b C N := by
  simpa only [MaskRectangles, Fintype.card_fin, RecoveryGrowth.replicationCount] using
    (ExactRecovery.card_mask_rectangles (I := Fin (RecoveryGrowth.shiftCount b C N)))

theorem subexponential_copies {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (MaskRectangles (RecoveryGrowth.shiftCount b C N))) / N)
      Filter.atTop (nhds 0) := by
  simp_rw [card_recovery_copies]
  exact RecoveryGrowth.tendsto_log_replicationCount_div_nat hb hC

end MatrixMultiplication.InverseLinearRecovery

end

end MatrixAllFields

end OAI
