import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Quadratic ingredients for contingency-table transport

The quadratic-form version of the one-positive-direction property and
the scalar telescoping step give the balanced-pair transport argument in
both contingency-table sampling and counting papers.
-/

namespace ContingencyTables

open Finset
open LinearMap (BilinForm)

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A symmetric form is nonpositive on the form-orthogonal complement
of every vector of positive square. This is the quadratic formulation
of positive inertia at most one. -/
def OnePositiveDirection (B : BilinForm ℝ V) : Prop :=
  ∀ u, 0 < B u u → ∀ v, B u v = 0 → B v v ≤ 0

/-- Nonpositivity on the kernel of one linear functional suffices for
the quadratic signature needed in the manuscripts. -/
theorem onePositiveDirection_of_kernel (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (ℓ : V →ₗ[ℝ] ℝ)
    (hker : ∀ v, ℓ v = 0 → B v v ≤ 0) : OnePositiveDirection B := by
  intro u hu v huv
  have hlu : ℓ u ≠ 0 := by
    intro h
    exact (not_le_of_gt hu) (hker u h)
  let a : ℝ := ℓ v / ℓ u
  have hw : ℓ (v - a • u) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, a]
    field_simp
    ring
  have hq := hker (v - a • u) hw
  have hvu : B v u = 0 := by rw [hsymm, huv]
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    huv, hvu, mul_zero, sub_zero, zero_sub] at hq
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith

/-- The projection inequality (200-01, equation positive-projection;
200-02, equation signature-projection). -/
theorem positive_projection (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (hsig : OnePositiveDirection B)
    (u v : V) (hu : 0 < B u u) :
    B v v ≤ (B u v) ^ 2 / B u u := by
  let a : ℝ := B u v / B u u
  have hzero : B u (v - a • u) = 0 := by
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, a]
    field_simp
    ring
  have hw := hsig u hu (v - a • u) hzero
  have hvu : B v u = B u v := hsymm v u
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hvu] at hw
  apply (le_div_iff₀ hu).2
  dsimp [a] at hw
  field_simp at hw
  nlinarith

/-- The rank-one-minus-squares decomposition used for laminar factors
implies the required signature. This theorem only requires the concrete
decomposition on quadratic evaluations. -/
theorem onePositiveDirection_of_rankOne_sub_squares {G : Type*} [Fintype G]
    (B : BilinForm ℝ V) (hsymm : ∀ x y, B x y = B y x)
    (ℓ : V →ₗ[ℝ] ℝ) (L : G → V →ₗ[ℝ] ℝ) (a : G → ℝ)
    (ha : ∀ g, 0 ≤ a g)
    (hdecomp : ∀ v, B v v = (ℓ v) ^ 2 - ∑ g, a g * (L g v) ^ 2) :
    OnePositiveDirection B := by
  apply onePositiveDirection_of_kernel B hsymm ℓ
  intro v hv
  rw [hdecomp, hv, zero_pow (by decide : 2 ≠ 0), zero_sub]
  exact neg_nonpos.mpr (sum_nonneg fun g _ => mul_nonneg (ha g) (sq_nonneg _))

end Forms

/-- Exact scalar expansion behind the balanced-pair telescoping
inequality. The two mixed entries are expressed as discrete differences
of the cumulative coefficients. -/
theorem pair_expansion (v um u up gm g gp : ℝ) :
    v + 2 * g * ((u * g - um * gm) - (up * gp - u * g)) +
        (um - 2 * u + up) * g ^ 2 -
        (um * (g - gm) ^ 2 + up * (g - gp) ^ 2) =
      v + 2 * u * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 := by
  ring

/-- Once the local projection estimate is available, the exact
expansion gives equation pair-one in 200-01 and integer-telescoping
in 200-02. The hypothesis is a local quadratic estimate, not a claim
that the whole manuscript has been proved. -/
theorem pair_telescoping_step (v um u up gm g gp : ℝ)
    (hprojection :
      v + 2 * g * ((u * g - um * gm) - (up * gp - u * g)) +
          (um - 2 * u + up) * g ^ 2 ≤
        um * (g - gm) ^ 2 + up * (g - gp) ^ 2) :
    2 * u * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 ≤ -v := by
  have h := sub_nonpos.mpr hprojection
  rw [pair_expansion] at h
  linarith

section PairProjection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The local inequality follows from the signature even when either or
both of the fresh diagonal entries vanish. This includes the capacity-two
boundary case in both manuscripts. -/
theorem pair_step_of_signature (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (hsig : OnePositiveDirection B)
    (h ea eb : V) (um u up gm g gp : ℝ)
    (haa : B ea ea = um) (hbb : B eb eb = up) (hab : B ea eb = u)
    (hha : B h ea = u * g - um * gm)
    (hhb : B h eb = up * gp - u * g)
    (hum : 0 ≤ um) (hup : 0 ≤ up)
    (hpositive : 0 < um ∨ 0 < up ∨ (um = 0 ∧ up = 0 ∧ 0 < u)) :
    2 * u * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 ≤ -B h h := by
  let v := h + g • ea - g • eb
  have hba : B eb ea = u := by rw [hsymm, hab]
  have hv_a : B v ea = um * (g - gm) := by
    dsimp [v]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, haa, hba, hha]
    ring
  have hv_b : B v eb = up * (gp - g) := by
    dsimp [v]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hab, hbb, hhb]
    ring
  have hvv : B v v = B h h +
      2 * g * ((u * g - um * gm) - (up * gp - u * g)) +
      (um - 2 * u + up) * g ^ 2 := by
    have hah : B ea h = u * g - um * gm := by rw [hsymm, hha]
    have hbh : B eb h = up * gp - u * g := by rw [hsymm, hhb]
    dsimp [v]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      haa, hbb, hab, hba, hha, hhb, hah, hbh]
    ring
  have hbound : B v v ≤ um * (g - gm) ^ 2 + up * (g - gp) ^ 2 := by
    rcases hpositive with ha | hb | ⟨ha, hb, hu⟩
    · have hh := positive_projection B hsymm hsig ea v (by rwa [haa])
      rw [hsymm ea v, hv_a, haa] at hh
      have heq : (um * (g - gm)) ^ 2 / um = um * (g - gm) ^ 2 := by
        field_simp
      rw [heq] at hh
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hup (sq_nonneg _)))
    · have hh := positive_projection B hsymm hsig eb v (by rwa [hbb])
      rw [hsymm eb v, hv_b, hbb] at hh
      have heq : (up * (gp - g)) ^ 2 / up = up * (g - gp) ^ 2 := by
        field_simp
        ring
      rw [heq] at hh
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg hum (sq_nonneg _)))
    · have hsum : B (ea + eb) (ea + eb) = 2 * u := by
        simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          haa, hbb, hab, hba, ha, hb]
        ring
      have horth : B (ea + eb) v = 0 := by
        rw [hsymm, LinearMap.BilinForm.add_right, hv_a, hv_b, ha, hb]
        ring
      have hh := hsig (ea + eb) (by rw [hsum]; linarith) v horth
      simpa only [ha, hb, zero_mul, zero_add] using hh
  rw [hvv] at hbound
  exact pair_telescoping_step _ _ _ _ _ _ _ hbound

end PairProjection

/-- The scalar second differences telescope with their actual boundary
terms. No absent endpoint matrix is needed. -/
theorem sum_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, (2 * a (j + 1) - a j - a (j + 2))) =
      a 1 - a 0 + a n - a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

/-- The endpoint convention in the unweighted balanced-pair summation
makes the scalar second differences have zero total. -/
theorem sum_second_differences_zero (a : ℕ → ℝ) (n : ℕ)
    (h0 : a 0 = 0) (h1 : a 1 = 0) (hn : a n = 0) (hn1 : a (n + 1) = 0) :
    (∑ j ∈ range n, (2 * a (j + 1) - a j - a (j + 2))) = 0 := by
  rw [sum_second_differences, h0, h1, hn, hn1]
  ring

end ContingencyTables

end OAI
