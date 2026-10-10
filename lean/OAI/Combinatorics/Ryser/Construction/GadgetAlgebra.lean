import OAI.Combinatorics.Ryser.Geometry.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

def cubeMap (p : Point F) : Point F := (p.1 ^ 3, p.2)

def cubicPoint (d z x : F) : Point F := (x ^ 3, d * x + z)

theorem cubicPoint_injective (d z : F) (hd : d ≠ 0) :
    Function.Injective (cubicPoint d z) := by
  intro x y h
  exact mul_left_cancel₀ hd (add_right_cancel (congrArg Prod.snd h))

variable [instFintypeF : Fintype F]

theorem cube_bijective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Bijective (fun x : F => x ^ 3) := by
  classical
  have hU : (Nat.card Fˣ).Coprime 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact h.symm
  have hpow : Function.Bijective (fun u : Fˣ => u ^ 3) :=
    Nat.Coprime.pow_left_bijective hU
  apply Function.Surjective.bijective_of_finite
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp⟩
  · obtain ⟨u, hu⟩ := hpow.surjective (Units.mk0 y hy)
    refine ⟨(u : F), ?_⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
      congrArg (fun v : Fˣ => (v : F)) hu

theorem cubeMap_bijective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Bijective (cubeMap : Point F → Point F) := by
  have hc := cube_bijective h
  constructor
  · intro p q hpq
    have hx := congrArg (fun r : Point F => r.1) hpq
    have hy := congrArg (fun r : Point F => r.2) hpq
    exact Prod.ext (hc.injective hx) hy
  · rintro ⟨x, y⟩
    obtain ⟨z, hz⟩ := hc.surjective x
    exact ⟨(z, y), Prod.ext hz rfl⟩

theorem cubeMap_vertical_iff (h : Nat.Coprime 3 (Fintype.card F - 1))
    (p : Point F) (b : F) :
    Incidence (cubeMap p) (none, b ^ 3) ↔ Incidence p (none, b) := by
  change p.1 ^ 3 = b ^ 3 ↔ p.1 = b
  constructor
  · intro hp
    exact (cube_bijective h).injective hp
  · intro hp
    rw [hp]

theorem cubeMap_horizontal_iff (p : Point F) (b : F) :
    Incidence (cubeMap p) (some 0, b) ↔ Incidence p (some 0, b) := let _ := instFintypeF; by
  change p.2 - 0 * p.1 ^ 3 = b ↔ p.2 - 0 * p.1 = b
  simp

variable [instDecidableEqF : DecidableEq F]

def cubicShape (d z : F) : Finset (Point F) :=
  Finset.univ.image (cubicPoint d z)

@[simp] theorem mem_cubicShape {d z : F} {p : Point F} :
    p ∈ cubicShape d z ↔ ∃ x, cubicPoint d z x = p := by
  simp [cubicShape]

theorem cubicShape_card (d z : F) (hd : d ≠ 0) :
    (cubicShape d z).card = Fintype.card F := by
  rw [cubicShape, Finset.card_image_of_injective _ (cubicPoint_injective d z hd),
    Finset.card_univ]

theorem cubicShape_eq_image_linePoints (d z : F) :
    cubicShape d z = (linePoints (some d, z)).image cubeMap := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := mem_cubicShape.mp hp
    refine Finset.mem_image.mpr ⟨(x, d * x + z), ?_, rfl⟩
    apply (mem_linePoints _ _).mpr
    change d * x + z - d * x = z
    ring
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine mem_cubicShape.mpr ⟨q.1, ?_⟩
    apply Prod.ext
    · rfl
    · have hq' : q.2 - d * q.1 = z := (mem_linePoints _ _).mp hq
      change d * q.1 + z = q.2
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hq').symm

theorem cubeMap_image_vertical (h : Nat.Coprime 3 (Fintype.card F - 1)) (b : F) :
    (linePoints (none, b)).image cubeMap = linePoints (none, b ^ 3) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_linePoints _ _).mpr ((cubeMap_vertical_iff h q b).2
      ((mem_linePoints _ _).mp hq))
  · intro hp
    obtain ⟨q, rfl⟩ := (cubeMap_bijective h).surjective p
    exact Finset.mem_image.mpr
      ⟨q, (mem_linePoints _ _).mpr ((cubeMap_vertical_iff h q b).1
        ((mem_linePoints _ _).mp hp)), rfl⟩

theorem cubeMap_image_horizontal (h : Nat.Coprime 3 (Fintype.card F - 1)) (b : F) :
    (linePoints (some 0, b)).image cubeMap = linePoints (some 0, b) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_linePoints _ _).mpr ((cubeMap_horizontal_iff q b).2
      ((mem_linePoints _ _).mp hq))
  · intro hp
    obtain ⟨q, rfl⟩ := (cubeMap_bijective h).surjective p
    exact Finset.mem_image.mpr
      ⟨q, (mem_linePoints _ _).mpr ((cubeMap_horizontal_iff q b).1
        ((mem_linePoints _ _).mp hp)), rfl⟩

open Polynomial

def cubicLinePolynomial (d z : F) : AffineLine F → F[X]
  | (none, b) => X ^ 3 - C b
  | (some m, b) => C d * X + C z - C m * X ^ 3 - C b

theorem eval_cubicLinePolynomial_eq_zero_iff (d z : F) (l : AffineLine F) (x : F) :
    (cubicLinePolynomial d z l).eval x = 0 ↔ Incidence (cubicPoint d z x) l := let _ := instFintypeF; let _ := instDecidableEqF; by
  obtain ⟨a, b⟩ := l
  cases a <;>
    simp [cubicLinePolynomial, cubicPoint, Incidence, projection, sub_eq_zero]

theorem cubicLinePolynomial_ne_zero (d z : F) (hd : d ≠ 0) (l : AffineLine F) :
    cubicLinePolynomial d z l ≠ 0 := let _ := instFintypeF; let _ := instDecidableEqF; by
  obtain ⟨a, b⟩ := l
  cases a with
  | none =>
      intro hp
      have hc := congrArg (fun p : F[X] => p.coeff 3) hp
      exact (one_ne_zero : (1 : F) ≠ 0)
        (by simp [cubicLinePolynomial, coeff_X_pow] at hc)
  | some m =>
      intro hp
      have hc := congrArg (fun p : F[X] => p.coeff 1) hp
      exact hd (by simpa [cubicLinePolynomial, coeff_X_pow] using hc)

theorem cubicLinePolynomial_natDegree_le (d z : F) (l : AffineLine F) :
    (cubicLinePolynomial d z l).natDegree ≤ 3 := let _ := instFintypeF; let _ := instDecidableEqF; by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn3 : n ≠ 3 := by omega
  obtain ⟨a, b⟩ := l
  cases a <;>
    simp [cubicLinePolynomial, coeff_X_pow, coeff_C, coeff_X,
      hn0, Ne.symm hn1, hn3]

theorem cubicShape_filter_incidence_card_le (d z : F) (hd : d ≠ 0)
    (l : AffineLine F) :
    ((cubicShape d z).filter (fun p => Incidence p l)).card ≤ 3 := by
  have hcount :
      (Finset.univ.filter (fun x => Incidence (cubicPoint d z x) l)).card ≤
        (cubicLinePolynomial d z l).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    exact (Polynomial.mem_roots (cubicLinePolynomial_ne_zero d z hd l)).2
      ((eval_cubicLinePolynomial_eq_zero_iff d z l x).2 (Finset.mem_filter.mp hx).2)
  rw [cubicShape, Finset.filter_image]
  exact (Finset.card_image_le.trans hcount).trans (cubicLinePolynomial_natDegree_le d z l)

theorem cubicShape_inter_linePoints_card_le (d z : F) (hd : d ≠ 0)
    (l : AffineLine F) :
    (cubicShape d z ∩ linePoints l).card ≤ 3 := by
  have heq : cubicShape d z ∩ linePoints l =
      (cubicShape d z).filter (fun p => Incidence p l) := by
    ext p
    simp
  rw [heq]
  exact cubicShape_filter_incidence_card_le d z hd l

theorem cubicShape_ne_linePoints (d z : F) (hd : d ≠ 0)
    (hcard : 3 < Fintype.card F) (l : AffineLine F) :
    cubicShape d z ≠ linePoints l := by
  intro heq
  have hall : (cubicShape d z).filter (fun p => Incidence p l) = cubicShape d z := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact (mem_linePoints _ _).mp (heq ▸ hp)
  have hle := cubicShape_filter_incidence_card_le d z hd l
  rw [hall, cubicShape_card d z hd] at hle
  exact (not_le_of_gt hcard) hle

theorem cubicShape_injective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Injective (fun dz : F × F => cubicShape dz.1 dz.2) := by
  intro a b hab
  change cubicShape a.1 a.2 = cubicShape b.1 b.2 at hab
  have heval : ∀ x, a.1 * x + a.2 = b.1 * x + b.2 := by
    intro x
    have hm : cubicPoint a.1 a.2 x ∈ cubicShape b.1 b.2 := by
      rw [← hab]
      exact mem_cubicShape.mpr ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := mem_cubicShape.mp hm
    have hyx : y = x := (cube_bijective h).injective (congrArg Prod.fst hy)
    subst y
    exact (congrArg Prod.snd hy).symm
  have hz : a.2 = b.2 := by simpa using heval 0
  have hd : a.1 = b.1 := by
    have h1 := heval 1
    simp only [mul_one] at h1
    rw [hz] at h1
    exact add_right_cancel h1
  exact Prod.ext hd hz

theorem cubicShape_intercept_unique (h : Nat.Coprime 3 (Fintype.card F - 1))
    (d : F) (p : Point F) : ∃! z, p ∈ cubicShape d z := by
  obtain ⟨x, hx⟩ := (cube_bijective h).surjective p.1
  refine ⟨p.2 - d * x, ?_, ?_⟩
  · refine mem_cubicShape.mpr ⟨x, ?_⟩
    apply Prod.ext
    · exact hx
    · change d * x + (p.2 - d * x) = p.2
      ring
  · intro z hz
    obtain ⟨y, hy⟩ := mem_cubicShape.mp hz
    have hyx : y = x :=
      (cube_bijective h).injective ((congrArg Prod.fst hy).trans hx.symm)
    subst y
    apply eq_sub_iff_add_eq.mpr
    simpa [cubicPoint, add_comm] using congrArg Prod.snd hy

theorem cubicShape_intercept_card (h : Nat.Coprime 3 (Fintype.card F - 1))
    (d : F) (p : Point F) :
    (Finset.univ.filter (fun z => p ∈ cubicShape d z)).card = 1 := by
  obtain ⟨z, hz, hu⟩ := cubicShape_intercept_unique h d p
  apply Finset.card_eq_one.mpr
  refine ⟨z, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨hu w, fun hw => hw ▸ hz⟩

theorem coprime_three_zmod_card_sub_one {p : ℕ} [Fact p.Prime] (hpmod : p % 3 = 2) :
    Nat.Coprime 3 (Fintype.card (ZMod p) - 1) := by
  rw [ZMod.card]
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

theorem cube_bijective_zmod {p : ℕ} [Fact p.Prime] (hpmod : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) :=
  cube_bijective (coprime_three_zmod_card_sub_one hpmod)

theorem cubeMap_bijective_zmod {p : ℕ} [Fact p.Prime] (hpmod : p % 3 = 2) :
    Function.Bijective (cubeMap : Point (ZMod p) → Point (ZMod p)) :=
  cubeMap_bijective (coprime_three_zmod_card_sub_one hpmod)

end RyserCoveringCounterexample.Construction

end

end OAI
