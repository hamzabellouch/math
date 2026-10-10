import Mathlib
import OAI.NumberTheory.CubicGram.Definitions

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
lemma omega_eq : omega = (-1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I / 3 =
      ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [omega, harg, Complex.exp_mul_I]
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hcos, hsin]
  push_cast
  ring

@[simp] lemma omega_re : omega.re = -1 / 2 := by rw [omega_eq]; simp
@[simp] lemma omega_im : omega.im = Real.sqrt 3 / 2 := by rw [omega_eq]; simp

lemma omega_quadratic : omega ^ 2 + omega + 1 = 0 := by
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
  · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · ring

lemma exists_coordinates (z : Eisenstein) : ∃ a b : ℤ, (z : ℂ) = a + b * omega := by
  refine Algebra.adjoin_induction (p := fun z _ => ∃ a b : ℤ, z = a + b * omega)
    ?_ ?_ ?_ ?_ z.property
  · intro x hx
    obtain rfl : x = omega := Set.mem_singleton_iff.mp hx
    exact ⟨0, 1, by simp⟩
  · intro a
    exact ⟨a, 0, by simp⟩
  · rintro x y _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a+c,b+d,?_⟩
    push_cast
    ring
  · rintro x y _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a*c-b*d, a*d+b*c-b*d, ?_⟩
    have h : omega ^ 2 = -omega - 1 := by linear_combination omega_quadratic
    push_cast
    ring_nf
    rw [h]
    ring

lemma coordinates_norm (a b : ℤ) :
    Complex.normSq ((a : ℂ) + b * omega) = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, omega_re, omega_im]
  push_cast
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma coordinates_unique {a b c d : ℤ}
    (h : (a : ℂ) + b * omega = (c : ℂ) + d * omega) : a = c ∧ b = d := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, omega_im, omega_re, zero_mul, add_zero, zero_add] at him
  have hs : (Real.sqrt 3 / 2 : ℝ) ≠ 0 := by positivity
  have hb : b = d := by
    exact_mod_cast mul_right_cancel₀ hs him
  subst d
  have ha : (a : ℂ) = c := add_right_cancel h
  exact ⟨by exact_mod_cast ha, rfl⟩

lemma norm_nonneg (z : Eisenstein) : 0 ≤ norm z := Complex.normSq_nonneg _

lemma normNat_cast (z : Eisenstein) : (normNat z : ℝ) = norm z := by
  obtain ⟨a,b,hz⟩ := exists_coordinates z
  have hn : norm z = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
    rw [norm, hz, coordinates_norm]
  have hm : 0 ≤ a ^ 2 - a * b + b ^ 2 := by exact_mod_cast hn ▸ norm_nonneg z
  have hn' : norm z = ((a ^ 2 - a * b + b ^ 2).toNat : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm, hn]
  rw [normNat, hn', Nat.floor_natCast]

def ofCoords (a b : ℤ) : Eisenstein := a + b * omegaE

@[simp] lemma ofCoords_coe (a b : ℤ) : (ofCoords a b : ℂ) = a + b * omega := rfl

lemma ofCoords_surjective : Function.Surjective (fun p : ℤ × ℤ => ofCoords p.1 p.2) := by
  intro z
  obtain ⟨a,b,h⟩ := exists_coordinates z
  exact ⟨(a,b), Subtype.ext h.symm⟩

lemma ofCoords_injective : Function.Injective (fun p : ℤ × ℤ => ofCoords p.1 p.2) := by
  intro ⟨a,b⟩ ⟨c,d⟩ h
  have hh := coordinates_unique (congrArg (fun z : Eisenstein => (z : ℂ)) h)
  exact Prod.ext hh.1 hh.2

lemma finite_norm_le (X : ℝ) : Set.Finite {z : Eisenstein | norm z ≤ X} := by
  let C : ℤ := ⌈2 * X + 1⌉
  have hC : 2 * X + 1 ≤ (C : ℝ) := Int.le_ceil _
  apply ((Set.finite_Icc (-C) C).prod (Set.finite_Icc (-C) C)).image
    (fun p : ℤ × ℤ => ofCoords p.1 p.2) |>.subset
  intro z hz
  obtain ⟨a,b,hz'⟩ := exists_coordinates z
  have hn : (a : ℝ)^2 - a*b + b^2 ≤ X := by
    have hh : norm z = ((a ^ 2 - a*b + b^2 : ℤ) : ℝ) := by
      rw [norm, hz', coordinates_norm]
    change norm z ≤ X at hz
    rw [hh] at hz
    exact_mod_cast hz
  have ha : -(C : ℝ) ≤ (a : ℝ) ∧ (a : ℝ) ≤ C := by
    constructor <;> nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg (b : ℝ),
      sq_nonneg ((a : ℝ) - 1), sq_nonneg ((a : ℝ) + 1)]
  have hb : -(C : ℝ) ≤ (b : ℝ) ∧ (b : ℝ) ≤ C := by
    constructor <;> nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg (a : ℝ),
      sq_nonneg ((b : ℝ) - 1), sq_nonneg ((b : ℝ) + 1)]
  refine ⟨(a,b), ?_, Subtype.ext hz'.symm⟩
  constructor
  · exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  · exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩

def primeCutoff (X : ℝ) : Finset Eisenstein :=
  ((finite_norm_le X).subset
    (show {p | primaryPrime p ∧ norm p ≤ X} ⊆ {p | norm p ≤ X} from
      fun _ h => h.2)).toFinset

@[simp] lemma mem_primeCutoff {p : Eisenstein} {X : ℝ} :
    p ∈ primeCutoff X ↔ primaryPrime p ∧ norm p ≤ X := Set.Finite.mem_toFinset _

lemma primeCutoffSum_eq_sum (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum f X = ∑ p ∈ primeCutoff X, f p := by
  unfold primeCutoffSum
  rw [tsum_eq_sum (s := primeCutoff X)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [mem_primeCutoff.mp hp]
  · intro p hp
    simp only [mem_primeCutoff] at hp
    simp [hp]

end CubicFirstMoment
end
end

end OAI
