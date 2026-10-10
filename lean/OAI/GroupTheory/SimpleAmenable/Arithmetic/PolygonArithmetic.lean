import Mathlib

namespace OAI

section

section
open scoped symmDiff

namespace SimpleAmenable

section PolygonArithmetic

abbrev CutRing := QuadraticAlgebra ℤ 1 1

noncomputable def ordinary : CutRing →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.goldenRatio, by
    simp only [one_smul, ← sq]
    linarith [Real.goldenRatio_sq]⟩

noncomputable def conjugate : CutRing →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.goldenConj, by
    simp only [one_smul, ← sq]
    linarith [Real.goldenConj_sq]⟩

theorem ordinary_apply (z : CutRing) :
    ordinary z = (z.re : ℝ) + (z.im : ℝ) * Real.goldenRatio := by
  simp [ordinary, QuadraticAlgebra.lift]

theorem conjugate_apply (z : CutRing) :
    conjugate z = (z.re : ℝ) + (z.im : ℝ) * Real.goldenConj := by
  simp [conjugate, QuadraticAlgebra.lift]

private theorem golden_coefficients_unique {p q : ℤ}
    (h : (p : ℝ) + (q : ℝ) * Real.goldenRatio = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    have hir := (Real.goldenRatio_irrational.intCast_mul hq).intCast_add p
    exact hir.ne_int 0 (by simpa using h)
  exact ⟨by simpa [hq] using h, hq⟩

theorem ordinary_injective : Function.Injective ordinary := by
  intro x y h
  have hz : ordinary (x - y) = 0 := by simp [h]
  obtain ⟨hre, him⟩ := golden_coefficients_unique ((ordinary_apply (x - y)).symm.trans hz)
  apply QuadraticAlgebra.ext
  · exact sub_eq_zero.mp hre
  · exact sub_eq_zero.mp him

theorem conjugate_eq_ordinary_star (z : CutRing) : conjugate z = ordinary (star z) := by
  simp only [conjugate_apply, ordinary_apply, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star, Int.cast_add, Int.cast_neg, one_mul]
  rw [← Real.one_sub_goldenConj]
  ring

theorem conjugate_injective : Function.Injective conjugate := by
  intro x y h
  have : star x = star y := ordinary_injective (by simpa only [conjugate_eq_ordinary_star] using h)
  simpa using congrArg star this

theorem cut_norm_identity (z : CutRing) :
    ordinary z * conjugate z = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  rw [conjugate_eq_ordinary_star, ← map_mul,
    ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp

theorem cut_norm_nonzero {z : CutRing} (hz : z ≠ 0) : QuadraticAlgebra.norm z ≠ 0 := by
  intro h
  have hx : ordinary z ≠ 0 := by simpa using ordinary_injective.ne hz
  have hy : conjugate z ≠ 0 := by simpa using conjugate_injective.ne hz
  exact mul_ne_zero hx hy (by simp [cut_norm_identity, h])

theorem one_le_abs_cut_norm {z : CutRing} (hz : z ≠ 0) :
    1 ≤ |ordinary z * conjugate z| := by
  rw [cut_norm_identity, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (cut_norm_nonzero hz)

def endpointLabel (z : CutRing) : ℤ := z.im

theorem endpointLabel_embedding (z : CutRing) :
    (endpointLabel z : ℝ) = (ordinary z - conjugate z) / Real.sqrt 5 := by
  have hs : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply (eq_div_iff hs).mpr
  simp only [ordinary_apply, conjugate_apply, endpointLabel]
  rw [← Real.goldenRatio_sub_goldenConj]
  ring

noncomputable abbrev cutTau : CutRing := QuadraticAlgebra.omega

@[simp] theorem ordinary_cutTau : ordinary cutTau = Real.goldenRatio := by simp [cutTau, ordinary_apply]
@[simp] theorem conjugate_cutTau : conjugate cutTau = Real.goldenConj := by simp [cutTau, conjugate_apply]

theorem cutTau_isUnit : IsUnit cutTau := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  norm_num [cutTau, QuadraticAlgebra.norm_def]

noncomputable def cutForm (a : ℕ) (j : Fin 4) (p : ℝ × ℝ) : ℝ :=
  ![p.1, p.2, p.2 - Real.goldenRatio ^ a * p.1,
    p.1 - Real.goldenRatio ^ a * p.2] j

noncomputable def integralCutForm (a : ℕ) (j : Fin 4) (p : CutRing × CutRing) : CutRing :=
  ![p.1, p.2, p.2 - cutTau ^ a * p.1, p.1 - cutTau ^ a * p.2] j

theorem cutForm_ordinary (a : ℕ) (j : Fin 4) (p : CutRing × CutRing) :
    cutForm a j (ordinary p.1, ordinary p.2) = ordinary (integralCutForm a j p) := by
  fin_cases j <;> simp [cutForm, integralCutForm]

theorem cutForm_add (a : ℕ) (j : Fin 4) (p q : ℝ × ℝ) :
    cutForm a j (p + q) = cutForm a j p + cutForm a j q := by
  fin_cases j <;> simp [cutForm] <;> ring

def AvoidsCuts (a : ℕ) (p : ℝ × ℝ) : Prop :=
  ∀ (j : Fin 4) (z : CutRing), cutForm a j p ≠ ordinary z

theorem avoidsCuts_translate {a : ℕ} {p : ℝ × ℝ} (hp : AvoidsCuts a p)
    (u : CutRing × CutRing) : AvoidsCuts a (p + (ordinary u.1, ordinary u.2)) := by
  intro j z hz
  apply hp j (z - integralCutForm a j u)
  rw [cutForm_add, cutForm_ordinary] at hz
  simpa only [map_sub] using eq_sub_of_add_eq hz

def GenericSquare (a : ℕ) :=
  {p : ℝ × ℝ // p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ AvoidsCuts a p}

def halfPlane (a : ℕ) (j : Fin 4) (z : CutRing) : Set (GenericSquare a) :=
  {p | cutForm a j p.val < ordinary z}

def polygonAlgebra (a : ℕ) : BooleanSubalgebra (Set (GenericSquare a)) :=
  BooleanSubalgebra.closure {U | ∃ j z, U = halfPlane a j z}

theorem polygon_induction {a : ℕ} {P : Set (GenericSquare a) → Prop}
    (hcut : ∀ j z, P (halfPlane a j z)) (hbot : P ∅)
    (hsup : ∀ U V, P U → P V → P (U ∪ V))
    (hcompl : ∀ U, P U → P Uᶜ) {U : Set (GenericSquare a)}
    (hU : U ∈ polygonAlgebra a) : P U := by
  induction hU using BooleanSubalgebra.closure_bot_sup_induction with
  | mem U h => obtain ⟨j, z, rfl⟩ := h; exact hcut j z
  | bot => exact hbot
  | sup U hU V hV ihU ihV => exact hsup U V ihU ihV
  | compl U hU ih => exact hcompl U ih

end PolygonArithmetic

end SimpleAmenable
end
end

end OAI
