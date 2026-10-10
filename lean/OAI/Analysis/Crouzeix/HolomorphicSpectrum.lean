import Mathlib
import OAI.Analysis.Crouzeix.HolomorphicAlgebra

namespace OAI

/-! Holomorphic Spectrum. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

variable (A : Operator H)

lemma holomorphicEval_congr {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (he : EqOn f g U) :
    holomorphicEval A U f = holomorphicEval A U g := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU hf Γ, holomorphicEval_eq_contourEval A hU hg Γ]
  apply contourEval_congr
  rintro z ⟨t,ht,rfl⟩
  exact he (Γ.avoids t ht).1

lemma isUnit_holomorphicEval {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hn : ∀ z ∈ numericalClosure A, f z ≠ 0) :
    IsUnit (holomorphicEval A U f) := by
  let V := U ∩ {z | f z ≠ 0}
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isOpen_ne
  have hKV : numericalClosure A ⊆ V := fun z hz => ⟨hKU hz,hn z hz⟩
  have hfV := hf.mono (show V ⊆ U from inter_subset_left)
  have hi : DifferentiableOn ℂ (fun z => (f z)⁻¹) V := hfV.inv (fun z hz => hz.2)
  rw [← holomorphicEval_restrict A hV hU hKV inter_subset_left hf]
  refine (isUnit_iff_exists).mpr ⟨holomorphicEval A V (fun z => (f z)⁻¹), ?_, ?_⟩
  · rw [← holomorphicEval_mul A hV hKV hfV hi,
      holomorphicEval_congr A hV hKV (hfV.fun_mul hi) (differentiableOn_const (1 : ℂ))
        (fun z hz => mul_inv_cancel₀ hz.2), holomorphicEval_const A hV hKV, map_one]
  · rw [← holomorphicEval_mul A hV hKV hi hfV,
      holomorphicEval_congr A hV hKV (hi.fun_mul hfV) (differentiableOn_const (1 : ℂ))
        (fun z hz => inv_mul_cancel₀ hz.2), holomorphicEval_const A hV hKV, map_one]

lemma spectrum_holomorphicEval_subset {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    spectrum ℂ (holomorphicEval A U f) ⊆ f '' numericalClosure A := by
  intro z hz
  by_contra hn
  have hnz : ∀ w ∈ numericalClosure A, z + (-1 : ℂ) * f w ≠ 0 := by
    intro w hw he
    apply hn
    refine ⟨w,hw,?_⟩
    linear_combination -he
  have hd := (differentiableOn_const (c := z)).fun_add (hf.const_mul (-1))
  have hu := isUnit_holomorphicEval A hU hKU hd hnz
  rw [holomorphicEval_add A hU hKU (differentiableOn_const z) (hf.const_mul (-1)),
    holomorphicEval_const A hU hKU, holomorphicEval_smul A hU hKU hf] at hu
  simp only [neg_one_smul, ← sub_eq_add_neg] at hu
  exact (spectrum.mem_iff.mp hz) hu

lemma spectralRadius_holomorphicEval_lt_one {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hfK : ∀ z ∈ numericalClosure A, ‖f z‖ < 1) :
    spectralRadius ℂ (holomorphicEval A U f) < 1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro z hz
  obtain ⟨w,hw,rfl⟩ := spectrum_holomorphicEval_subset A hU hKU hf hz
  exact hfK w hw

lemma holomorphicEval_polynomial_comp {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (p : Polynomial ℂ) :
    holomorphicEval A U (fun z => p.eval (f z)) = Polynomial.aeval (holomorphicEval A U f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [holomorphicEval_add A hU hKU
      (show DifferentiableOn ℂ (fun z => p.eval (f z)) U from p.differentiable.comp_differentiableOn hf)
      (show DifferentiableOn ℂ (fun z => q.eval (f z)) U from q.differentiable.comp_differentiableOn hf), hp, hq]
  | monomial n c =>
    have hpow : holomorphicEval A U (fun z => f z ^ n) = holomorphicEval A U f ^ n := by
      induction n with
      | zero => simpa only [pow_zero, map_one] using holomorphicEval_const A hU hKU (1 : ℂ)
      | succ n ih =>
        simp_rw [pow_succ]
        rw [holomorphicEval_mul A hU hKU (f := fun z => f z^n) (hf.pow n) hf, ih]
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [holomorphicEval_smul A hU hKU (f := fun z => f z^n) (hf.pow n), hpow, Algebra.smul_def]

end CrouzeixHilbert

end

end OAI
