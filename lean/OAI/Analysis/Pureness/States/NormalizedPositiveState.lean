import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Linarith

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointFunctionalComplex (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (ℜ a) : ℂ) + Complex.I * (f (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointFunctionalComplex_apply (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointFunctionalComplex f a = (f a : ℂ) := by
  have hr : ℜ (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [selfAdjointFunctionalComplex, hr, a.property.imaginaryPart]

lemma selfAdjointFunctional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hn : ‖f‖ ≤ 1) (h1 : f 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ f a := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖(a : A)‖ := norm_pos_iff.mpr (fun h => hz (Subtype.ext h))
  let b : selfAdjoint A := ‖(a : A)‖⁻¹ • a
  have hb0 : 0 ≤ (b : A) := smul_nonneg (by positivity) ha
  have hbn : ‖(b : A)‖ ≤ 1 := by
    change ‖‖(a : A)‖⁻¹ • (a : A)‖ ≤ 1
    simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hb1 : (b : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn
  have hsub : ‖(1 : selfAdjoint A) - b‖ ≤ 1 := by
    change ‖(1 : A) - (b : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hb1)).mpr
      (sub_le_self _ hb0)
  have hf : ‖f (1 - b)‖ ≤ 1 :=
    (f.le_opNorm _).trans ((mul_le_mul hn hsub (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hfb : 0 ≤ f b := by
    have := le_abs_self (f (1 - b))
    rw [map_sub, h1] at hf this
    change |1 - f b| ≤ 1 at hf
    linarith
  change 0 ≤ f (‖(a : A)‖⁻¹ • a) at hfb
  rw [map_smul, smul_eq_mul] at hfb
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp hfb

theorem exists_normalizedPositiveState [Nontrivial A] :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 := by
  have hn1 : ‖(1 : selfAdjoint A)‖ = 1 := norm_one (α := A)
  obtain ⟨f, hfn, hf1⟩ := exists_dual_vector ℝ (1 : selfAdjoint A) (by rw [hn1]; norm_num)
  have hf1' : f 1 = 1 := by simpa [hn1] using hf1
  let g := selfAdjointFunctionalComplex f.toLinearMap
  have hg : ∀ a : A, 0 ≤ a → 0 ≤ g a := by
    intro a ha
    have h := selfAdjointFunctional_nonneg f hfn.le hf1' ⟨a, .of_nonneg ha⟩ ha
    change 0 ≤ selfAdjointFunctionalComplex f.toLinearMap (⟨a, .of_nonneg ha⟩ : selfAdjoint A)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast h
  refine ⟨{ toLinearMap := g, monotone' := ?_ }, ?_⟩
  · intro a b hab
    change g a ≤ g b
    have := hg (b - a) (sub_nonneg.mpr hab)
    simpa only [map_sub, sub_nonneg] using this
  · change selfAdjointFunctionalComplex f.toLinearMap ((1 : selfAdjoint A) : A) = 1
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast hf1'
end CuntzPureness

end

end OAI
