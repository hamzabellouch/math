import OAI.Analysis.Naimark.States

namespace OAI

/-! Positive scalar functionals on unital self-adjoint linear subspaces.
The extension uses real Hahn–Banach on the self-adjoint part. -/

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def operatorSystemRealPart (S : Submodule ℂ A) : Submodule ℝ A :=
  S.restrictScalars ℝ ⊓ selfAdjoint.submodule ℝ A

def operatorSystemRealInclusion (S : Submodule ℂ A) :
    operatorSystemRealPart S →ₗ[ℝ] S where
  toFun x := ⟨x.val, x.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma positive_subspace_selfAdjoint_im (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a)
    (a : S) (ha : IsSelfAdjoint (a : A)) : (f a).im = 0 := by
  let e : S := ⟨1, h1⟩
  have he : (f e).im = 0 := (hf e zero_le_one).2.symm
  have hb : 0 ≤ ‖a‖ • (1 : A) + (a : A) := by
    change 0 ≤ ‖(a : A)‖ • (1 : A) + (a : A)
    have h := ha.neg_algebraMap_norm_le_self
    simpa only [Algebra.algebraMap_eq_smul_one, neg_le_iff_add_nonneg, add_comm] using h
  have h := (hf ((‖a‖ : ℂ) • e + a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) + (a : A)
    rw [Complex.coe_smul]
    exact hb)).2
  simpa only [map_add, map_smul, smul_eq_mul, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, he, mul_zero, zero_mul, zero_add,
    Complex.zero_im] using h.symm

lemma positive_subspace_real_bound (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a)
    (a : S) (ha : IsSelfAdjoint (a : A)) :
    |(f a).re| ≤ (f ⟨1, h1⟩).re * ‖a‖ := by
  let e : S := ⟨1, h1⟩
  have hup : 0 ≤ ‖a‖ • (1 : A) - (a : A) := by
    apply sub_nonneg.mpr
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using ha.le_algebraMap_norm_self
  have hlo : 0 ≤ ‖a‖ • (1 : A) + (a : A) := by
    change 0 ≤ ‖(a : A)‖ • (1 : A) + (a : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_le_iff_add_nonneg, add_comm]
      using ha.neg_algebraMap_norm_le_self
  have hp := (hf ((‖a‖ : ℂ) • e - a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) - (a : A)
    rw [Complex.coe_smul]
    exact hup)).1
  have hm := (hf ((‖a‖ : ℂ) • e + a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) + (a : A)
    rw [Complex.coe_smul]
    exact hlo)).1
  simp only [map_sub, map_add, map_smul, smul_eq_mul, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re] at hp hm
  change 0 ≤ ‖a‖ * (f ⟨1, h1⟩).re - (f a).re at hp
  change 0 ≤ ‖a‖ * (f ⟨1, h1⟩).re + (f a).re at hm
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

def operatorSystemRealFunctional (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a) :
    operatorSystemRealPart S →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (Complex.reLm.comp ((f.restrictScalars ℝ).comp (operatorSystemRealInclusion S)))
    (f ⟨1, h1⟩).re (fun a =>
      positive_subspace_real_bound S h1 f hf (operatorSystemRealInclusion S a) a.property.2)

lemma selfAdjoint_nonneg_of_norm_le (g : selfAdjoint A →L[ℝ] ℝ) (c : ℝ)
    (hg : ‖g‖ ≤ c) (h1 : g 1 = c) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ g a := by
  have hau : (a : A) ≤ ‖a‖ • (1 : A) := by
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (a : A) (norm_nonneg _) ha).mp le_rfl
  have hpos : 0 ≤ ‖a‖ • (1 : A) - (a : A) := sub_nonneg.mpr hau
  have hn : ‖‖a‖ • (1 : selfAdjoint A) - a‖ ≤ ‖a‖ := by
    change ‖‖a‖ • (1 : A) - (a : A)‖ ≤ ‖a‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hpos).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖a‖ • (1 : A)) ha
  have hc : ‖g (‖a‖ • (1 : selfAdjoint A) - a)‖ ≤ c * ‖a‖ :=
    (g.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hn ((norm_nonneg g).trans hg)))
  rw [map_sub, map_smul, h1, smul_eq_mul, Real.norm_eq_abs] at hc
  have h := (le_abs_self _).trans hc
  nlinarith

end BoundedHochschild.KadisonRingrose

end

end OAI
