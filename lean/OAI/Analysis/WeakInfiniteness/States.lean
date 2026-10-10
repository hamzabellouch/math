import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_add_one_of_nonneg [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ‖b + 1‖ = ‖b‖ + 1 := by
  apply le_antisymm
  · exact (norm_add_le _ _).trans (by rw [norm_one])
  · have hs : ‖b‖ + 1 ∈ spectrum ℝ (b + 1) := by
      simpa only [map_one, add_comm (1 : A) b] using
        (spectrum.add_mem_add_iff (R := ℝ) (a := b) (r := ‖b‖) (s := 1)).mpr
          (CStarAlgebra.norm_mem_spectrum_of_nonneg b hb)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖b‖ + 1)] using
      spectrum.norm_le_norm_of_mem hs

def selfAdjointComplexification (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (realPart a) : ℂ) + Complex.I * (f (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' c a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add,
      map_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointComplexification_apply (f : selfAdjoint A →ₗ[ℝ] ℝ) (b : selfAdjoint A) :
    selfAdjointComplexification f (b : A) = (f b : ℂ) := by
  have hr : realPart (b : A) = b := Subtype.ext b.property.coe_realPart
  simp [selfAdjointComplexification, hr, b.property.imaginaryPart]

lemma real_functional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hf : ‖f‖ ≤ 1) (hf1 : f 1 = 1) (b : selfAdjoint A) (hb : 0 ≤ (b : A)) :
    0 ≤ f b := by
  let z : selfAdjoint A := ‖b‖ • 1 - b
  have hb' : IsSelfAdjoint (b : A) := b.property
  have hz : 0 ≤ (z : A) := by
    change 0 ≤ ‖b‖ • (1 : A) - (b : A)
    rw [sub_nonneg, ← Algebra.algebraMap_eq_smul_one]
    exact hb'.le_algebraMap_norm_self
  have hzn : ‖z‖ ≤ ‖b‖ := by
    change ‖(z : A)‖ ≤ ‖(b : A)‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hz).mpr
    change ‖b‖ • (1 : A) - (b : A) ≤ algebraMap ℝ A ‖(b : A)‖
    rw [Algebra.algebraMap_eq_smul_one]
    exact sub_le_self _ hb
  have hg : f z ≤ ‖b‖ := calc
    f z ≤ ‖f z‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
    _ ≤ 1 * ‖b‖ := mul_le_mul hf hzn (norm_nonneg _) zero_le_one
    _ = ‖b‖ := one_mul _
  simp only [z, map_sub, map_smul, hf1, smul_eq_mul, mul_one] at hg
  linarith

def positiveComplexification (f : selfAdjoint A →L[ℝ] ℝ)
    (hf : ‖f‖ ≤ 1) (hf1 : f 1 = 1) : A →ₚ[ℂ] ℂ where
  toLinearMap := selfAdjointComplexification f.toLinearMap
  monotone' := by
    intro a b hab
    change selfAdjointComplexification f.toLinearMap a ≤ selfAdjointComplexification f.toLinearMap b
    rw [← sub_nonneg, ← map_sub]
    let z : selfAdjoint A := ⟨b-a, IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hab)⟩
    change 0 ≤ selfAdjointComplexification f.toLinearMap (z : A)
    rw [selfAdjointComplexification_apply]
    exact Complex.zero_le_real.mpr (real_functional_nonneg f hf hf1 z (sub_nonneg.mpr hab))

lemma positiveComplexification_apply (f : selfAdjoint A →L[ℝ] ℝ)
    (hf : ‖f‖ ≤ 1) (hf1 : f 1 = 1) (b : selfAdjoint A) :
    positiveComplexification f hf hf1 (b : A) = (f b : ℂ) :=
  selfAdjointComplexification_apply _ _

theorem exists_norming_positive_functional [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f b = (‖b‖ : ℂ) := by
  let b' : selfAdjoint A := ⟨b, IsSelfAdjoint.of_nonneg hb⟩
  have hn : ‖b' + 1‖ = ‖b‖ + 1 := norm_add_one_of_nonneg b hb
  obtain ⟨f, hf, hfb⟩ := exists_dual_vector ℝ (b' + 1) (by rw [hn]; positivity)
  have hf1 : f 1 ≤ 1 := calc
    f 1 ≤ ‖f 1‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖(1 : selfAdjoint A)‖ := f.le_opNorm _
    _ = 1 := by rw [hf]; change 1 * ‖(1 : A)‖ = 1; simp
  have hfb' : f b' ≤ ‖b‖ := calc
    f b' ≤ ‖f b'‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖b'‖ := f.le_opNorm _
    _ = ‖b‖ := by rw [hf, one_mul]; rfl
  rw [map_add, hn] at hfb
  change f b' + f 1 = ‖b‖ + 1 at hfb
  have hfone : f 1 = 1 := by linarith
  have hfnorm : f b' = ‖b‖ := by linarith
  refine ⟨positiveComplexification f hf.le hfone, ?_, ?_⟩
  · change positiveComplexification f hf.le hfone ((1 : selfAdjoint A) : A) = 1
    rw [positiveComplexification_apply, hfone, Complex.ofReal_one]
  · change positiveComplexification f hf.le hfone (b' : A) = _
    rw [positiveComplexification_apply, hfnorm]

def gnsCyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS 1 : f.GNS)

lemma norm_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ‖gnsCyclicVector f‖ = 1 := by
  rw [gnsCyclicVector, UniformSpace.Completion.norm_coe]
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [hf]

lemma norm_gns_action_sq (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖f.gnsStarAlgHom a (gnsCyclicVector f)‖ ^ 2 = (f (star a * a)).re := by
  change ‖f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1 : f.GNS)‖ ^ 2 = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.norm_coe]
  change ‖f.toPreGNS (a * 1)‖ ^ 2 = _
  rw [mul_one, PositiveLinearMap.preGNS_norm_def]
  apply Real.sq_sqrt
  exact (Complex.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg a))).1

theorem exists_norming_gns [Nontrivial A] (a : A) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ ‖f.gnsStarAlgHom a‖ = ‖a‖ := by
  obtain ⟨f, hf, hfa⟩ := exists_norming_positive_functional (star a * a)
    (star_mul_self_nonneg a)
  refine ⟨f, hf, le_antisymm (NonUnitalStarAlgHom.norm_apply_le f.gnsNonUnitalStarAlgHom a) ?_⟩
  have hn : ‖f.gnsStarAlgHom a (gnsCyclicVector f)‖ = ‖a‖ := by
    have hs := norm_gns_action_sq f a
    rw [hfa, Complex.ofReal_re, CStarRing.norm_star_mul_self] at hs
    nlinarith [norm_nonneg (f.gnsStarAlgHom a (gnsCyclicVector f)), norm_nonneg a]
  calc
    ‖a‖ = ‖f.gnsStarAlgHom a (gnsCyclicVector f)‖ := hn.symm
    _ ≤ ‖f.gnsStarAlgHom a‖ * ‖gnsCyclicVector f‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖f.gnsStarAlgHom a‖ := by rw [norm_gnsCyclicVector f hf, mul_one]

end WeakPureInfiniteness
end

end OAI
