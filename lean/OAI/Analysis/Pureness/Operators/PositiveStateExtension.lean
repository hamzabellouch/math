import OAI.Analysis.Pureness.Operators.SimpleStateGNS

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule InnerProductSpace
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma positiveState_norm_le (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) (a : A) : ‖f a‖ ≤ ‖a‖ := by
  rw [← stateGNS_vector_value f a]
  calc
    _ ≤ ‖stateGNSVector f‖ * ‖f.gnsStarAlgHom a (stateGNSVector f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖stateGNSVector f‖ * (‖f.gnsStarAlgHom a‖ * ‖stateGNSVector f‖) :=
      mul_le_mul_of_nonneg_left ((f.gnsStarAlgHom a).le_opNorm _) (norm_nonneg _)
    _ = ‖f.gnsStarAlgHom a‖ := by rw [stateGNSVector_norm f h1]; ring
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom.toNonUnitalStarAlgHom a

def positiveStateReal (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) : selfAdjoint A →L[ℝ] ℝ :=
  (Complex.reLm.comp (f.toLinearMap.restrictScalars ℝ) |>.comp
    (selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by
      change ‖(f (a : A)).re‖ ≤ 1 * ‖a‖
      simpa using (Complex.abs_re_le_norm (f (a : A))).trans (positiveState_norm_le f h1 a))

lemma positiveStateReal_norm_le (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ‖positiveStateReal f h1‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖(f (a : A)).re‖ ≤ 1 * ‖a‖
  simpa using (Complex.abs_re_le_norm (f (a : A))).trans (positiveState_norm_le f h1 a)

lemma positiveStateReal_one (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    positiveStateReal f h1 1 = 1 := by
  change (f 1).re = 1
  simp [h1]

lemma positiveStateReal_complexify (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) (a : A) :
    selfAdjointFunctionalComplex (positiveStateReal f h1).toLinearMap a = f a := by
  have hr : ((f (realPart a : A)).re : ℂ) = f (realPart a : A) := by
    apply Complex.ext
    · rfl
    · exact (Complex.conj_eq_iff_im.mp ((realPart a).property.map f).star_eq).symm
  have hi : ((f (imaginaryPart a : A)).re : ℂ) = f (imaginaryPart a : A) := by
    apply Complex.ext
    · rfl
    · exact (Complex.conj_eq_iff_im.mp ((imaginaryPart a).property.map f).star_eq).symm
  change ((f (realPart a : A)).re : ℂ) + Complex.I * ((f (imaginaryPart a : A)).re : ℂ) = f a
  rw [hr, hi, ← smul_eq_mul, ← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]

def selfAdjointEmbedding (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι) :
    selfAdjoint A →ₗᵢ[ℝ] selfAdjoint B where
  toFun a := ⟨ι a, a.property.map ι⟩
  map_add' a b := Subtype.ext (map_add ι (a : A) (b : A))
  map_smul' r a := Subtype.ext ((ι.toLinearMap.restrictScalars ℝ).map_smul r (a : A))
  norm_map' a := NonUnitalStarAlgHom.norm_map ι.toNonUnitalStarAlgHom hι a

lemma realFunctional_extension_isometry {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (f : E →L[ℝ] ℝ) :
    ∃ g : F →L[ℝ] ℝ, (∀ a, g (e a) = f a) ∧ ‖g‖ ≤ ‖f‖ := by
  let fr := f.comp e.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq e.toLinearMap.range fr
  refine ⟨g, ?_, ?_⟩
  · intro a
    simpa [fr] using hg (e.equivRange a)
  · rw [hgn]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    simpa [fr] using f.le_opNorm (e.equivRange.symm a)

theorem exists_positiveState_extension (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι)
    (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ∃ g : B →ₚ[ℂ] ℂ, g 1 = 1 ∧ ∀ a, g (ι a) = f a := by
  let e := selfAdjointEmbedding ι hι
  obtain ⟨g, hg, hgn⟩ := realFunctional_extension_isometry e (positiveStateReal f h1)
  have hn : ‖g‖ ≤ 1 := hgn.trans (positiveStateReal_norm_le f h1)
  have he1 : e 1 = 1 := Subtype.ext ι.map_one
  have hg1 : g 1 = 1 := by simpa [he1, positiveStateReal_one] using hg 1
  let c := selfAdjointFunctionalComplex g.toLinearMap
  have hc : ∀ b : B, 0 ≤ b → 0 ≤ c b := by
    intro b hb
    change 0 ≤ selfAdjointFunctionalComplex g.toLinearMap (⟨b, .of_nonneg hb⟩ : selfAdjoint B)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast selfAdjointFunctional_nonneg g hn hg1 ⟨b, .of_nonneg hb⟩ hb
  refine ⟨PositiveLinearMap.mk₀ c hc, ?_, ?_⟩
  · change selfAdjointFunctionalComplex g.toLinearMap ((1 : selfAdjoint B) : B) = 1
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast hg1
  · intro a
    have hr : realPart (ι a) = e (realPart a) := Subtype.ext (map_realPart ι a).symm
    have hi : imaginaryPart (ι a) = e (imaginaryPart a) := Subtype.ext (map_imaginaryPart ι a).symm
    change (g (realPart (ι a)) : ℂ) + Complex.I * (g (imaginaryPart (ι a)) : ℂ) = f a
    rw [hr, hi, hg, hg]
    exact positiveStateReal_complexify f h1 a
end CuntzPureness

end

end OAI
