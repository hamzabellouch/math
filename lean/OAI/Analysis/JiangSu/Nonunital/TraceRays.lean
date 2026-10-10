import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.CompactTraceBase

namespace OAI


noncomputable section
namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def functionalWeight (f : A →ₚ[ℂ] ℂ) (htr : ∀ a b, f (a*b)=f (b*a)) : ExtendedTrace A where
  toFun a := ENNReal.ofReal (f a.1).re
  map_zero := by simp [Positive.zero]
  map_add a b := by
    change ENNReal.ofReal (f (a.1+b.1)).re=_
    rw [map_add,Complex.add_re,ENNReal.ofReal_add (f.map_nonneg a.2).1 (f.map_nonneg b.2).1]
  map_smul r a := by
    change ENNReal.ofReal (f ((r:ℝ) • a.1)).re=_
    rw [←Complex.coe_smul,map_smul,smul_eq_mul,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  tracial x := by change ENNReal.ofReal (f (star x*x)).re=ENNReal.ofReal (f (x*star x)).re;rw [htr]
  lowerSemicontinuous :=
    (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp ((map_continuous f).comp continuous_subtype_val))).lowerSemicontinuous

lemma functionalWeight_bounded (f : A →ₚ[ℂ] ℂ) (htr : ∀ a b, f (a*b)=f (b*a)) :
    WeightBounded (functionalWeight f htr) := by
  refine ⟨‖positiveFunctionalCLM f‖₊,?_⟩
  intro a ha
  change ENNReal.ofReal (f a.1).re ≤ (‖positiveFunctionalCLM f‖₊:ℝ≥0∞)
  rw [←ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.re_le_norm _).trans ((positiveFunctionalCLM f).le_opNorm a.1 |>.trans
    (mul_le_of_le_one_right (norm_nonneg _) ha))

lemma functionalWeight_recover (τ : ExtendedTrace A) (hτ : WeightBounded τ) :
    functionalWeight (boundedWeightFunctional τ hτ) (boundedWeightFunctional_tracial τ hτ)=τ := by
  apply ExtendedTrace.ext
  intro a
  change ENNReal.ofReal (boundedWeightFunctional τ hτ a.1).re=τ a
  rw [show boundedWeightFunctional τ hτ a.1=((τ a).toReal:ℂ) from
    ExtendedTraceExtension.functional_positive τ (weightBounded_finite hτ) a]
  simp only [Complex.ofReal_re,ENNReal.ofReal_toReal (weightBounded_finite hτ a)]

lemma positiveFunctional_ext_of_nonneg {f g : A →ₚ[ℂ] ℂ}
    (h : ∀ a : A, 0 ≤ a → f a=g a) : f=g := by
  apply PositiveLinearMap.ext
  have hsa (a : selfAdjoint A) : f a.1=g a.1 := by
    rw [←CFC.posPart_sub_negPart a.1 a.2,map_sub,map_sub,
      h _ (CFC.posPart_nonneg _),h _ (CFC.negPart_nonneg _)]
  intro x
  rw [←realPart_add_I_smul_imaginaryPart x,map_add,map_add,map_smul,map_smul,
    hsa (realPart x),hsa (imaginaryPart x)]

lemma functionalWeight_injective (f g : A →ₚ[ℂ] ℂ)
    (hf : ∀ a b, f (a*b)=f (b*a)) (hg : ∀ a b, g (a*b)=g (b*a))
    (h : functionalWeight f hf=functionalWeight g hg) : f=g := by
  apply positiveFunctional_ext_of_nonneg
  intro a ha
  have he := congrArg (fun τ : ExtendedTrace A => τ ⟨a,ha⟩) h
  change ENNReal.ofReal (f a).re=ENNReal.ofReal (g a).re at he
  apply Complex.ext
  · have hv := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (f.map_nonneg ha).1,ENNReal.toReal_ofReal (g.map_nonneg ha).1] using hv
  · exact ((Complex.nonneg_iff.mp (f.map_nonneg ha)).2).symm.trans
      (Complex.nonneg_iff.mp (g.map_nonneg ha)).2

lemma normalizedWeight_ray (τ : ExtendedTrace A) (hτ : WeightBounded τ) (hne : τ ≠ 0)
    (a : Positive A) :
    τ a=(‖positiveFunctionalCLM (boundedWeightFunctional τ hτ)‖₊:ℝ≥0∞)*
      ENNReal.ofReal ((normalizedWeight τ hτ hne).functional a.1).re := by
  have hn := norm_pos_iff.mpr (boundedWeightFunctional_nonzero hτ hne)
  change τ a=(‖positiveFunctionalCLM (boundedWeightFunctional τ hτ)‖₊:ℝ≥0∞)*
    ENNReal.ofReal (scaleFunctional _ _ a.1).re
  rw [scaleFunctional_apply,show boundedWeightFunctional τ hτ a.1=((τ a).toReal:ℂ) from
    ExtendedTraceExtension.functional_positive τ (weightBounded_finite hτ) a]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,NNReal.coe_inv,coe_nnnorm]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hn.le),ENNReal.ofReal_toReal (weightBounded_finite hτ a)]
  rw [ENNReal.ofReal_inv_of_pos hn,show ENNReal.ofReal ‖positiveFunctionalCLM (boundedWeightFunctional τ hτ)‖=(‖positiveFunctionalCLM (boundedWeightFunctional τ hτ)‖₊:ℝ≥0∞) from ofReal_norm _,←mul_assoc,ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast (nnnorm_ne_zero_iff.mpr (boundedWeightFunctional_nonzero hτ hne))
  · exact ENNReal.coe_ne_top

end NonunitalGamma

end


noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def NormalizedTrace.twoNorm (τ : NormalizedTrace A) (a : A) : ℝ :=
  traceTwoNorm τ.unitized (Unitization.inr a)

lemma NormalizedTrace.twoNorm_nonneg (τ : NormalizedTrace A) (a : A) :
    0 ≤ τ.twoNorm a := traceTwoNorm_nonneg _ _

@[simp] lemma NormalizedTrace.twoNorm_zero (τ : NormalizedTrace A) : τ.twoNorm 0=0 := by
  simp [NormalizedTrace.twoNorm]

lemma NormalizedTrace.twoNorm_add_le (τ : NormalizedTrace A) (a b : A) :
    τ.twoNorm (a+b) ≤ τ.twoNorm a+τ.twoNorm b := by
  simpa only [NormalizedTrace.twoNorm,Unitization.inr_add] using
    traceTwoNorm_add_le τ.unitized (Unitization.inr a) (Unitization.inr b)

@[simp] lemma NormalizedTrace.twoNorm_neg (τ : NormalizedTrace A) (a : A) :
    τ.twoNorm (-a)=τ.twoNorm a := by
  simp only [NormalizedTrace.twoNorm,Unitization.inr_neg,traceTwoNorm_neg]

lemma NormalizedTrace.twoNorm_mul_left (τ : NormalizedTrace A) (a b : A) :
    τ.twoNorm (a*b) ≤ ‖a‖*τ.twoNorm b := by
  simpa only [NormalizedTrace.twoNorm,Unitization.inr_mul,Unitization.norm_inr] using
    traceTwoNorm_mul_left τ.unitized (Unitization.inr a) (Unitization.inr b)

lemma NormalizedTrace.twoNorm_mul_right (τ : NormalizedTrace A) (a b : A) :
    τ.twoNorm (b*a) ≤ ‖a‖*τ.twoNorm b := by
  simpa only [NormalizedTrace.twoNorm,Unitization.inr_mul,Unitization.norm_inr] using
    traceTwoNorm_mul_right τ.unitized (Unitization.inr a) (Unitization.inr b)

lemma NormalizedTrace.norm_le_twoNorm (τ : NormalizedTrace A) (a : A) :
    ‖τ.functional a‖ ≤ τ.twoNorm a := by
  simpa only [NormalizedTrace.unitized_inr,NormalizedTrace.twoNorm] using trace_norm_le_twoNorm τ.unitized (Unitization.inr a)

lemma NormalizedTrace.twoNorm_eq (τ : NormalizedTrace A) (a : A) :
    τ.twoNorm a=Real.sqrt (τ.functional (star a*a)).re := by
  simp only [NormalizedTrace.twoNorm,traceTwoNorm,←Unitization.inr_star,←Unitization.inr_mul,
    NormalizedTrace.unitized_inr]

lemma NormalizedTrace.continuous_twoNorm (τ : NormalizedTrace A) : Continuous τ.twoNorm := by
  rw [show τ.twoNorm = fun a => Real.sqrt (τ.functional (star a*a)).re from funext τ.twoNorm_eq]
  exact Real.continuous_sqrt.comp (Complex.continuous_re.comp ((map_continuous τ.functional).comp
    (continuous_star.mul continuous_id)))

def NormalizedTrace.nullIdeal (τ : NormalizedTrace A) : TwoSidedIdeal A :=
  .mk' {a | τ.twoNorm a=0} τ.twoNorm_zero
    (fun {a b} ha hb => le_antisymm (by
      change τ.twoNorm a=0 at ha;change τ.twoNorm b=0 at hb
      simpa only [ha,hb,add_zero] using τ.twoNorm_add_le a b) (τ.twoNorm_nonneg _))
    (fun {a} ha => by simpa only [Set.mem_ofPred_eq,τ.twoNorm_neg] using ha)
    (fun {a b} hb => le_antisymm (by
      change τ.twoNorm b=0 at hb
      simpa only [hb,mul_zero] using τ.twoNorm_mul_left a b) (τ.twoNorm_nonneg _))
    (fun {a b} ha => le_antisymm (by
      change τ.twoNorm a=0 at ha
      simpa only [ha,mul_zero] using τ.twoNorm_mul_right b a) (τ.twoNorm_nonneg _))

lemma NormalizedTrace.nullIdeal_isClosed (τ : NormalizedTrace A) :
    IsClosed (τ.nullIdeal : Set A) := by
  rw [NormalizedTrace.nullIdeal,TwoSidedIdeal.coe_mk']
  exact isClosed_eq τ.continuous_twoNorm continuous_const

lemma NormalizedTrace.nullIdeal_eq_bot (τ : NormalizedTrace A) (hsimple : TopologicallySimple A) :
    τ.nullIdeal=⊥ := by
  rcases hsimple τ.nullIdeal τ.nullIdeal_isClosed with h|h
  · exact h
  · have hz (a : A) : τ.functional a=0 := by
      have ha : a ∈ τ.nullIdeal := h.symm ▸ TwoSidedIdeal.mem_top A
      simp only [NormalizedTrace.nullIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] at ha
      exact norm_le_zero_iff.mp (by simpa only [ha] using τ.norm_le_twoNorm a)
    have hf : positiveFunctionalCLM τ.functional=0 := by ext a;exact hz a
    have hn := τ.norm_one
    rw [hf,norm_zero] at hn
    exact (zero_ne_one hn).elim

theorem NormalizedTrace.faithful (τ : NormalizedTrace A) (hsimple : TopologicallySimple A)
    (a : A) (ha : 0 ≤ a) (hτ : τ.functional a=0) : a=0 := by
  have hz : CFC.sqrt a ∈ τ.nullIdeal := by
    simp only [NormalizedTrace.nullIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]
    rw [τ.twoNorm_eq,(CFC.sqrt_nonneg a).star_eq,CFC.sqrt_mul_sqrt_self a ha,hτ]
    simp
  rw [τ.nullIdeal_eq_bot hsimple,TwoSidedIdeal.mem_bot] at hz
  rw [←CFC.sqrt_mul_sqrt_self a ha,hz,zero_mul]

end NonunitalGamma

end

end OAI
