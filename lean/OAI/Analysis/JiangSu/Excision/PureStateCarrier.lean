import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
namespace PureStateExcision
open scoped ComplexOrder ComplexStarModule

variable {A : Type*} [CStarAlgebra A]

def realStateCarrier : Set (WeakDual ℝ (selfAdjoint A)) :=
  {f | f 1 = 1 ∧ ‖f.toStrongDual‖ ≤ 1}

lemma realStateCarrier_isCompact : IsCompact (realStateCarrier (A := A)) := by
  have heq : realStateCarrier (A := A) =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (selfAdjoint A)) 1 ∩
        {f : WeakDual ℝ (selfAdjoint A) | f 1 = 1} := by
    ext f
    change (f 1 = 1 ∧ ‖f.toStrongDual‖ ≤ 1) ↔
      (f.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℝ (selfAdjoint A)) 1 ∧ f 1 = 1)
    rw [mem_closedBall_zero_iff (E := StrongDual ℝ (selfAdjoint A))]
    exact and_comm
  rw [heq]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℝ (selfAdjoint A)) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous _) continuous_const)

lemma realStateCarrier_nonempty [Nontrivial A] : (realStateCarrier (A := A)).Nonempty := by
  have hn1 : ‖(1 : selfAdjoint A)‖ = 1 := norm_one (α := A)
  obtain ⟨f,hfn,hf1⟩ := exists_dual_vector ℝ (1 : selfAdjoint A) (by rw [hn1]; norm_num)
  exact ⟨StrongDual.toWeakDual f,by simpa [hn1] using hf1,hfn.le⟩

lemma exists_extreme_realState [Nontrivial A] :
    ((realStateCarrier (A := A)).extremePoints ℝ).Nonempty := by
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) :=
    WeakBilin.locallyConvexSpace
  exact realStateCarrier_isCompact.extremePoints_nonempty realStateCarrier_nonempty

variable [PartialOrder A] [StarOrderedRing A]

def toPositiveState (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ realStateCarrier) :
    A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
  (Pureness.selfAdjointFunctionalComplex f.toStrongDual.toLinearMap) (by
    intro a ha
    change 0 ≤ Pureness.selfAdjointFunctionalComplex f.toStrongDual.toLinearMap
      ((⟨a, IsSelfAdjoint.of_nonneg ha⟩ : selfAdjoint A) : A)
    rw [Pureness.selfAdjointFunctionalComplex_apply]
    exact_mod_cast Pureness.selfAdjointFunctional_nonneg f.toStrongDual hf.2 hf.1
      ⟨a, IsSelfAdjoint.of_nonneg ha⟩ ha)

lemma toPositiveState_one (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ realStateCarrier) :
    toPositiveState f hf 1 = 1 := by
  change Pureness.selfAdjointFunctionalComplex f.toStrongDual.toLinearMap
    ((1 : selfAdjoint A) : A) = 1
  rw [Pureness.selfAdjointFunctionalComplex_apply]
  exact_mod_cast hf.1

lemma toPositiveState_apply (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ realStateCarrier)
    (a : selfAdjoint A) : toPositiveState f hf a = (f a : ℂ) :=
  Pureness.selfAdjointFunctionalComplex_apply _ a


def ofPositiveState (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : WeakDual ℝ (selfAdjoint A) :=
  StrongDual.toWeakDual (CurrentMain.stateRealContinuous f hf)

lemma ofPositiveState_mem (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ofPositiveState f hf ∈ realStateCarrier := by
  constructor
  · change (f 1).re=1
    simp [hf]
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change |(f a).re|≤1*‖a‖
    simpa only [one_mul] using CurrentMain.state_realPart_bound f hf a

lemma positive_state_eq (f g : A →ₚ[ℂ] ℂ)
    (h : ∀ a : selfAdjoint A,(f a).re=(g a).re) : f=g := by
  have he (a : selfAdjoint A) : f a=g a := by
    apply Complex.ext (h a)
    have hf : (f a).im=0 := Complex.conj_eq_iff_im.mp (a.property.map f).star_eq
    have hg : (g a).im=0 := Complex.conj_eq_iff_im.mp (a.property.map g).star_eq
    rw [hf,hg]
  ext a
  have ha := realPart_add_I_smul_imaginaryPart a
  calc
    f a=f ((ℜ a : A)+Complex.I • (ℑ a : A)) := congrArg f ha.symm
    _=g ((ℜ a : A)+Complex.I • (ℑ a : A)) := by rw [map_add,map_add,map_smul,map_smul,he,he]
    _=g a := congrArg g ha

lemma extreme_convex_decomposition (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ (realStateCarrier (A := A)).extremePoints ℝ)
    (g h : A →ₚ[ℂ] ℂ) (hg : g 1=1) (hh : h 1=1)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (heq : ∀ a : A,toPositiveState f hf.1 a=(t : ℂ)*g a+(1-t : ℂ)*h a) :
    g=toPositiveState f hf.1 := by
  have hw : f=t • ofPositiveState g hg+(1-t) • ofPositiveState h hh := by
    apply DFunLike.ext
    intro a
    change f a=t*(g a).re+(1-t)*(h a).re
    have ha := congrArg Complex.re (heq a)
    rw [toPositiveState_apply] at ha
    simpa only [Complex.ofReal_re,Complex.add_re,Complex.mul_re,Complex.ofReal_im,
      Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,zero_sub,sub_zero,
      zero_mul] using ha
  have hseg : f ∈ openSegment ℝ (ofPositiveState g hg) (ofPositiveState h hh) := by
    rw [hw]
    exact ⟨t,1-t,ht,sub_pos.mpr ht1,by ring,rfl⟩
  have he := (mem_extremePoints_iff_left.mp hf).2 _ (ofPositiveState_mem g hg)
    _ (ofPositiveState_mem h hh) hseg
  apply positive_state_eq
  intro a
  have hd := congrArg (fun F : WeakDual ℝ (selfAdjoint A) => F a) he
  change (g a).re=f a at hd
  rw [toPositiveState_apply,Complex.ofReal_re]
  exact hd

def normalizedPositive (g : A →ₚ[ℂ] ℂ) (t : ℝ) (ht : 0<t) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (((t⁻¹ : ℝ) : ℂ) • g.toLinearMap) (by
    intro a ha
    exact mul_nonneg (by exact_mod_cast (inv_pos.mpr ht).le) (g.map_nonneg ha))

lemma normalizedPositive_apply (g : A →ₚ[ℂ] ℂ) (t : ℝ) (ht : 0<t) (a : A) :
    normalizedPositive g t ht a=((t⁻¹ : ℝ) : ℂ)*g a := rfl

lemma normalizedPositive_one (g : A →ₚ[ℂ] ℂ) (t : ℝ) (ht : 0<t) (hg : g 1=(t : ℂ)) :
    normalizedPositive g t ht 1=1 := by
  rw [normalizedPositive_apply,hg]
  exact_mod_cast inv_mul_cancel₀ ht.ne'

theorem extreme_positive_summand (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ (realStateCarrier (A := A)).extremePoints ℝ)
    (g h : A →ₚ[ℂ] ℂ) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hg : g 1=(t : ℂ)) (hh : h 1=(1-t : ℂ))
    (hadd : ∀ a : A,g a+h a=toPositiveState f hf.1 a) :
    ∀ a : A,g a=(t : ℂ)*toPositiveState f hf.1 a := by
  have hu : 0<1-t := sub_pos.mpr ht1
  have he := extreme_convex_decomposition f hf (normalizedPositive g t ht)
    (normalizedPositive h (1-t) hu) (normalizedPositive_one g t ht hg)
    (normalizedPositive_one h (1-t) hu (by simpa using hh)) ht ht1 (fun a => by
      rw [normalizedPositive_apply,normalizedPositive_apply,←mul_assoc,←mul_assoc]
      have h1 : (t : ℂ)*((t⁻¹ : ℝ) : ℂ)=1 := by exact_mod_cast mul_inv_cancel₀ ht.ne'
      have h2 : (1-(t : ℂ))*(((1-t)⁻¹ : ℝ) : ℂ)=1 := by
        norm_cast
        exact mul_inv_cancel₀ hu.ne'
      rw [h1,h2,one_mul,one_mul]
      exact (hadd a).symm)
  intro a
  have hva := congrArg (fun q : A →ₚ[ℂ] ℂ => q a) he
  rw [normalizedPositive_apply] at hva
  rw [←hva,←mul_assoc,←Complex.ofReal_mul,mul_inv_cancel₀ ht.ne',Complex.ofReal_one,one_mul]

lemma toPositiveState_ofPositiveState (f : A →ₚ[ℂ] ℂ) (hf : f 1=1) :
    toPositiveState (ofPositiveState f hf) (ofPositiveState_mem f hf)=f := by
  apply positive_state_eq
  intro a
  rw [toPositiveState_apply,Complex.ofReal_re]
  rfl

lemma ofPositiveState_toPositiveState (f : WeakDual ℝ (selfAdjoint A))
    (hf : f∈realStateCarrier) :
    ofPositiveState (toPositiveState f hf) (toPositiveState_one f hf)=f := by
  apply DFunLike.ext
  intro a
  change (toPositiveState f hf a).re=f a
  rw [toPositiveState_apply,Complex.ofReal_re]

theorem exists_pure_positive_state [Nontrivial A] :
    ∃ (f : A →ₚ[ℂ] ℂ) (hf : f 1=1),
      ofPositiveState f hf∈(realStateCarrier (A := A)).extremePoints ℝ := by
  obtain ⟨f,hf⟩ := exists_extreme_realState (A := A)
  refine ⟨toPositiveState f hf.1,toPositiveState_one f hf.1,?_⟩
  rw [ofPositiveState_toPositiveState]
  exact hf

end PureStateExcision

end

end OAI
