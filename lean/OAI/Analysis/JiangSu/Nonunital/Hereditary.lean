import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model
import OAI.Analysis.JiangSu.Nonunital.TraceRays

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Filter Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def sandwichSubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A where
  carrier := Set.range (fun w : A => h * w * h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by noncomm_ring⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * h * h * y, by simp only [mul_assoc]⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨star x, by simp only [star_mul, hh.star_eq, mul_assoc]⟩

noncomputable def hereditarySubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A :=
  (sandwichSubalgebra h hh).topologicalClosure

def hereditaryCarrier (h : A) : Set A := closure (Set.range (fun w : A => h * w * h))

lemma hereditarySubalgebra_coe (h : A) (hh : 0 ≤ h) :
    (hereditarySubalgebra h hh : Set A) = hereditaryCarrier h := rfl

instance hereditarySubalgebra_closed (h : A) (hh : 0 ≤ h) :
    IsClosed (hereditarySubalgebra h hh : Set A) := isClosed_closure

lemma hereditary_sqrt_mem {h a : A} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (ham : a ∈ hereditaryCarrier h) : CFC.sqrt a ∈ hereditaryCarrier h := by
  change CFC.sqrt a ∈ hereditarySubalgebra h hh
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem Real.sqrt (show a ∈ hereditarySubalgebra h hh from ham)

lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) : h ∈ hereditaryCarrier h := by
  have hm : h * h ∈ hereditaryCarrier h := by
    have ht := ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const h
    exact isClosed_closure.mem_of_tendsto ht
      (Eventually.of_forall fun u => subset_closure ⟨u,rfl⟩)
  have hs := hereditary_sqrt_mem hh (by simpa only [hh.star_eq] using star_mul_self_nonneg h) hm
  simpa only [CFC.sqrt_mul_self h hh] using hs

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_sandwich_mem {h x y : A} (z : A)
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier h) :
    x * z * y ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  apply isClosed_closure.mem_of_tendsto ((hux.mul_const z).mul hvy)
  apply Eventually.of_forall
  intro j
  obtain ⟨a, ha⟩ := hu j
  obtain ⟨b, hb⟩ := hv j
  apply subset_closure
  exact ⟨a * h * z * h * b, by simp only [← ha, ← hb, mul_assoc]⟩

lemma sqrt_sandwich_mem_hereditary (h z : A) (hh : 0 ≤ h) :
    CFC.sqrt h * z * CFC.sqrt h ∈ hereditaryCarrier h := by
  have hm := hereditary_sqrt_mem hh hh (self_mem_hereditary h hh)
  exact hereditary_sandwich_mem z hm hm

open ComplexStarModule
open scoped ComplexOrder CStarAlgebra

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_complex_smul_mem {h x : A} (z : ℂ) (hx : x ∈ hereditaryCarrier h) :
    z • x ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hx
  apply isClosed_closure.mem_of_tendsto (ht.const_smul z)
  apply Eventually.of_forall
  intro j
  obtain ⟨w, hw⟩ := hu j
  apply subset_closure
  exact ⟨z • w, by simp only [← hw, mul_smul_comm, smul_mul_assoc]⟩

lemma hereditary_realPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℜ x : A) ∈ hereditaryCarrier h := by
  rw [realPart_apply_coe]
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).add_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma hereditary_imaginaryPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℑ x : A) ∈ hereditaryCarrier h := by
  rw [imaginaryPart_apply_coe]
  apply hereditary_complex_smul_mem
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).sub_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma trace_selfAdjoint_im_zero (τ : NormalizedTrace A) (x : A) (hx : IsSelfAdjoint x) :
    (τ.functional x).im = 0 := by
  have hp : (τ.functional x⁺).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.posPart_nonneg x))).2.symm
  have hq : (τ.functional x⁻).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.negPart_nonneg x))).2.symm
  have he := congrArg (fun a => (τ.functional a).im) (CFC.posPart_sub_negPart x hx)
  simpa only [map_sub, Complex.sub_im, hp, hq, sub_self] using he.symm

lemma trace_zero_selfadjoint_split (τ : NormalizedTrace A) (hsimple : TopologicallySimple A)
    (h x : A) (hh : 0 ≤ h) (hx : IsSelfAdjoint x) (hx0 : x ≠ 0)
    (hxm : x ∈ hereditaryCarrier h) (hτ : τ.functional x = 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  have heq : τ.functional (x⁺) = τ.functional (x⁻) := by
    apply sub_eq_zero.mp
    rw [← map_sub, CFC.posPart_sub_negPart x hx, hτ]
  have hp0 : x⁺ ≠ 0 := by
    intro hp
    have hq := τ.faithful hsimple _ (CFC.negPart_nonneg x) (by rw [← heq, hp, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  have hq0 : x⁻ ≠ 0 := by
    intro hq
    have hp := τ.faithful hsimple _ (CFC.posPart_nonneg x) (by rw [heq, hq, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  refine ⟨x⁺, x⁻, CFC.posPart_nonneg x, hp0, ?_,
    CFC.negPart_nonneg x, hq0, ?_, CFC.posPart_mul_negPart x⟩
  · change x⁺ ∈ hereditarySubalgebra h hh
    rw [CFC.posPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)
  · change x⁻ ∈ hereditarySubalgebra h hh
    rw [CFC.negPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)

theorem exists_orthogonal_pair_hereditary (τ : NormalizedTrace A)
    (hsimple : TopologicallySimple A) (hproj : Projectionless A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e*f=0 := by
  by_contra hno
  have hτh0 : τ.functional h ≠ 0 := fun hz => hh0 (τ.faithful hsimple h hh hz)
  have hτh : 0 < (τ.functional h).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hh) hτh0.symm)).1
  have hscalar (x : A) (hx : IsSelfAdjoint x) (hxm : x ∈ hereditaryCarrier h) :
      ∃ r : ℝ, x=r • h := by
    let r := (τ.functional x).re / (τ.functional h).re
    have hy : IsSelfAdjoint (x-r • h) := hx.sub ((IsSelfAdjoint.all r).smul hh.isSelfAdjoint)
    have hym : x-r • h ∈ hereditaryCarrier h :=
      (hereditarySubalgebra h hh).sub_mem hxm
        ((hereditarySubalgebra h hh).smul_mem r (self_mem_hereditary h hh))
    have hτy : τ.functional (x-r • h)=0 := by
      rw [map_sub,τ.functional.map_smul_of_tower]
      apply Complex.ext
      · simp only [Complex.sub_re,Complex.smul_re,Complex.zero_re]
        dsimp [r]
        exact sub_eq_zero.mpr (div_mul_cancel₀ _ (ne_of_gt hτh)).symm
      · simp only [Complex.sub_im,Complex.smul_im,Complex.zero_im,
          trace_selfAdjoint_im_zero τ x hx,trace_selfAdjoint_im_zero τ h hh.isSelfAdjoint,
          smul_zero,sub_zero]
    have hy0 : x-r • h=0 := by
      by_contra hy0
      exact hno (trace_zero_selfadjoint_split τ hsimple h _ hh hy hy0 hym hτy)
    exact ⟨r,sub_eq_zero.mp hy0⟩
  have hh2 : 0 ≤ h*h := by simpa only [hh.star_eq] using star_mul_self_nonneg h
  have hh20 : h*h ≠ 0 := by
    intro he
    apply hh0
    apply (CStarRing.star_mul_self_eq_zero_iff h).mp
    simpa only [hh.star_eq] using he
  obtain ⟨r,hr⟩ := hscalar (h*h) hh2.isSelfAdjoint
    ((hereditarySubalgebra h hh).mul_mem (self_mem_hereditary h hh) (self_mem_hereditary h hh))
  have ht0 : 0 < (τ.functional (h*h)).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hh2)
      (fun hz => hh20 (τ.faithful hsimple _ hh2 hz.symm)))).1
  have htr : (τ.functional (h*h)).re=r*(τ.functional h).re := by
    rw [hr,τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul]
  have hr0 : 0 < r := by
    rw [htr] at ht0
    exact pos_of_mul_pos_left ht0 hτh.le
  have hp : IsStarProjection (r⁻¹ • h) := {
    isSelfAdjoint := ((IsSelfAdjoint.all r⁻¹).smul hh.isSelfAdjoint)
    isIdempotentElem := by
      change (r⁻¹ • h)*(r⁻¹ • h)=r⁻¹ • h
      rw [smul_mul_assoc,mul_smul_comm,hr,smul_smul,smul_smul]
      congr 1
      field_simp }
  exact (smul_ne_zero (inv_ne_zero hr0.ne') hh0) (hproj _ hp)

end NonunitalGamma

end
end

end OAI
