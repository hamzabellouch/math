import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerToTracial

namespace OAI

noncomputable section


namespace DirectComparison
open Pureness
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def upperCut (δ : ℝ) (f : A) : A := δ⁻¹ • directPositiveCut (1-δ) f

omit [PartialOrder A] [StarOrderedRing A] in
lemma upperCut_cfc (δ : ℝ) (f : A) :
    upperCut δ f=cfc (fun t : ℝ => δ⁻¹*max (t-(1-δ)) 0) f := by
  rw [cfc_const_mul δ⁻¹ _ f (by fun_prop)]
  rfl

lemma upperCut_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (f : A) : 0 ≤ upperCut δ f :=
  smul_nonneg (inv_nonneg.mpr hδ) (directPositiveCut_nonneg _ _)

lemma upperCut_le_one {δ : ℝ} (hδ : 0<δ) (f : A) (hfn : ‖f‖ ≤ 1) :
    upperCut δ f ≤ 1 := by
  nontriviality A
  rw [upperCut_cfc]
  apply cfc_le_one
  intro t ht
  have ht1 : t ≤ 1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans hfn
  apply (inv_mul_le_iff₀ hδ).mpr
  exact max_le (by linarith) (by positivity)

lemma upperCut_norm_le {δ : ℝ} (hδ : 0<δ) (f : A) (hfn : ‖f‖ ≤ 1) :
    ‖upperCut δ f‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (upperCut_nonneg hδ.le f)).mpr
    (upperCut_le_one hδ f hfn)

lemma upperCut_support_error {δ : ℝ} (hδ : 0<δ) (f : A)
    (hf : 0 ≤ f) (hfn : ‖f‖ ≤ 1) : ‖f*upperCut δ f-upperCut δ f‖ ≤ δ := by
  nontriviality A using hδ.le
  have he : f*upperCut δ f-upperCut δ f=
      cfc (fun t : ℝ => t*(δ⁻¹*max (t-(1-δ)) 0)-δ⁻¹*max (t-(1-δ)) 0) f := by
    rw [cfc_sub (fun t : ℝ => t*(δ⁻¹*max (t-(1-δ)) 0))
      (fun t : ℝ => δ⁻¹*max (t-(1-δ)) 0) f (by fun_prop) (by fun_prop),
      cfc_mul (fun t : ℝ => t) (fun t : ℝ => δ⁻¹*max (t-(1-δ)) 0) f
        continuousOn_id (by fun_prop),cfc_id' ℝ f hf.isSelfAdjoint,←upperCut_cfc]
  rw [he]
  apply norm_cfc_le hδ.le
  intro t ht
  have ht1 : t ≤ 1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans hfn
  have hq0 : 0 ≤ δ⁻¹*max (t-(1-δ)) 0 := mul_nonneg (inv_nonneg.mpr hδ.le) (le_max_right _ _)
  have hq1 : δ⁻¹*max (t-(1-δ)) 0 ≤ 1 := by
    apply (inv_mul_le_iff₀ hδ).mpr
    exact max_le (by linarith) (by positivity)
  rw [Real.norm_eq_abs,abs_le]
  by_cases h : t ≤ 1-δ
  · rw [max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero,sub_self]
    exact ⟨by linarith,hδ.le⟩
  · constructor
    · nlinarith [mul_nonneg (by linarith : 0 ≤ t-(1-δ)) hq0,
        mul_nonneg hδ.le (sub_nonneg.mpr hq1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hq0]

lemma upperCut_trace_lower (τ : TracialState A) {δ : ℝ} (hδ : 0<δ)
    (f : A) (hf : 0 ≤ f) (hfn : ‖f‖ ≤ 1) :
    (τ.functional f).re-(τ.functional (f-f*f)).re/δ ≤ (τ.functional (upperCut δ f)).re := by
  have : Nontrivial A := ⟨⟨0,1,fun h => by
    have he := congrArg τ.functional h
    simp only [map_zero,τ.normalized,zero_ne_one] at he⟩⟩
  have he : δ • f-(f-f*f) ≤ directPositiveCut (1-δ) f := by
    have hid : δ • f-(f-f*f)=cfc (fun t : ℝ => δ*t-(t-t*t)) f := by
      rw [cfc_sub (fun t : ℝ => δ*t) (fun t : ℝ => t-t*t) f (by fun_prop) (by fun_prop),
        cfc_const_mul_id δ f hf.isSelfAdjoint,
        cfc_sub (fun t : ℝ => t) (fun t : ℝ => t*t) f continuousOn_id (by fun_prop),
        cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) f continuousOn_id continuousOn_id,
        cfc_id' ℝ f hf.isSelfAdjoint]
    rw [hid]
    apply cfc_mono (hf := by fun_prop) (hg := by fun_prop)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg hf ht
    have ht1 : t ≤ 1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans hfn
    change δ*t-(t-t*t) ≤ max (t-(1-δ)) 0
    by_cases hcut : t ≤ 1-δ
    · exact (show δ*t-(t-t*t) ≤ 0 by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hcut)]).trans (le_max_right _ _)
    · apply (le_max_left _ _).trans'
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_of_not_ge hcut))]
  have ht := (τ.functional.monotone he).1
  change (τ.functional (δ • f-(f-f*f))).re ≤ (τ.functional (directPositiveCut (1-δ) f)).re at ht
  simp only [map_sub,τ.functional.map_smul_of_tower,Complex.sub_re,Complex.smul_re,smul_eq_mul] at ht
  simp only [upperCut,τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul]
  rw [inv_mul_eq_div]
  simp only [map_sub,Complex.sub_re]
  apply (le_div_iff₀ hδ).mpr
  field_simp
  nlinarith

end DirectComparison


namespace DirectComparison
open Pureness CurrentMain
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_positive_sandwich_le (τ : TracialState A) (u x : A) (hu : 0 ≤ u) :
    (τ.functional (star x*u*x)).re ≤ ‖x‖^2*(τ.functional u).re := by
  let r := CFC.sqrt u
  have hr : star r=r := (CFC.sqrt_nonneg u).isSelfAdjoint.star_eq
  have hr2 : r*r=u := CFC.sqrt_mul_sqrt_self u hu
  have h1 : traceTwoNorm τ r^2=(τ.functional u).re := by
    rw [traceTwoNorm_sq,hr,hr2]
  have h2 : traceTwoNorm τ (r*x)^2=(τ.functional (star x*u*x)).re := by
    rw [traceTwoNorm_sq,star_mul,hr]
    congr 2
    calc
      star x*r*(r*x)=star x*(r*r)*x := by simp only [mul_assoc]
      _=star x*u*x := by rw [hr2]
  have h := traceTwoNorm_mul_right τ x r
  have hn1 := traceTwoNorm_nonneg τ (r*x)
  have hn2 := traceTwoNorm_nonneg τ r
  have hc : 0 ≤ ‖x‖*traceTwoNorm τ r := mul_nonneg (norm_nonneg _) hn2
  have hsq : traceTwoNorm τ (r*x)^2 ≤ (‖x‖*traceTwoNorm τ r)^2 :=
    (sq_le_sq₀ hn1 hc).mpr h
  rw [mul_pow,h1,h2] at hsq
  exact hsq

lemma trace_sub_real_le_norm (τ : TracialState A) (a b : A) :
    (τ.functional a).re-(τ.functional b).re ≤ ‖a-b‖ := by
  rw [←Complex.sub_re,←map_sub]
  exact (Complex.re_le_norm _).trans (trace_norm_le_norm τ _)

omit [PartialOrder A] [StarOrderedRing A] in
lemma compression_swap_error (c t x : A) :
    ‖t*(star x*c*x)*t-star x*(t*c*t)*x‖ ≤
      ‖t*star x-star x*t‖*‖c*x*t‖+
      ‖star x*t*c‖*‖x*t-t*x‖ := by
  have he : t*(star x*c*x)*t-star x*(t*c*t)*x=
      (t*star x-star x*t)*(c*x*t)+(star x*t*c)*(x*t-t*x) := by noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

theorem trace_full_frame_compression {I : Type*} [Fintype I]
    (τ : TracialState A) (c t : A) (hc : 0 ≤ c) (ht : IsSelfAdjoint t)
    (x : I → A) (hframe : ∑ i,star (x i)*c*x i=1) :
    (τ.functional (t*t)).re ≤
      (∑ i,‖x i‖^2)*(τ.functional (t*c*t)).re+
      ∑ i,(‖t*star (x i)-star (x i)*t‖*‖c*x i*t‖+
        ‖star (x i)*t*c‖*‖x i*t-t*x i‖) := by
  have htrace : (τ.functional (t*t)).re=
      ∑ i,(τ.functional (t*(star (x i)*c*x i)*t)).re := by
    rw [←Complex.re_sum,←map_sum,←Finset.sum_mul,←Finset.mul_sum,hframe,mul_one]
  rw [htrace,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hpos : 0 ≤ t*c*t := ht.conjugate_nonneg hc
  have hs := trace_positive_sandwich_le τ (t*c*t) (x i) hpos
  have he := (trace_sub_real_le_norm τ (t*(star (x i)*c*x i)*t)
    (star (x i)*(t*c*t)*x i)).trans (compression_swap_error c t (x i))
  linarith

end DirectComparison


namespace DirectComparison
open Pureness CurrentMain
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 def hereditaryUpperCut (δ : ℝ) (f c : A) : A := c*upperCut δ f*c

 lemma hereditaryUpperCut_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (f c : A)
    (hc : IsSelfAdjoint c) : 0 ≤ hereditaryUpperCut δ f c :=
  hc.conjugate_nonneg (upperCut_nonneg hδ f)

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma norm_contractive_sandwich (c a : A) (hc : ‖c‖ ≤ 1) : ‖c*a*c‖ ≤ ‖a‖ := by
  calc
    _ ≤ (‖c‖*‖a‖)*‖c‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖a‖*‖c‖ := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg a) hc) (norm_nonneg c)
    _ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg a) hc

 lemma hereditaryUpperCut_norm_le {δ : ℝ} (hδ : 0<δ) (f c : A)
    (hfn : ‖f‖ ≤ 1) (hcn : ‖c‖ ≤ 1) : ‖hereditaryUpperCut δ f c‖ ≤ 1 :=
  (norm_contractive_sandwich c _ hcn).trans (upperCut_norm_le hδ f hfn)

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma hereditaryUpperCut_support (δ : ℝ) (f c h : A) (hhc : h*c=c) :
    h*hereditaryUpperCut δ f c=hereditaryUpperCut δ f c := by
  dsimp [hereditaryUpperCut]
  simp only [←mul_assoc,hhc]

 lemma hereditaryUpperCut_error {δ : ℝ} (hδ : 0<δ) (f c : A)
    (hf : 0 ≤ f) (hfn : ‖f‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    ‖f*hereditaryUpperCut δ f c-hereditaryUpperCut δ f c‖ ≤ ‖f*c-c*f‖+δ := by
  have he : f*hereditaryUpperCut δ f c-hereditaryUpperCut δ f c=
      (f*c-c*f)*upperCut δ f*c+c*(f*upperCut δ f-upperCut δ f)*c := by
    dsimp [hereditaryUpperCut]; noncomm_ring
  rw [he]
  have h1 : ‖(f*c-c*f)*upperCut δ f*c‖ ≤ ‖f*c-c*f‖ := by
    have hq := upperCut_norm_le hδ f hfn
    calc
      _ ≤ (‖f*c-c*f‖*‖upperCut δ f‖)*‖c‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖f*c-c*f‖*‖upperCut δ f‖ := mul_le_of_le_one_right
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcn
      _ ≤ ‖f*c-c*f‖ := mul_le_of_le_one_right (norm_nonneg _) hq
  exact (norm_add_le _ _).trans (add_le_add h1
    ((norm_contractive_sandwich c _ hcn).trans (upperCut_support_error hδ f hf hfn)))

 lemma hereditaryUpperCut_trace (τ : TracialState A) {δ : ℝ} (hδ : 0 ≤ δ) (f c : A) :
    (τ.functional (hereditaryUpperCut δ f c)).re=
      (τ.functional (CFC.sqrt (upperCut δ f)*(c*c)*CFC.sqrt (upperCut δ f))).re := by
  have ht := CFC.sqrt_mul_sqrt_self (upperCut δ f) (upperCut_nonneg hδ f)
  congr 1
  calc
    τ.functional (hereditaryUpperCut δ f c)=τ.functional ((c*c)*upperCut δ f) := by
      dsimp [hereditaryUpperCut]
      rw [τ.tracial (c*upperCut δ f) c,mul_assoc]
    _=τ.functional (CFC.sqrt (upperCut δ f)*(c*c)*CFC.sqrt (upperCut δ f)) := by
      rw [τ.tracial (CFC.sqrt (upperCut δ f)*(c*c)) (CFC.sqrt (upperCut δ f)),←mul_assoc,ht]
      exact τ.tracial _ _

 theorem hereditaryUpperCut_trace_lower {I : Type*} [Fintype I]
    (τ : TracialState A) {δ : ℝ} (hδ : 0<δ) (f c : A)
    (hf : 0 ≤ f) (hfn : ‖f‖ ≤ 1) (hc : IsSelfAdjoint c) (x : I → A)
    (hframe : ∑ i,star (x i)*(c*c)*x i=1) :
    (τ.functional f).re-(τ.functional (f-f*f)).re/δ ≤
      (∑ i,‖x i‖^2)*(τ.functional (hereditaryUpperCut δ f c)).re+
        ∑ i,(‖CFC.sqrt (upperCut δ f)*star (x i)-star (x i)*CFC.sqrt (upperCut δ f)‖*
          ‖(c*c)*x i*CFC.sqrt (upperCut δ f)‖+
          ‖star (x i)*CFC.sqrt (upperCut δ f)*(c*c)‖*
          ‖x i*CFC.sqrt (upperCut δ f)-CFC.sqrt (upperCut δ f)*x i‖) := by
  have hs : 0 ≤ c*c := by simpa only [hc.star_eq] using star_mul_self_nonneg c
  have ht := trace_full_frame_compression τ (c*c) (CFC.sqrt (upperCut δ f)) hs
    (CFC.sqrt_nonneg _).isSelfAdjoint x hframe
  rw [CFC.sqrt_mul_sqrt_self _ (upperCut_nonneg hδ.le f),←hereditaryUpperCut_trace τ hδ.le f c] at ht
  exact (upperCut_trace_lower τ hδ f hf hfn).trans ht

end DirectComparison

end

end OAI
