import Mathlib
import OAI.Geometry.CubicTorus.Profiles.CornerGrid381

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

theorem secondCorner_endpoint_contradiction {A h b r s : ℝ}
    (hA0 : 0<A) (hA : A≤1) (hh : 0≤h)
    (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0≤r) (hr1 : r≤1/Real.pi)
    (hs1 : s≤1)
    (htop : Real.sqrt (Real.pi*r)≤A*b-h*(1/Real.pi-r))
    (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-1/Real.pi))
    (hdrop : s-r≤A*Real.sqrt (1-b))
    (hbmax : 2/3≤b) (hxcap : h*A≤7/4) : False := by
  let a : ℝ := 1
  let x := h*A
  let d := Real.sqrt (1-b)
  let w := Real.sqrt (Real.pi*r)/a
  have ha : 0<a := by dsimp [a]; positivity
  have hp : Real.pi≠0 := Real.pi_pos.ne'
  have hva : 1/Real.pi=a^2/Real.pi := by norm_num [a]
  have haA : A≤a := hA
  have hx0 : 0≤x := mul_nonneg hh hA0.le
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hd2 : d^2=1-b := Real.sq_sqrt (by linarith)
  have hw0 : 0≤w := div_nonneg (Real.sqrt_nonneg _) ha.le
  have haw : a*w=Real.sqrt (Real.pi*r) := by dsimp only [w]; field_simp
  have hrw : r=a^2*w^2/Real.pi := by
    have hz := Real.sq_sqrt (mul_nonneg Real.pi_pos.le hr0)
    rw [← haw,mul_pow] at hz
    apply (eq_div_iff hp).mpr
    nlinarith only [hz]
  have hw1 : w≤1 := by
    rw [hva,hrw] at hr1
    have hz := (div_le_div_iff_of_pos_right Real.pi_pos).mp hr1
    have ha2 := sq_pos_of_pos ha
    have hw2' : w^2≤1 := (mul_le_mul_iff_right₀ ha2).mp (by simpa only [mul_one] using hz)
    nlinarith only [hw2',hw0]
  have hw2 : 0≤1-w^2 := by nlinarith
  have hxn : x≤h*a := mul_le_mul_of_nonneg_left haA hh
  have hnorm : w+x/Real.pi*(1-w^2)≤b := by
    have hleft := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hxn Real.pi_pos.le) hw2
    have hleft' := mul_le_mul_of_nonneg_left (add_le_add (le_refl w) hleft) ha.le
    have ht : a*(w+h*a/Real.pi*(1-w^2))≤A*b := by
      have hid : a*(w+h*a/Real.pi*(1-w^2))=a*w+h*(1/Real.pi-r) := by
        rw [hva,hrw]
        ring
      rw [hid,haw]
      linarith only [htop]
    have hright := mul_le_mul_of_nonneg_right haA hb0
    exact (mul_le_mul_iff_right₀ ha).mp (hleft'.trans (ht.trans hright))
  let f : ℝ → ℝ := fun t => t+x/Real.pi*(1-t^2)
  have hf : Continuous f := by fun_prop
  have hf1 : f 1=1 := by dsimp [f]; ring
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hw1 hf.continuousOn
    (show b∈Icc (f w) (f 1) from ⟨hnorm,by rw [hf1]; exact hb1.le⟩)
  have ht0 : 0≤t := hw0.trans ht.1
  have ht1 : t<1 := by
    by_contra hn
    have he : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [he,hf1] at hft
    linarith
  have htden : 0<1-t^2 := by nlinarith
  have hroot : t+x/Real.pi*(1-t^2)=b := hft
  have hxterm : 0≤x/Real.pi*(1-t^2) := by positivity
  have htd : t+d^2≤1 := by linarith only [hroot,hxterm,hd2]
  have hxroot : x=Real.pi*(1-t-d^2)/(1-t^2) := by
    apply (eq_div_iff htden.ne').mpr
    have he := congrArg (fun y : ℝ => y*Real.pi) hroot
    field_simp at he
    rw [show 1-t-d^2=b-t by linarith only [hd2]]
    nlinarith only [he]
  have hwtsq : w^2≤t^2 := (sq_le_sq₀ hw0 ht0).mpr ht.1
  have hrbound : r≤a^2*t^2/Real.pi := by
    rw [hrw]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwtsq (sq_nonneg a)) Real.pi_pos.le
  have hEt : A*b-h*(1/Real.pi-a^2*t^2/Real.pi)≤a*t := by
    have he : A*b-h*(1/Real.pi-a^2*t^2/Real.pi)=
        A*t+(h/Real.pi)*(A^2-a^2)*(1-t^2) := by
      rw [hva,← hroot]
      dsimp only [x]
      ring
    have hA2 : A^2≤a^2 := (sq_le_sq₀ hA0.le ha.le).mpr haA
    have hcorr : (h/Real.pi)*(A^2-a^2)*(1-t^2)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hh Real.pi_pos.le) (sub_nonpos.mpr hA2)) htden.le
    rw [he]
    have hat := mul_le_mul_of_nonneg_right haA ht0
    linarith only [hcorr,hat]
  have hsb : s≤a^2*t^2/Real.pi+a*d := by
    have hAd := mul_le_mul_of_nonneg_right haA hd0
    linarith only [hdrop,hrbound,hAd]
  have hbottom' : Real.sqrt (Real.pi*(1-s))≤a*t+x*d := by
    have hdiff := mul_le_mul_of_nonneg_left hdrop hh
    have hrr := mul_le_mul_of_nonneg_left hrbound hh
    have hxd : h*(A*d)=x*d := by dsimp [x]; ring
    rw [hxd] at hdiff
    linarith only [hbottom,hdiff,hrr,hEt]
  have hbsq : Real.pi*(1-s)≤(a*t+x*d)^2 := by
    have hy : 0≤a*t+x*d := by positivity
    have hh' := (sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*(1-s))) hy).mpr hbottom'
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by linarith : 0≤1-s))] at hh'
  have hnec : 1≤a*d+(a^2*t^2+(a*t+x*d)^2)/Real.pi := by
    have hh' := mul_le_mul_of_nonneg_left hsb Real.pi_pos.le
    have hcancel : Real.pi*(a^2*t^2/Real.pi+a*d)=a^2*t^2+Real.pi*a*d := by field_simp
    rw [hcancel] at hh'
    have hh2 : 1≤((a*d)*Real.pi+(a^2*t^2+(a*t+x*d)^2))/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith only [hh',hbsq])
    simpa only [add_div,mul_div_cancel_right₀ _ hp] using hh2
  have hd3 : d^2≤1/3 := by linarith only [hd2,hbmax]
  have hroot' : Real.pi*(1-t-d^2)=x*(1-t^2) := by
    exact ((eq_div_iff htden.ne').mp hxroot).symm
  have hstrict := corner_root_strict (show CornerRootData t d x from
    ⟨ht0,ht1,hd0,hd3,hx0,hxcap,hroot'⟩)
  have hnec' : 1≤d+(t^2+(t+x*d)^2)/Real.pi := by
    simpa only [a,one_mul,one_pow] using hnec
  exact (not_lt_of_ge hnec') hstrict

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_second_transition_corner_excluded
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (1/Real.pi) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (hw0 : 2/3≤axialFluxWeight μ 0) (hw1 : axialFluxWeight μ 0<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : False := by
  have hvh := secondTransition_mem_Ioo_half
  have hV : 1/Real.pi∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier hV hE hm hμ
  obtain ⟨hA,_,hA1,hh,hr,hrV,_,hs1,hb,_,htop,hbottom,hdrop⟩ :=
    isMinimizerAt_four_corner_necessary_data hvh hE hm hμ hN hp ha hs hsg hH ht1 ht2 hb1 hb2
  exact secondCorner_endpoint_contradiction hA hA1 hh hb hw1 hr hrV hs1 htop hbottom hdrop hw0
    (isMinimizerAt_second_endpoint_linear_bound hE hm hμ hH).le

theorem isMinimizerAt_second_transition_standard {E : Set Torus}
    (hmE : IsMinimizerAt (1/Real.pi) E) : SmallStandardRegion (1/Real.pi) E := by
  by_contra hnstd
  obtain ⟨F,μ,N,hN,hp,c,H,hF,hm,hμ,ha,hs,hsg,hH,hws,hw,haxis,hface⟩ :=
    isMinimizerAt_second_transition_nonstandard_star hmE hnstd
  obtain ⟨i,hi⟩ : ∃ i : Fin 3,2/3≤axialFluxWeight μ i := by
    by_contra! hn
    rw [Fin.sum_univ_three] at hws
    linarith [hn 0,hn 1,hn 2]
  classical
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have he0 : e.symm 0=i := by simp [e]
  have he1 : e.symm 1≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have he2 : e.symm 2≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have hpair (j : Fin 3) : ((fun k : Fin 3 => decide (k=0 ∨ k=j)) ∘ e)=
      (fun k => decide (k=i ∨ k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply,he0]
  have hsingle (j : Fin 3) : ((fun k : Fin 3 => decide (k=j)) ∘ e)=
      (fun k => decide (k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply]
  have ht (j : Fin 3) (hj : j≠i) :
      quotientMap (chamberVertex c (fun k => decide (k=i ∨ k=j)))∉openRepresentative F := by
    obtain ⟨k,hk⟩ := fin3_pair_complement i j hj.symm
    rw [hk]
    exact fun h => hface k (subset_closure h)
  have hv (b : Fin 3 → Bool) :
      quotientMap (chamberVertex (c ∘ e.symm) b)∈openRepresentative (torusCoordinatePermute e ⁻¹' F) ↔
      quotientMap (chamberVertex c (b ∘ e))∈openRepresentative F := by
    rw [openRepresentative_coordinatePermute hF e]
    change torusCoordinatePermute e (quotientMap (chamberVertex (c ∘ e.symm) b))∈openRepresentative F ↔ _
    rw [← quotientMap_coordinatePermute,chamberVertex_coordinatePermute]
  apply isMinimizerAt_second_transition_corner_excluded
    ((torusCoordinatePermute e).continuous.measurable hF) (isMinimizerAt_coordinatePermute hm e)
    (isNormalMeasure_coordinatePermute hF hμ e)
    (coordinatePermutedField_contDiff e hN) (coordinatePermutedField_periodic e hp)
    (permuted_normal_ae hN.continuous hp ha e) (reflection_invariant_coordinatePermute hs e)
    (chamberSign_coordinatePermute hF hsg e)
  · simpa [axialFluxWeight_permute,e] using hi
  · rw [axialFluxWeight_permute]
    exact (hw _).2
  · rw [hv,hpair]
    exact ht _ he1
  · rw [hv,hpair]
    exact ht _ he2
  · rw [hv,hsingle]
    exact haxis _
  · rw [hv,hsingle]
    exact haxis _
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isoperimetricProfile_second_transition :
    isoperimetricProfile (1/Real.pi)=1 := by
  have hV := secondTransition_mem_Ioo_half
  obtain ⟨E,hm⟩ := exists_isMinimizerAt (show 1/Real.pi∈Ioo (0 : ℝ) 1 from
    ⟨hV.1,by linarith [hV.2]⟩)
  have hs := isMinimizerAt_second_transition_standard hm
  have hP := (hs.bv_data ⟨hV.1,hV.2.le⟩).2.2
  rw [candidateProfile_slab (show 1/Real.pi∈Icc TwoVolume.V₂ (1-TwoVolume.V₂) from
    ⟨le_rfl,by change 1/Real.pi≤1-1/Real.pi; linarith [hV.2]⟩)] at hP
  rw [isoperimetricProfile_eq_of_isMinimizerAt hm,hP,ENNReal.toReal_ofReal (by positivity)]
  norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cylinderRatio (V : ℝ) : ℝ := isoperimetricProfile V/Real.sqrt V

lemma profile_ge_second_chord {V : ℝ} (hV : V∈Icc (0 : ℝ) (1/Real.pi)) :
    Real.pi*V ≤ isoperimetricProfile V := by
  have hv2 := secondTransition_mem_Ioo_half
  have hvp : V*Real.pi≤1 := (le_div_iff₀ Real.pi_pos).mp hV.2
  have hh := concaveOn_isoperimetricProfile.2
    (show (0 : ℝ)∈Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show 1/Real.pi∈Icc (0 : ℝ) 1 from ⟨hv2.1.le,by linarith [hv2.2]⟩)
    (show 0≤1-V*Real.pi by linarith) (show 0≤V*Real.pi from mul_nonneg hV.1 Real.pi_pos.le)
    (show (1-V*Real.pi)+V*Real.pi=1 by ring)
  have he : (1-V*Real.pi)*0+V*Real.pi*(1/Real.pi)=V := by field_simp; ring
  simp only [smul_eq_mul,isoperimetricProfile_zero,isoperimetricProfile_second_transition,
    mul_zero,mul_one,zero_add] at hh
  simpa only [mul_assoc,mul_one_div_cancel Real.pi_pos.ne',mul_one,mul_comm] using hh

lemma cylinder_contact_support_deriv {V : ℝ} (hV : 0<V)
    (hc : IsLocalMin cylinderRatio V) {C : ℝ → ℝ}
    (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    deriv C V=isoperimetricProfile V/(2*V) := by
  have hloc : IsLocalMin (fun W => C W/Real.sqrt W) V := by
    filter_upwards [hc,hs.above,Ioi_mem_nhds hV] with W hW hab hpos
    change C V/Real.sqrt V≤C W/Real.sqrt W
    rw [hs.contact]
    exact hW.trans (div_le_div_of_nonneg_right hab (Real.sqrt_nonneg _))
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt.div
    (Real.hasDerivAt_sqrt hV.ne') (Real.sqrt_ne_zero'.mpr hV)
  have hz := hloc.hasDerivAt_eq_zero hd
  rw [hs.contact] at hz
  have hq : (Real.sqrt V)^2=V := Real.sq_sqrt hV.le
  have hn : Real.sqrt V≠0 := Real.sqrt_ne_zero'.mpr hV
  field_simp [hn] at hz
  apply (eq_div_iff (by positivity : 2*V≠0)).mpr
  rw [hq] at hz
  nlinarith only [hz]

theorem isMinimizerAt_cylinder_contact_multiplier {V : ℝ} (hV : V∈Ioo 0 1)
    (hc : IsLocalMin cylinderRatio V) {E : Set Torus}
    (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    (H/2)*V=((perimeter E).toReal/2)/2 := by
  obtain ⟨N,C,hN,hp,ha,hs,hd,_⟩ := Periodic.profile_hessian_of_CMC hV hE hm hμ
    (fun _ hF hpF => Periodic.weakCMC_identity hμ hH hF hpF)
  have hh := cylinder_contact_support_deriv hV.1 hc hs
  rw [hd,isoperimetricProfile_eq_of_isMinimizerAt hm] at hh
  have he := (eq_div_iff (ne_of_gt (mul_pos (by norm_num : (0 : ℝ)<2) hV.1))).mp hh
  nlinarith only [he]

theorem isMinimizerAt_cylinder_contact_bounds {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    (hc : IsLocalMin cylinderRatio V) {E : Set Torus}
    (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    let A := (perimeter E).toReal/2
    let h := H/2
    0<A ∧ A≤1 ∧ h*V=A/2 ∧ Real.pi/2≤h ∧ h*A≤Real.pi/2 := by
  have hv1 := firstTransition_mem_Ioo_half
  have hv2 := secondTransition_mem_Ioo_half
  have hv : V∈Ioo (0 : ℝ) 1 := ⟨hv1.1.trans_le hV.1,lt_of_le_of_lt hV.2 (by change 1/Real.pi<1; linarith [hv2.2])⟩
  let A := (perimeter E).toReal/2
  let h := H/2
  have hpos : 0<A := by dsimp only [A]; rw [←isoperimetricProfile_eq_of_isMinimizerAt hm]; exact isoperimetricProfile_pos hv
  have hA1 : A≤1 := isMinimizerAt_perimeter_half_le_one hv hm
  have he : h*V=A/2 := isMinimizerAt_cylinder_contact_multiplier hv hc hE hm hμ hH
  have hlow := profile_ge_second_chord (show V∈Icc (0 : ℝ) (1/Real.pi) from ⟨hv.1.le,hV.2⟩)
  rw [isoperimetricProfile_eq_of_isMinimizerAt hm] at hlow
  change Real.pi*V≤A at hlow
  have hh : Real.pi/2≤h := by
    apply (mul_le_mul_iff_left₀ hv.1).mp
    change Real.pi/2*V≤h*V
    rw [he]
    linarith only [hlow]
  have hupper := isoperimetricProfile_le_candidate ⟨hv.1.le,hv.2.le⟩
  rw [candidateProfile_tube hV,isoperimetricProfile_eq_of_isMinimizerAt hm] at hupper
  change A≤2*Real.sqrt (Real.pi*V)/2 at hupper
  have hsq := Real.sq_sqrt (show 0≤Real.pi*V from mul_nonneg Real.pi_pos.le hv.1.le)
  have hA2 : A^2≤Real.pi*V := by nlinarith [Real.sqrt_nonneg (Real.pi*V)]
  have hcap : h*A≤Real.pi/2 := by
    apply (mul_le_mul_iff_left₀ hv.1).mp
    nlinarith only [hA2,congrArg (fun x : ℝ => x*A) he]
  exact ⟨hpos,hA1,he,hh,hcap⟩

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

def criticalCorrection (h : ℝ) : ℝ := (49/50 : ℝ)/Real.pi*h+(51*Real.pi/200)*h⁻¹-1

lemma criticalCorrection_convex : ConvexOn ℝ (Ioi 0) criticalCorrection := by
  have hi : ConvexOn ℝ (Ioi (0 : ℝ)) (fun h : ℝ => h⁻¹) := by
    simpa using (strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)).convexOn
  refine ⟨convex_Ioi 0,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := mul_le_mul_of_nonneg_left (hi.2 hx hy ha hb hab) (show 0≤51*Real.pi/200 by positivity)
  simp only [smul_eq_mul] at hh ⊢
  unfold criticalCorrection
  nlinarith only [hh,hab]

lemma criticalCorrection_nonpos {h : ℝ} (hl : Real.pi/2≤h) (hu : h≤81/50) :
    criticalCorrection h≤0 := by
  have hp : 0<h := lt_of_lt_of_le (by positivity : 0<Real.pi/2) hl
  have hupper : h≤51*Real.pi/98 := by linarith [Real.pi_gt_d4]
  have hf := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (sub_nonpos.mpr hupper)
  have he : criticalCorrection h*(Real.pi*h)=
      (49/50 : ℝ)*(h-Real.pi/2)*(h-51*Real.pi/98) := by
    unfold criticalCorrection
    field_simp
    ring
  have hn : criticalCorrection h*(Real.pi*h)≤0 := by rw [he, mul_assoc]; exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hf
  exact (mul_le_mul_iff_left₀ (mul_pos Real.pi_pos hp)).mp (by simpa using hn)

lemma criticalCorrection_rational_upper {h : ℝ} (hh : 0<h) :
    criticalCorrection h≤(49/50 : ℝ)/(3141592/1000000)*h+
      (51*(3141593/1000000)/200)*h⁻¹-1 := by
  have hpl : (3141592/1000000 : ℝ)≤Real.pi := by linarith [Real.pi_gt_d6]
  have hpu : Real.pi≤(3141593/1000000 : ℝ) := by linarith [Real.pi_lt_d6]
  have hl := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤49/50) (by norm_num) hpl) hh.le
  have hr := mul_le_mul_of_nonneg_right hpu (show 0≤(51/200 : ℝ)*h⁻¹ by positivity)
  unfold criticalCorrection
  nlinarith only [hl,hr]

lemma criticalCorrection_162 : criticalCorrection (81/50)≤-1/10000 := by
  have hh := criticalCorrection_rational_upper (h := 81/50) (by norm_num)
  norm_num at hh ⊢
  linarith
lemma criticalCorrection_170 : criticalCorrection (17/10)≤31/20000 := by
  have hh := criticalCorrection_rational_upper (h := 17/10) (by norm_num)
  norm_num at hh ⊢
  linarith
lemma criticalCorrection_190 : criticalCorrection (19/10)≤717/50000 := by
  have hh := criticalCorrection_rational_upper (h := 19/10) (by norm_num)
  norm_num at hh ⊢
  linarith

lemma critical_baseline_chord {a b x l r : ℝ} (ha : 0<a) (hab : a<b)
    (hx : x∈Icc a b)
    (hl : l≤nestingBaseline a-criticalCorrection a)
    (hr : r≤nestingBaseline b-criticalCorrection b) :
    min l r-(b-a)^2/(4*a^2)≤nestingBaseline x-criticalCorrection x := by
  have hc := criticalCorrection_convex.subset (show Icc a b⊆Ioi 0 from fun y hy => ha.trans_le hy.1) (convex_Icc a b)
  have hf : ConcaveOn ℝ (Icc a b)
      (fun h => nestingBaseline h-criticalCorrection h-(1/a^2)*h^2) := by
    apply ((ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected (b := b) ha).sub hc).congr
    intro y hy
    dsimp only [Pi.sub_apply]
    rw [nestingBaseline_eq_reused (ha.trans_le hy.1)]
    ring
  have hb := ReusedScalar205.CubicTorus.Scalar.semiconcave_chord_bound hab
    (show 0≤(1 : ℝ)/a^2 by positivity) hf hx
  have hm := min_le_min hl hr
  have he : (1/a^2)*(b-a)^2/4=(b-a)^2/(4*a^2) := by ring
  rw [he] at hb
  linarith

lemma critical_baseline_positive {h : ℝ} (hh : h∈Icc (81/50 : ℝ) (19/10)) :
    0<nestingBaseline h-criticalCorrection h := by
  have hl : (978/1000000 : ℝ)≤nestingBaseline (81/50)-criticalCorrection (81/50) := by
    rw [nestingBaseline_eq_reused (by norm_num)]
    linarith [ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_162,criticalCorrection_162]
  have hm : (3829/1000000 : ℝ)≤nestingBaseline (17/10)-criticalCorrection (17/10) := by
    rw [nestingBaseline_eq_reused (by norm_num)]
    linarith [ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_170,criticalCorrection_170]
  have hr : (8423/1000000 : ℝ)≤nestingBaseline (19/10)-criticalCorrection (19/10) := by
    rw [nestingBaseline_eq_reused (by norm_num)]
    linarith [ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_190,criticalCorrection_190]
  by_cases hmidh : h≤17/10
  · have hb := critical_baseline_chord (by norm_num) (by norm_num) ⟨hh.1,hmidh⟩ hl hm
    have hp : (0 : ℝ) < min (978/1000000 : ℝ) (3829/1000000)-((17/10 : ℝ)-81/50)^2/(4*(81/50 : ℝ)^2) := by norm_num
    exact hp.trans_le hb
  · have hb := critical_baseline_chord (by norm_num) (by norm_num) ⟨(lt_of_not_ge hmidh).le,hh.2⟩ hm hr
    have hp : (0 : ℝ) < min (3829/1000000 : ℝ) (8423/1000000)-((19/10 : ℝ)-17/10)^2/(4*(17/10 : ℝ)^2) := by norm_num
    exact hp.trans_le hb

theorem critical_nesting_contradiction {h : ℝ} (hh : h∈Icc (Real.pi/2) (19/10))
    (hB : nestingBaseline h≤criticalCorrection h)
    (hBS : h≤81/50 →nestingBaseline h+nestingGainInfimum h≤criticalCorrection h) : False := by
  by_cases hm : h≤81/50
  · have hp := nesting_scalar_positive.2 h ⟨by linarith [hh.1,Real.pi_gt_three],hm⟩
    have hd := criticalCorrection_nonpos hh.1 hm
    have hb := hBS hm
    linarith
  · have hp := critical_baseline_positive ⟨(lt_of_not_ge hm).le,hh.2⟩
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma critical_three_vertex_parameters {h s A : ℝ}
    (hh : Real.pi/2 ≤ h) (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hcap : h*A ≤ Real.pi/2) (hp : s^2 ≤ A^2/2)
    (hd : Real.pi*(1-s) ≤ (h*s)^2) : h ≤ 19/10 ∧ Shape.t h ≤ s := by
  have hh0 : 0<h := lt_of_lt_of_le (by positivity : 0<Real.pi/2) hh
  have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg h)
  have hsq := (sq_le_sq₀ (mul_nonneg hh0.le hA) (by positivity : 0 ≤ Real.pi/2)).mpr hcap
  have hhs : 8*(h*s)^2 ≤ Real.pi^2 := by nlinarith only [hmul,hsq]
  have hpi : Real.pi<22/7 := Real.pi_lt_d4.trans (by norm_num)
  have hslo : 3/5 ≤ s := by
    have hh' := mul_lt_mul_of_pos_left hpi Real.pi_pos
    have hp0 : 0<Real.pi := Real.pi_pos
    nlinarith only [hhs,hd,hh',hp0]
  have hs2 : (3/5 : ℝ)^2 ≤ s^2 := (sq_le_sq₀ (by norm_num) hs).mpr hslo
  have hm := mul_le_mul_of_nonneg_left hs2 (sq_nonneg h)
  have hpi2 := (sq_le_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 22/7)).mpr hpi.le
  exact ⟨by nlinarith only [hhs,hm,hpi2,hh0], source_root_le_of_bottom hh0 hs hd⟩

lemma critical_area_correction {A h V : ℝ} (hh : 0<h)
    (he : h*V=A/2) (hcap : h*A ≤ Real.pi/2) :
    Nesting.lambda*h/Real.pi+A-Nesting.lambda*h*V-1 ≤ criticalCorrection h := by
  have ha : A ≤ (Real.pi/2)*h⁻¹ := by
    rw [←div_eq_mul_inv]
    exact (le_div_iff₀ hh).mpr (by nlinarith only [hcap])
  have hmul : Nesting.lambda*h*V=Nesting.lambda*(A/2) := by rw [mul_assoc,he]
  rw [hmul]
  unfold Nesting.lambda criticalCorrection
  simp only [div_eq_mul_inv] at ha ⊢
  nlinarith only [ha]

theorem isMinimizerAt_cylinder_contact_not_three_vertices {V : ℝ}
    (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) (hcontact : IsLocalMin cylinderRatio V)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (haxes : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) : False := by
  have hv1 := firstTransition_mem_Ioo_half
  have hv2 := secondTransition_mem_Ioo_half
  have hv' : V∈Ioo (0 : ℝ) 1 :=
    ⟨hv1.1.trans_le hV.1,lt_of_le_of_lt hV.2 (by change 1/Real.pi<1; linarith [hv2.2])⟩
  obtain ⟨hout,hin⟩ := isMinimizerAt_three_vertex_bottom hv' hmin hc hR b hd i hv haxes
  obtain ⟨_,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hv' hE hmin hR b hd hμ hCMC i ha hv hout (hin 0) (hin 1)
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  obtain ⟨hA0,hA1,he,hlo,hcap⟩ := isMinimizerAt_cylinder_contact_bounds hV hcontact hE hmin hμ hH
  have hproj := isMinimizerAt_missing_neighbor_projection hv' hE hmin hR b hd hμ hH i ha hv
  rw [he] at hproj
  have hp : _ ≤ ((perimeter E).toReal/2)^2/2 := hproj.trans_eq (by ring)
  obtain ⟨hhi,ht⟩ := critical_three_vertex_parameters hlo hA0.le measureReal_nonneg hcap hp hdisc
  have hH0 : 0 ≤ H/2 := by linarith [Real.pi_pos]
  have hcorr := critical_area_correction (lt_of_lt_of_le (by positivity : 0<Real.pi/2) hlo) he hcap
  have hflux := isMinimizerAt_missing_neighbor_sharp_area_flux hv' hE hmin hR b hd hμ (by linarith) hH i ha hv
  have hB : nestingBaseline (H/2) ≤ criticalCorrection (H/2) := by
    have hb := nestingBaseline_slack hH0 ht
    rw [show 2*(H/2)=H by ring] at hb
    have hn := mul_nonneg (show 0 ≤ Nesting.ell by norm_num [Nesting.ell]) (sub_nonneg.mpr ht)
    change Nesting.lambda*H*V+2*(∫ v in (0 : ℝ)..
      volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle)),sharpSectionWeight H v) ≤ (perimeter E).toReal at hflux
    nlinarith only [hb,hn,hflux,hcorr]
  apply critical_nesting_contradiction ⟨hlo,hhi⟩ hB
  intro hmid
  have hm : H/2∈Icc (51/50 : ℝ) (81/50) := ⟨by linarith [Real.pi_gt_three,hlo],hmid⟩
  have hg := isMinimizerAt_nesting_cubic_gain hv' hE hmin hR b hd hμ hCMC i ha hv hout (hin 0) (hin 1) hm
  have hb := nestingBaseline_slack hH0 ht
  have hs := nestingGainInfimum_actual_slack hH0 ht
  rw [show 2*(H/2)=H by ring] at hb
  dsimp only [nestingC0] at hs
  dsimp only at hg
  nlinarith only [hb,hs,hg,hcorr]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_cylinder_contact_nonstandard_star
    {V : ℝ} (hVrange : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    (hcontact : IsLocalMin cylinderRatio V)
    {E : Set Torus} (hmE : IsMinimizerAt V E)
    (hnstd : ¬SmallStandardRegion V E) :
    ∃ (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x)
      (c : Fin 3 → Bool) (H : ℝ),
      MeasurableSet F ∧ IsMinimizerAt V F ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ j : Fin 3,coordinateReflection j ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (j : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (∑ j : Fin 3,axialFluxWeight μ j)=2 ∧
      (∀ j : Fin 3,0≤axialFluxWeight μ j ∧ axialFluxWeight μ j<1) ∧
      (∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l=j)))∈openRepresentative F) ∧
      (∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l≠j)))∉closure (openRepresentative F)) := by
  have hv1 := firstTransition_mem_Ioo_half
  have hv2 := secondTransition_mem_Ioo_half
  have hvh : V∈Ioo (0 : ℝ) (1/2) := ⟨hv1.1.trans_le hVrange.1,hVrange.2.trans_lt hv2.2⟩
  have hV : V∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨v,F,μ,N,hN,hp,c,H,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,_,hws,hw,hvi,_⟩ :=
    isMinimizerAt_nonstandard_section_system ⟨hvh.1,hvh.2.le⟩ hmE hnstd
  have hnF : ¬SmallStandardRegion V F := fun h => hnstd (smallStandardRegion_of_translated he h)
  have hnstdF : ¬StandardRegionAt V F := by
    simpa only [StandardRegionAt,ite_eq_left hvh.2.le] using hnF
  have hR : ∀ i : Fin 3,F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) := by
    intro i
    rw [axisReflection_eq_coordinateReflection]
    exact (hs i).symm
  have hd := isMinimizerAt_chamber_upper_downset hV hF hm hμ hN hp ha hs hsg
  have heq (j : Fin 3) :
      quotientMap (orientedUpperVertex c (fun k => if k=j then true else false))=
        quotientMap (chamberVertex c (fun k => decide (k=j))) := by
    rw [quotient_orientedUpperVertex_eq]
    congr 2
  obtain ⟨i,hi⟩ := hvi
  have hiO : quotientMap (chamberVertex c (fun j => decide (j=i)))∈openRepresentative F :=
    mem_open_of_mem_closure_not_frontier (isOpen_openRepresentative F) hi
      (isMinimizerAt_reflection_vertex_excluded hV hF hm hμ hN hp ha hs
        (chamberVertex_sine_zero c _))
  have hcF : IsPreconnected (frontier (openRepresentative F)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV hm).resolve_right (fun h => hnstdF h.2.2)
  obtain ⟨ν,K,hν,hCMC,hAC,_⟩ := isMinimizerAt_nonstandard_integrated_flux ⟨hvh.1,hvh.2.le⟩ hm hnstdF hR
  have hno (k : Fin 3)
      (hk : quotientMap (chamberVertex c (fun j => decide (j=k)))∉openRepresentative F)
      (hall : ∀ j : Fin 2,quotientMap (chamberVertex c (fun l => decide (l=k.succAbove j)))∈openRepresentative F) : False := by
    apply isMinimizerAt_cylinder_contact_not_three_vertices hVrange hcontact hF hm hcF hR c hd hν hCMC k (hAC k)
    · rwa [heq]
    · intro j
      rw [heq]
      exact hall j
  have hall : ∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l=j)))∈openRepresentative F := by
    rcases three_axes_dichotomy _ ⟨i,hiO⟩ hno with hall|⟨k,hk⟩
    · exact hall
    · obtain ⟨hzero,_,hdown⟩ := isMinimizerAt_chamber_vertex_order hV hF hm hμ ha
        (fun x hx j => (hsg x j ⟨hx.1,mem_iInter.mp hx.2 j⟩).le) hs
      have hv := bool_vertex_two_point_ideal hzero hdown k ((hk k).mpr rfl)
        (fun j hj => (hk j).mp hj)
      exact (isMinimizerAt_strict_two_vertices_impossible ⟨hvh.1,hvh.2.le⟩ hF hm hμ hN hp ha hs hsg k hv).elim
  exact ⟨F,μ,N,hN,hp,c,H,hF,hm,hμ,ha,hs,hsg,hH,hws,hw,hall,
    isMinimizerAt_smaller_side_double_vertices_vacant hvh hF hm hμ hN hp ha hs hsg hH⟩
end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

theorem fourCorner_normalized_contradiction {A h b r s a V : ℝ}
    (hA0 : 0<A) (ha : 0<a) (ha1 : a≤1) (hA : A≤a) (hva : V=a^2/Real.pi) (hh : 0≤h)
    (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0≤r) (hr1 : r≤V)
    (hs1 : s≤1)
    (htop : Real.sqrt (Real.pi*r)≤A*b-h*(V-r))
    (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-V))
    (hdrop : s-r≤A*Real.sqrt (1-b))
    (hbmax : 2/3≤b) (hxcap : h*A≤7/4) : False := by
  let x := h*A
  let d := Real.sqrt (1-b)
  let w := Real.sqrt (Real.pi*r)/a
  have hp : Real.pi≠0 := Real.pi_pos.ne'
  have haA : A≤a := hA
  have hx0 : 0≤x := mul_nonneg hh hA0.le
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hd2 : d^2=1-b := Real.sq_sqrt (by linarith)
  have hw0 : 0≤w := div_nonneg (Real.sqrt_nonneg _) ha.le
  have haw : a*w=Real.sqrt (Real.pi*r) := by dsimp only [w]; field_simp
  have hrw : r=a^2*w^2/Real.pi := by
    have hz := Real.sq_sqrt (mul_nonneg Real.pi_pos.le hr0)
    rw [← haw,mul_pow] at hz
    apply (eq_div_iff hp).mpr
    nlinarith only [hz]
  have hw1 : w≤1 := by
    rw [hva,hrw] at hr1
    have hz := (div_le_div_iff_of_pos_right Real.pi_pos).mp hr1
    have ha2 := sq_pos_of_pos ha
    have hw2' : w^2≤1 := (mul_le_mul_iff_right₀ ha2).mp (by simpa only [mul_one] using hz)
    nlinarith only [hw2',hw0]
  have hw2 : 0≤1-w^2 := by nlinarith
  have hxn : x≤h*a := mul_le_mul_of_nonneg_left haA hh
  have hnorm : w+x/Real.pi*(1-w^2)≤b := by
    have hleft := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hxn Real.pi_pos.le) hw2
    have hleft' := mul_le_mul_of_nonneg_left (add_le_add (le_refl w) hleft) ha.le
    have ht : a*(w+h*a/Real.pi*(1-w^2))≤A*b := by
      have hid : a*(w+h*a/Real.pi*(1-w^2))=a*w+h*(V-r) := by
        rw [hva,hrw]
        ring
      rw [hid,haw]
      linarith only [htop]
    have hright := mul_le_mul_of_nonneg_right haA hb0
    exact (mul_le_mul_iff_right₀ ha).mp (hleft'.trans (ht.trans hright))
  let f : ℝ → ℝ := fun t => t+x/Real.pi*(1-t^2)
  have hf : Continuous f := by fun_prop
  have hf1 : f 1=1 := by dsimp [f]; ring
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hw1 hf.continuousOn
    (show b∈Icc (f w) (f 1) from ⟨hnorm,by rw [hf1]; exact hb1.le⟩)
  have ht0 : 0≤t := hw0.trans ht.1
  have ht1 : t<1 := by
    by_contra hn
    have he : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [he,hf1] at hft
    linarith
  have htden : 0<1-t^2 := by nlinarith
  have hroot : t+x/Real.pi*(1-t^2)=b := hft
  have hxterm : 0≤x/Real.pi*(1-t^2) := by positivity
  have htd : t+d^2≤1 := by linarith only [hroot,hxterm,hd2]
  have hxroot : x=Real.pi*(1-t-d^2)/(1-t^2) := by
    apply (eq_div_iff htden.ne').mpr
    have he := congrArg (fun y : ℝ => y*Real.pi) hroot
    field_simp at he
    rw [show 1-t-d^2=b-t by linarith only [hd2]]
    nlinarith only [he]
  have hwtsq : w^2≤t^2 := (sq_le_sq₀ hw0 ht0).mpr ht.1
  have hrbound : r≤a^2*t^2/Real.pi := by
    rw [hrw]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwtsq (sq_nonneg a)) Real.pi_pos.le
  have hEt : A*b-h*(V-a^2*t^2/Real.pi)≤a*t := by
    have he : A*b-h*(V-a^2*t^2/Real.pi)=
        A*t+(h/Real.pi)*(A^2-a^2)*(1-t^2) := by
      rw [hva,← hroot]
      dsimp only [x]
      ring
    have hA2 : A^2≤a^2 := (sq_le_sq₀ hA0.le ha.le).mpr haA
    have hcorr : (h/Real.pi)*(A^2-a^2)*(1-t^2)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hh Real.pi_pos.le) (sub_nonpos.mpr hA2)) htden.le
    rw [he]
    have hat := mul_le_mul_of_nonneg_right haA ht0
    linarith only [hcorr,hat]
  have hsb : s≤a^2*t^2/Real.pi+a*d := by
    have hAd := mul_le_mul_of_nonneg_right haA hd0
    linarith only [hdrop,hrbound,hAd]
  have hbottom' : Real.sqrt (Real.pi*(1-s))≤a*t+x*d := by
    have hdiff := mul_le_mul_of_nonneg_left hdrop hh
    have hrr := mul_le_mul_of_nonneg_left hrbound hh
    have hxd : h*(A*d)=x*d := by dsimp [x]; ring
    rw [hxd] at hdiff
    linarith only [hbottom,hdiff,hrr,hEt]
  have hbsq : Real.pi*(1-s)≤(a*t+x*d)^2 := by
    have hy : 0≤a*t+x*d := by positivity
    have hh' := (sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*(1-s))) hy).mpr hbottom'
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by linarith : 0≤1-s))] at hh'
  have hnec : 1≤a*d+(a^2*t^2+(a*t+x*d)^2)/Real.pi := by
    have hh' := mul_le_mul_of_nonneg_left hsb Real.pi_pos.le
    have hcancel : Real.pi*(a^2*t^2/Real.pi+a*d)=a^2*t^2+Real.pi*a*d := by field_simp
    rw [hcancel] at hh'
    have hh2 : 1≤((a*d)*Real.pi+(a^2*t^2+(a*t+x*d)^2))/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith only [hh',hbsq])
    simpa only [add_div,mul_div_cancel_right₀ _ hp] using hh2
  have hd3 : d^2≤1/3 := by linarith only [hd2,hbmax]
  have hroot' : Real.pi*(1-t-d^2)=x*(1-t^2) := by
    exact ((eq_div_iff htden.ne').mp hxroot).symm
  have hstrict := corner_root_strict (show CornerRootData t d x from
    ⟨ht0,ht1,hd0,hd3,hx0,hxcap,hroot'⟩)
  have hnec' : 1≤d+(t^2+(t+x*d)^2)/Real.pi := by
    have had := mul_le_mul_of_nonneg_right ha1 hd0
    have hat : a*t≤t := by simpa using mul_le_mul_of_nonneg_right ha1 ht0
    have hatsq : a^2*t^2≤t^2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg ha.le ht0) ht0).mpr hat
    have hsum : (a*t+x*d)^2≤(t+x*d)^2 := by
      have hat0 : 0≤a*t+x*d := by positivity
      have hxd0 : 0≤x*d := by positivity
      exact (sq_le_sq₀ hat0 (add_nonneg ht0 hxd0)).mpr (add_le_add hat (le_refl (x*d)))
    have hdiv := div_le_div_of_nonneg_right (add_le_add hatsq hsum) Real.pi_pos.le
    linarith only [hnec,had,hdiv]
  exact (not_lt_of_ge hnec') hstrict

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_cylinder_contact_corner_excluded
    {V : ℝ} (hVrange : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    (hcontact : IsLocalMin cylinderRatio V)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (hw0 : 2/3 ≤ axialFluxWeight μ 0) (hw1 : axialFluxWeight μ 0<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : False := by
  have hv1 := firstTransition_mem_Ioo_half
  have hv2 := secondTransition_mem_Ioo_half
  have hvh : V∈Ioo (0 : ℝ) (1/2) := ⟨hv1.1.trans_le hVrange.1,hVrange.2.trans_lt hv2.2⟩
  have hV : V∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier hV hE hm hμ
  obtain ⟨hA,hAc,hA1,hh,hr,hrV,_,hs1,hb,_,htop,hbottom,hdrop⟩ :=
    isMinimizerAt_four_corner_necessary_data hvh hE hm hμ hN hp ha hs hsg hH ht1 ht2 hb1 hb2
  have hpos : 0<Real.sqrt (Real.pi*V) := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hvh.1)
  have hle : Real.sqrt (Real.pi*V) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    simpa only [mul_comm] using (le_div_iff₀ Real.pi_pos).mp hVrange.2
  have hv : V=(Real.sqrt (Real.pi*V))^2/Real.pi := by
    rw [Real.sq_sqrt (mul_nonneg Real.pi_pos.le hvh.1.le)]
    field_simp
  have hcap := (isMinimizerAt_cylinder_contact_bounds hVrange hcontact hE hm hμ hH).2.2.2.2
  rw [← hμ.1] at hcap
  exact fourCorner_normalized_contradiction hA hpos hle hAc hv hh hb hw1 hr hrV hs1 htop hbottom hdrop hw0
    (hcap.trans (by linarith [Real.pi_lt_d2]))

theorem isMinimizerAt_cylinder_contact_standard {V : ℝ}
    (hVrange : V∈Icc TwoVolume.V₁ TwoVolume.V₂) (hcontact : IsLocalMin cylinderRatio V)
    {E : Set Torus}
    (hmE : IsMinimizerAt V E) : SmallStandardRegion V E := by
  by_contra hnstd
  obtain ⟨F,μ,N,hN,hp,c,H,hF,hm,hμ,ha,hs,hsg,hH,hws,hw,haxis,hface⟩ :=
    isMinimizerAt_cylinder_contact_nonstandard_star hVrange hcontact hmE hnstd
  obtain ⟨i,hi⟩ : ∃ i : Fin 3,2/3 ≤ axialFluxWeight μ i := by
    by_contra! hn
    rw [Fin.sum_univ_three] at hws
    linarith [hn 0,hn 1,hn 2]
  classical
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have he0 : e.symm 0=i := by simp [e]
  have he1 : e.symm 1≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have he2 : e.symm 2≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have hpair (j : Fin 3) : ((fun k : Fin 3 => decide (k=0 ∨ k=j)) ∘ e)=
      (fun k => decide (k=i ∨ k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply,he0]
  have hsingle (j : Fin 3) : ((fun k : Fin 3 => decide (k=j)) ∘ e)=
      (fun k => decide (k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply]
  have ht (j : Fin 3) (hj : j≠i) :
      quotientMap (chamberVertex c (fun k => decide (k=i ∨ k=j)))∉openRepresentative F := by
    obtain ⟨k,hk⟩ := fin3_pair_complement i j hj.symm
    rw [hk]
    exact fun h => hface k (subset_closure h)
  have hv (b : Fin 3 → Bool) :
      quotientMap (chamberVertex (c ∘ e.symm) b)∈openRepresentative (torusCoordinatePermute e ⁻¹' F) ↔
      quotientMap (chamberVertex c (b ∘ e))∈openRepresentative F := by
    rw [openRepresentative_coordinatePermute hF e]
    change torusCoordinatePermute e (quotientMap (chamberVertex (c ∘ e.symm) b))∈openRepresentative F ↔ _
    rw [← quotientMap_coordinatePermute,chamberVertex_coordinatePermute]
  apply isMinimizerAt_cylinder_contact_corner_excluded hVrange hcontact
    ((torusCoordinatePermute e).continuous.measurable hF) (isMinimizerAt_coordinatePermute hm e)
    (isNormalMeasure_coordinatePermute hF hμ e)
    (coordinatePermutedField_contDiff e hN) (coordinatePermutedField_periodic e hp)
    (permuted_normal_ae hN.continuous hp ha e) (reflection_invariant_coordinatePermute hs e)
    (chamberSign_coordinatePermute hF hsg e)
  · simpa [axialFluxWeight_permute,e] using hi
  · rw [axialFluxWeight_permute]
    exact (hw _).2
  · rw [hv,hpair]
    exact ht _ he1
  · rw [hv,hpair]
    exact ht _ he2
  · rw [hv,hsingle]
    exact haxis _
  · rw [hv,hsingle]
    exact haxis _
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cylinder_interval_interior {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) :
    V∈Ioo (0 : ℝ) (1/2) :=
  ⟨firstTransition_mem_Ioo_half.1.trans_le hV.1,hV.2.trans_lt secondTransition_mem_Ioo_half.2⟩

lemma profile_eq_tube_of_small_standard {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    {E : Set Torus} (hm : IsMinimizerAt V E) (hs : SmallStandardRegion V E) :
    isoperimetricProfile V=Real.sqrt (Real.pi*V) := by
  have hv := cylinder_interval_interior hV
  have hP := (hs.bv_data ⟨hv.1,hv.2.le⟩).2.2
  rw [candidateProfile_tube hV] at hP
  rw [isoperimetricProfile_eq_of_isMinimizerAt hm,hP,ENNReal.toReal_ofReal (by positivity)]
  ring

lemma cylinderRatio_eq_of_profile {V : ℝ} (hV : 0<V)
    (he : isoperimetricProfile V=Real.sqrt (Real.pi*V)) :
    cylinderRatio V=Real.sqrt Real.pi := by
  rw [cylinderRatio,he,Real.sqrt_mul Real.pi_pos.le,mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr hV)]

lemma cylinderRatio_first : cylinderRatio TwoVolume.V₁=Real.sqrt Real.pi := by
  have hv := firstTransition_mem_Ioo_half
  obtain ⟨E,hm⟩ := exists_isMinimizerAt (show TwoVolume.V₁∈Ioo (0 : ℝ) 1 from ⟨hv.1,by change 4*Real.pi/81<1; linarith [hv.2]⟩)
  apply cylinderRatio_eq_of_profile hv.1
  apply profile_eq_tube_of_small_standard ⟨le_rfl,TwoVolume.transitions.2.1.le⟩ hm
  exact isMinimizerAt_first_transition_standard hm

lemma cylinderRatio_second : cylinderRatio TwoVolume.V₂=Real.sqrt Real.pi := by
  have hv := secondTransition_mem_Ioo_half
  obtain ⟨E,hm⟩ := exists_isMinimizerAt (show TwoVolume.V₂∈Ioo (0 : ℝ) 1 from ⟨hv.1,by change 1/Real.pi<1; linarith [hv.2]⟩)
  apply cylinderRatio_eq_of_profile hv.1
  apply profile_eq_tube_of_small_standard ⟨TwoVolume.transitions.2.1.le,le_rfl⟩ hm
  exact isMinimizerAt_second_transition_standard hm

lemma cylinderRatio_contact {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    (hc : IsLocalMin cylinderRatio V) : cylinderRatio V=Real.sqrt Real.pi := by
  have hv := cylinder_interval_interior hV
  obtain ⟨E,hm⟩ := exists_isMinimizerAt (show V∈Ioo (0 : ℝ) 1 from ⟨hv.1,by linarith [hv.2]⟩)
  exact cylinderRatio_eq_of_profile hv.1 (profile_eq_tube_of_small_standard hV hm
    (isMinimizerAt_cylinder_contact_standard hV hc hm))

theorem isoperimetricProfile_cylinder_interval {V : ℝ}
    (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) :
    isoperimetricProfile V=Real.sqrt (Real.pi*V) := by
  have hv := cylinder_interval_interior hV
  have hc : ContinuousOn cylinderRatio (Icc TwoVolume.V₁ TwoVolume.V₂) := by
    apply (continuousOn_isoperimetricProfile.mono ?_).div Real.continuous_sqrt.continuousOn
    · intro W hW
      exact Real.sqrt_ne_zero'.mpr (cylinder_interval_interior hW).1
    · intro W hW
      have hh := cylinder_interval_interior hW
      exact ⟨hh.1.le,by linarith [hh.2]⟩
  obtain ⟨W,hW,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc TwoVolume.V₁ TwoVolume.V₂).Nonempty from ⟨V,hV⟩) hc
  have heW : cylinderRatio W=Real.sqrt Real.pi := by
    rcases eq_or_lt_of_le hW.1 with he|he
    · rw [←he,cylinderRatio_first]
    rcases eq_or_lt_of_le hW.2 with he'|he'
    · rw [he',cylinderRatio_second]
    exact cylinderRatio_contact hW (hmin.isLocalMin (Icc_mem_nhds he he'))
  have hr := hmin hV
  rw [heW] at hr
  change Real.sqrt Real.pi ≤ isoperimetricProfile V/Real.sqrt V at hr
  have hlow := (le_div_iff₀ (Real.sqrt_pos.mpr hv.1)).mp hr
  rw [←Real.sqrt_mul Real.pi_pos.le] at hlow
  apply le_antisymm _ hlow
  have hu := isoperimetricProfile_le_candidate (show V∈Icc (0 : ℝ) 1 from ⟨hv.1.le,by linarith [hv.2]⟩)
  rw [candidateProfile_tube hV] at hu
  linarith only [hu]

lemma isoperimetricProfile_cylinder_contact {V : ℝ} (hV : V∈Ioo TwoVolume.V₁ TwoVolume.V₂) :
    IsLocalMin cylinderRatio V := by
  have he := cylinderRatio_eq_of_profile (cylinder_interval_interior ⟨hV.1.le,hV.2.le⟩).1
    (isoperimetricProfile_cylinder_interval ⟨hV.1.le,hV.2.le⟩)
  filter_upwards [Ioo_mem_nhds hV.1 hV.2] with W hW
  rw [he,cylinderRatio_eq_of_profile (cylinder_interval_interior ⟨hW.1.le,hW.2.le⟩).1
    (isoperimetricProfile_cylinder_interval ⟨hW.1.le,hW.2.le⟩)]

theorem isMinimizerAt_cylinder_interval_standard {V : ℝ}
    (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) {E : Set Torus} (hm : IsMinimizerAt V E) :
    SmallStandardRegion V E := by
  rcases eq_or_lt_of_le hV.1 with he|he
  · subst V
    exact isMinimizerAt_first_transition_standard hm
  rcases eq_or_lt_of_le hV.2 with he'|he'
  · subst V
    exact isMinimizerAt_second_transition_standard hm
  exact isMinimizerAt_cylinder_contact_standard hV (isoperimetricProfile_cylinder_contact ⟨he,he'⟩) hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TwoVolume.sphereArea_three_halves {V : ℝ} (hV : 0≤V) :
    TwoVolume.sphereArea V^(3/2 : ℝ)=(9*Real.pi/2)^(1/2 : ℝ)*V := by
  unfold TwoVolume.sphereArea
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hV _),
    ← Real.rpow_mul (by positivity : 0≤9*Real.pi/2),← Real.rpow_mul hV]
  norm_num

theorem isoperimetricProfile_sphere_interval {V : ℝ} (hV : V∈Icc 0 TwoVolume.V₁) :
    isoperimetricProfile V=TwoVolume.sphereArea V := by
  have hv1 := TwoVolume.transitions.1
  have hv1h : TwoVolume.V₁<1/2 := TwoVolume.transitions.2.1.trans TwoVolume.transitions.2.2
  have hv1' : TwoVolume.V₁≤1 := by linarith
  have hlimit : isoperimetricProfile TwoVolume.V₁=TwoVolume.sphereArea TwoVolume.V₁ := by
    rw [isoperimetricProfile_cylinder_interval ⟨le_rfl,TwoVolume.transitions.2.1.le⟩,
      TwoVolume.sphereArea_eq_tubeArea_V₁]
    rfl
  have hb : 0≤V/TwoVolume.V₁ := div_nonneg hV.1 hv1.le
  have hb1 : V/TwoVolume.V₁≤1 := (div_le_one hv1).mpr hV.2
  have hh := concaveOn_isoperimetricProfile_three_halves.2
    (show (0 : ℝ)∈Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show TwoVolume.V₁∈Icc (0 : ℝ) 1 from ⟨hv1.le,hv1'⟩)
    (show 0≤1-V/TwoVolume.V₁ by linarith) hb
    (show (1-V/TwoVolume.V₁)+V/TwoVolume.V₁=1 by ring)
  have hcenter : (1-V/TwoVolume.V₁)*0+(V/TwoVolume.V₁)*TwoVolume.V₁=V := by
    field_simp
    ring
  simp only [smul_eq_mul] at hh
  rw [hcenter] at hh
  simp only [isoperimetricProfile_zero,Real.zero_rpow (by norm_num : (3/2 : ℝ)≠0),
    mul_zero,zero_add,hlimit,TwoVolume.sphereArea_three_halves hv1.le] at hh
  have hl : TwoVolume.sphereArea V^(3/2 : ℝ) ≤ isoperimetricProfile V^(3/2 : ℝ) := by
    rw [TwoVolume.sphereArea_three_halves hV.1]
    calc
      (9*Real.pi/2)^(1/2 : ℝ)*V = (V/TwoVolume.V₁)*((9*Real.pi/2)^(1/2 : ℝ)*TwoVolume.V₁) := by
        field_simp
      _ ≤ isoperimetricProfile V^(3/2 : ℝ) := hh
  have hl' := (Real.rpow_le_rpow_iff (TwoVolume.sphereArea_nonneg hV.1)
    (isoperimetricProfile_nonneg V) (by norm_num : (0 : ℝ)<3/2)).mp hl
  have hu := isoperimetricProfile_le_candidate (show V∈Icc (0 : ℝ) 1 from ⟨hV.1,hV.2.trans hv1'⟩)
  rw [candidateProfile_sphere hV,unit_sphereArea] at hu
  apply le_antisymm _ hl'
  linarith only [hu]

theorem isMinimizerAt_sphere_open_standard {V : ℝ} (hV : V∈Ioo 0 TwoVolume.V₁)
    {E : Set Torus} (hm : IsMinimizerAt V E) : SmallStandardRegion V E := by
  have hv1h : TwoVolume.V₁<1/2 := TwoVolume.transitions.2.1.trans TwoVolume.transitions.2.2
  have hvh : V∈Ioo (0 : ℝ) (1/2) := ⟨hV.1,hV.2.trans hv1h⟩
  have hv : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hvh.2]⟩
  rcases Periodic.isMinimizerAt_connected_or_standard_slab hv hm with hc|hs
  · let F := toMeasurable torusVolume E
    have hF : MeasurableSet F := measurableSet_toMeasurable _ _
    have hFE : F=ᵐ[torusVolume]E := hm.1.1.toMeasurable_ae_eq
    have hmF := (isMinimizerAt_congr_ae hFE).mpr hm
    have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [openRepresentative_congr_ae hFE]
    have he : ∀ᶠ W in 𝓝 V,isoperimetricProfile W^(3/2 : ℝ)=(9*Real.pi/2)^(1/2 : ℝ)*W+0 := by
      filter_upwards [Ioo_mem_nhds hV.1 hV.2] with W hW
      rw [isoperimetricProfile_sphere_interval ⟨hW.1.le,hW.2.le⟩,
        TwoVolume.sphereArea_three_halves hW.1.le,add_zero]
    have hh := Periodic.isMinimizerAt_power_affine_standard_ball hvh hF hmF hcF he
    have hstd : SmallStandardRegion V F := Or.inl hh
    exact (smallStandardRegion_congr_ae hFE V).mp hstd
  · have hs' : SmallStandardRegion V E := by
      simpa only [StandardRegionAt,ite_eq_left hvh.2.le] using hs.2.2
    exact hs'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isoperimetricProfile_slab_interval {V : ℝ}
    (hV : V∈Icc TwoVolume.V₂ (1-TwoVolume.V₂)) : isoperimetricProfile V=1 := by
  have hv2 := secondTransition_mem_Ioo_half
  have hh := isoperimetricProfile_chord hv2.1.le
    (show 1-TwoVolume.V₂≤1 by change 1-1/Real.pi≤1; linarith [hv2.1])
    (show TwoVolume.V₂<1-TwoVolume.V₂ by change 1/Real.pi<1-1/Real.pi; linarith [hv2.2]) V hV
  rw [isoperimetricProfile_compl (show TwoVolume.V₂∈Icc (0 : ℝ) 1 from
    ⟨hv2.1.le,by change 1/Real.pi≤1; linarith [hv2.2]⟩)] at hh
  change isoperimetricProfile (1/Real.pi)+_ ≤ isoperimetricProfile V at hh
  simp only [TwoVolume.V₂,sub_self,mul_zero,zero_div,add_zero,isoperimetricProfile_second_transition] at hh
  have hv : V∈Icc (0 : ℝ) 1 := ⟨hv2.1.le.trans hV.1,hV.2.trans (by change 1-1/Real.pi≤1; linarith [hv2.1])⟩
  have hu := isoperimetricProfile_le_candidate hv
  rw [candidateProfile_slab hV] at hu
  exact le_antisymm (by linarith only [hu]) hh

lemma isoperimetricProfile_slab_local_min {V : ℝ}
    (hV : V∈Ioo TwoVolume.V₂ (1-TwoVolume.V₂)) : IsLocalMin isoperimetricProfile V := by
  filter_upwards [Ioo_mem_nhds hV.1 hV.2] with W hW
  rw [isoperimetricProfile_slab_interval ⟨hV.1.le,hV.2.le⟩,
    isoperimetricProfile_slab_interval ⟨hW.1.le,hW.2.le⟩]

theorem isMinimizerAt_small_slab_standard {V : ℝ} (hV : V∈Icc TwoVolume.V₂ (1/2))
    {E : Set Torus} (hm : IsMinimizerAt V E) : SmallStandardRegion V E := by
  rcases eq_or_lt_of_le hV.1 with he|he
  · subst V
    exact isMinimizerAt_second_transition_standard hm
  have hv2 := secondTransition_mem_Ioo_half
  have hv : V∈Ioo (0 : ℝ) 1 := ⟨hv2.1.trans_le hV.1,by linarith [hV.2]⟩
  have hc := isoperimetricProfile_slab_local_min (show V∈Ioo TwoVolume.V₂ (1-TwoVolume.V₂) from
    ⟨he,by change V<1-1/Real.pi; linarith [hV.2,hv2.2]⟩)
  have hh := Periodic.isMinimizerAt_profile_local_min_slab hv hm hc
  simpa only [StandardRegionAt,ite_eq_left hV.2] using hh.2.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_small_volume_standard {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hm : IsMinimizerAt V E) : SmallStandardRegion V E := by
  by_cases hfirst : V < TwoVolume.V₁
  · exact isMinimizerAt_sphere_open_standard ⟨hV.1,hfirst⟩ hm
  · by_cases hsecond : V ≤ TwoVolume.V₂
    · exact isMinimizerAt_cylinder_interval_standard ⟨le_of_not_gt hfirst,hsecond⟩ hm
    · exact isMinimizerAt_small_slab_standard ⟨(lt_of_not_ge hsecond).le,hV.2⟩ hm

theorem isMinimizerAt_all_volume_standard {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hm : IsMinimizerAt V E) : StandardRegionAt V E := by
  unfold StandardRegionAt
  split_ifs with hv
  · exact isMinimizerAt_small_volume_standard ⟨hV.1,hv⟩ hm
  · have hvc : 1-V ∈ Ioc (0 : ℝ) (1/2) := by constructor <;> linarith [hV.2]
    exact isMinimizerAt_small_volume_standard hvc
      ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).2 hm)

theorem perimeter_eq_candidate_of_minimizer {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hm : IsMinimizerAt V E) :
    perimeter E = ENNReal.ofReal (candidateProfile V) :=
  ((isMinimizerAt_all_volume_standard hV hm).bv_data hV).2.2

theorem StandardRegionAt.isMinimizerAt {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hs : StandardRegionAt V E) : IsMinimizerAt V E := by
  obtain ⟨F,hmF⟩ := exists_isMinimizerAt hV
  obtain ⟨hE,heV,heP⟩ := hs.bv_data hV
  have hfP := perimeter_eq_candidate_of_minimizer hV hmF
  refine ⟨hE,heV,?_⟩
  intro G hG hgV
  rw [heP,←hfP]
  exact hmF.2.2 G hG hgV

theorem unit_cubic_isoperimetric (V : ℝ) (hV : V ∈ Ioo 0 1) :
    (∃ E : Set Torus, IsMinimizerAt V E) ∧
    (∀ E : Set Torus, IsMinimizerAt V E →
      perimeter E = ENNReal.ofReal (candidateProfile V)) ∧
    (∀ E : Set Torus, IsMinimizerAt V E ↔ StandardRegionAt V E) := by
  refine ⟨exists_isMinimizerAt hV,?_,?_⟩
  · intro E hm
    exact perimeter_eq_candidate_of_minimizer hV hm
  · intro E
    exact ⟨isMinimizerAt_all_volume_standard hV,StandardRegionAt.isMinimizerAt hV⟩

end CubicTorus

end
end

end OAI
