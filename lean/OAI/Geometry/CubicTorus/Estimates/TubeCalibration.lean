import Mathlib
import OAI.Geometry.CubicTorus.Estimates.LatticeHeightHom

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_affine_volume_support {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (P H : ℝ) (A : ℝ → ℝ),0<P ∧ P=(perimeter E).toReal ∧
      ContDiffAt ℝ (⊤ : ℕ∞) A 0 ∧ A 0=P ∧ deriv A 0=H*P ∧
      deriv (deriv A) 0≤0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),isoperimetricProfile (V+t*P)≤A t/2) := by
  obtain ⟨P,H,A,hP,hPe,hA,hA0,hdA,hddA,habove,_⟩ :=
    isMinimizerAt_affine_volume_support_with_CMC hV hE hmin
  exact ⟨P,H,A,hP,hPe,hA,hA0,hdA,hddA,habove⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology

namespace CubicTorus.Reduction

lemma second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  rw [hz] at hneg
  exact (lt_irrefl 0) hneg

lemma second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y => f y - g y)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have heq : deriv (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => deriv f y - deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_sub (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_sub
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

structure UpperSupport (I C : ℝ → ℝ) (x : ℝ) : Prop where
  smooth : ContDiffAt ℝ 2 C x
  contact : C x = I x
  above : ∀ᶠ y in 𝓝 x, I y ≤ C y

lemma jet_comparison {I C F : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMin (fun y => I y - F y) x) :
    deriv C x = deriv F x ∧ deriv (deriv F) x ≤ deriv (deriv C) x := by
  have hmc : IsLocalMin (fun y => C y - F y) x := by
    filter_upwards [hm, hs.above] with y hy habove
    change C x - F x ≤ C y - F y
    rw [hs.contact]
    linarith
  have h1 := hmc.deriv_eq_zero
  change deriv (C - F) x = 0 at h1
  rw [deriv_sub (hs.smooth.differentiableAt (by norm_num))
    (hF.differentiableAt (by norm_num))] at h1
  have h2 := second_deriv_nonneg_of_local_min hmc (hs.smooth.continuousAt.sub hF.continuousAt)
  rw [second_deriv_sub hs.smooth hF] at h2
  exact ⟨sub_eq_zero.mp h1, sub_nonneg.mp h2⟩

def ode (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv F) x + (deriv F x) ^ 2 / F x

lemma ode_comparison {I C F : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMin (fun y => I y - F y) x)
    (hpos : 0 < I x) (hle : I x ≤ F x) : ode F x ≤ ode C x := by
  have hj := jet_comparison hs hF hm
  have hd := div_le_div_of_nonneg_left (sq_nonneg (deriv F x)) hpos hle
  rw [← hs.contact, ← hj.1] at hd
  unfold ode
  rw [← hj.1]
  exact add_le_add hj.2 hd

theorem branch_comparison {I F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : ContinuousOn I (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hupper : ∀ x ∈ Icc a b, I x ≤ F x)
    (hleft : I a = F a) (hright : I b = F b)
    (hpositive : ∀ x ∈ Ioo a b, 0 < I x)
    (hsmooth : ∀ x ∈ Ioo a b, ContDiffAt ℝ 2 F x)
    (hode : ∀ x ∈ Ioo a b, 0 ≤ ode F x)
    (hsupport : ∀ x ∈ Ioo a b, I x < F x →
      ∃ C : ℝ → ℝ, UpperSupport I C x ∧ ode C x < 0) :
    ∀ x ∈ Icc a b, I x = F x := by
  intro y hy
  apply le_antisymm (hupper y hy)
  by_contra! hylt
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (le_of_lt hab)) (hI.sub hF)
  have hnegative : I x - F x < 0 := lt_of_le_of_lt (hmin hy) (sub_neg.mpr hylt)
  have hnleft : x ≠ a := by intro heq; subst x; rw [hleft, sub_self] at hnegative; linarith
  have hnright : x ≠ b := by intro heq; subst x; rw [hright, sub_self] at hnegative; linarith
  have hxin : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hnleft), lt_of_le_of_ne hx.2 hnright⟩
  have hm : IsLocalMin (fun y => I y - F y) x :=
    hmin.isLocalMin (Icc_mem_nhds hxin.1 hxin.2)
  obtain ⟨C, hc, hcneg⟩ := hsupport x hxin (sub_neg.mp hnegative)
  have hcomp := ode_comparison hc (hsmooth x hxin) hm (hpositive x hxin) (hupper x hx)
  linarith [hode x hxin]

theorem no_negative_support {I F C : ℝ → ℝ} {x : ℝ}
    (heq : I =ᶠ[𝓝 x] F) (hs : UpperSupport I C x)
    (hsmooth : ContDiffAt ℝ 2 F x) (hpositive : 0 < F x) (hode : 0 ≤ ode F x) :
    ¬ ode C x < 0 := by
  have hm : IsLocalMin (fun y => I y - F y) x := by
    filter_upwards [heq] with y hy
    change I x - F x ≤ I y - F y
    rw [heq.self_of_nhds, hy]
    simp only [sub_self, le_refl]
  have hi : I x = F x := heq.self_of_nhds
  have hc := ode_comparison hs hsmooth hm (hi.symm ▸ hpositive) (le_of_eq hi)
  linarith

lemma second_deriv_quadratic (α β γ x : ℝ) :
    deriv (deriv (fun y => α * y ^ 2 + β * y + γ)) x = 2 * α := by
  have hd (y : ℝ) : HasDerivAt (fun z => α * z ^ 2 + β * z + γ) (2 * α * y + β) y := by
    convert! (((hasDerivAt_pow 2 y).const_mul α).add
      ((hasDerivAt_id y).const_mul β)).add_const γ using 1
    ring
  have hdeq : deriv (fun y => α * y ^ 2 + β * y + γ) = (fun y => 2 * α * y + β) := by
    funext y
    exact (hd y).deriv
  rw [hdeq]
  have hd2 : HasDerivAt (fun y : ℝ => 2 * α * y + β) (2 * α) x := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul (2 * α)).add_const β
  exact hd2.deriv

theorem chord_below_of_upper_support {I : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) :
    ∀ x ∈ Icc a b, I a + (x - a) * (I b - I a) / (b - a) ≤ I x := by
  intro c hc
  by_contra! hgap
  let m := (I b - I a) / (b - a)
  let L := fun x : ℝ => I a + (x - a) * m
  have hLa : L a = I a := by simp [L]
  have hLb : L b = I b := by
    dsimp [L, m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hgap' : I c < L c := by simpa [L, m, mul_div_assoc] using hgap
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    intro heq
    subst c
    rw [hLa] at hgap'
    exact (lt_irrefl _ hgap')
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    intro heq
    subst c
    rw [hLb] at hgap'
    exact (lt_irrefl _ hgap')
  let ε := (L c - I c) / (2 * ((c - a) * (b - c)))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap')
    (mul_pos (by norm_num) (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hcb)))
  let F := fun x : ℝ => ε * x ^ 2 + (m - ε * (a + b)) * x +
    (I a - a * m + ε * a * b)
  have hF_eq (x : ℝ) : F x = L x + ε * (x - a) * (x - b) := by dsimp [F, L]; ring
  have hFa : F a = I a := by rw [hF_eq, hLa]; ring
  have hFb : F b = I b := by rw [hF_eq, hLb]; ring
  have hFc : I c < F c := by
    have hprod : ε * (c - a) * (b - c) = (L c - I c) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt (sub_pos.mpr hca), ne_of_gt (sub_pos.mpr hcb)]
    rw [hF_eq]
    nlinarith
  have hF : ContDiff ℝ 2 F := by dsimp [F]; fun_prop
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hI.sub hF.continuous.continuousOn)
  have hneg : I x - F x < 0 := lt_of_le_of_lt (hmin hc) (sub_neg.mpr hFc)
  have hxa : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro heq
    subst x
    rw [hFa, sub_self] at hneg
    exact lt_irrefl _ hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro heq
    subst x
    rw [hFb, sub_self] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨C, hC, hC''⟩ := hsupport x ⟨hxa, hxb⟩
  have hj := (jet_comparison hC hF.contDiffAt
    (hmin.isLocalMin (Icc_mem_nhds hxa hxb))).2
  have hF'' : deriv (deriv F) x = 2 * ε := second_deriv_quadratic _ _ _ _
  rw [hF''] at hj
  linarith

end CubicTorus.Reduction

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma deriv_volume_reparam (A : ℝ → ℝ) (V P x : ℝ) :
    deriv (fun y ↦ A ((y-V)/P)) x=deriv A ((x-V)/P)/P := by
  have he : (fun y ↦ A ((y-V)/P))=(fun y ↦ A (P⁻¹*(y-V))) := by
    funext y
    congr 1
    ring
  rw [he,deriv_comp_sub_const (fun t ↦ A (P⁻¹*t)) V x,deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [show P⁻¹*(x-V)=(x-V)/P by ring]
  ring

lemma second_deriv_volume_reparam (A : ℝ → ℝ) (V P x : ℝ) :
    deriv (deriv (fun y ↦ A ((y-V)/P)/2)) x=
      deriv (deriv A) ((x-V)/P)/P/P/2 := by
  have he : deriv (fun y ↦ A ((y-V)/P)/2)=
      (fun y ↦ deriv A ((y-V)/P)/P/2) := by
    funext y
    rw [deriv_div_const,deriv_volume_reparam]
  rw [he,deriv_div_const,deriv_div_const,deriv_volume_reparam]

theorem isoperimetricProfile_upper_support {V : ℝ} (hV : V∈Ioo 0 1) :
    ∃ C : ℝ → ℝ,Reduction.UpperSupport isoperimetricProfile C V ∧
      deriv (deriv C) V≤0 := by
  obtain ⟨E,hE⟩ := exists_isMinimizerAt hV
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmin : IsMinimizerAt V F := (isMinimizerAt_congr_ae hE.1.1.toMeasurable_ae_eq).2 hE
  obtain ⟨P,H,A,hP,hPe,hA,hA0,_hdA,hddA,habove⟩ :=
    Periodic.isMinimizerAt_affine_volume_support hV hF hmin
  let C : ℝ → ℝ := fun W ↦ A ((W-V)/P)/2
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun W : ℝ ↦ (W-V)/P) := by fun_prop
  have hrV : (V-V)/P=0 := by simp
  have hC : ContDiffAt ℝ (⊤ : ℕ∞) C V := by
    have ha : ContDiffAt ℝ (⊤ : ℕ∞) A ((V-V)/P) := hrV.symm ▸ hA
    exact (ha.comp V hr.contDiffAt).div_const 2
  refine ⟨C,⟨hC.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),?_,?_⟩,?_⟩
  · simp only [C,sub_self,zero_div,hA0,hPe,isoperimetricProfile_eq_of_isMinimizerAt hmin]
  · have ht : Tendsto (fun W : ℝ ↦ (W-V)/P) (𝓝 V) (𝓝 0) := by
      simpa only [sub_self,zero_div] using hr.continuous.continuousAt.tendsto (x := V)
    filter_upwards [ht.eventually habove] with W hW
    have hi : V+(W-V)/P*P=W := by rw [div_mul_cancel₀ _ hP.ne']; ring
    simpa only [hi,C] using hW
  · change deriv (deriv (fun W ↦ A ((W-V)/P)/2)) V≤0
    rw [second_deriv_volume_reparam,sub_self,zero_div]
    exact div_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hddA hP.le) hP.le)
      (by norm_num)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus.Reduction

theorem chord_below_of_lowerSemicontinuous_upper_support {I : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : LowerSemicontinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) :
    ∀ x ∈ Icc a b, I a + (x - a) * (I b - I a) / (b - a) ≤ I x := by
  intro c hc
  by_contra! hgap
  let m := (I b - I a) / (b - a)
  let L := fun x : ℝ => I a + (x - a) * m
  have hLa : L a = I a := by simp [L]
  have hLb : L b = I b := by
    dsimp [L, m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hgap' : I c < L c := by simpa [L, m, mul_div_assoc] using hgap
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    intro heq
    subst c
    rw [hLa] at hgap'
    exact (lt_irrefl _ hgap')
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    intro heq
    subst c
    rw [hLb] at hgap'
    exact (lt_irrefl _ hgap')
  let ε := (L c - I c) / (2 * ((c - a) * (b - c)))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap')
    (mul_pos (by norm_num) (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hcb)))
  let F := fun x : ℝ => ε * x ^ 2 + (m - ε * (a + b)) * x +
    (I a - a * m + ε * a * b)
  have hF_eq (x : ℝ) : F x = L x + ε * (x - a) * (x - b) := by dsimp [F, L]; ring
  have hFa : F a = I a := by rw [hF_eq, hLa]; ring
  have hFb : F b = I b := by rw [hF_eq, hLb]; ring
  have hFc : I c < F c := by
    have hprod : ε * (c - a) * (b - c) = (L c - I c) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt (sub_pos.mpr hca), ne_of_gt (sub_pos.mpr hcb)]
    rw [hF_eq]
    nlinarith
  have hF : ContDiff ℝ 2 F := by dsimp [F]; fun_prop
  have hsemi : LowerSemicontinuousOn (fun y ↦ I y-F y) (Icc a b) := by
    simpa only [sub_eq_add_neg,Pi.neg_apply] using hI.add hF.continuous.neg.continuousOn.lowerSemicontinuousOn
  obtain ⟨x, hx, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (nonempty_Icc.mpr hab.le) isCompact_Icc hsemi
  have hneg : I x - F x < 0 := lt_of_le_of_lt (hmin hc) (sub_neg.mpr hFc)
  have hxa : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro heq
    subst x
    rw [hFa, sub_self] at hneg
    exact lt_irrefl _ hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro heq
    subst x
    rw [hFb, sub_self] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨C, hC, hC''⟩ := hsupport x ⟨hxa, hxb⟩
  have hj := (jet_comparison hC hF.contDiffAt
    (hmin.isLocalMin (Icc_mem_nhds hxa hxb))).2
  have hF'' : deriv (deriv F) x = 2 * ε := second_deriv_quadratic _ _ _ _
  rw [hF''] at hj
  linarith

end CubicTorus.Reduction

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isoperimetricProfile_chord {a b : ℝ} (ha : 0≤a) (hb : b≤1) (hab : a<b) :
    ∀ x∈Icc a b,isoperimetricProfile a+
      (x-a)*(isoperimetricProfile b-isoperimetricProfile a)/(b-a)≤ isoperimetricProfile x := by
  apply Reduction.chord_below_of_lowerSemicontinuous_upper_support hab
  · exact lowerSemicontinuousOn_isoperimetricProfile.mono (Icc_subset_Icc ha hb)
  · intro x hx
    exact isoperimetricProfile_upper_support ⟨ha.trans_lt hx.1,hx.2.trans_le hb⟩

theorem concaveOn_isoperimetricProfile :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) isoperimetricProfile := by
  apply LinearOrder.concaveOn_of_lt (convex_Icc (0 : ℝ) 1)
  intro x hx y hy hxy a b ha hb hab
  have hmem : a*x+b*y∈Icc x y := by
    have hax : a*x+b*x=x := by rw [← add_mul,hab,one_mul]
    have hay : a*y+b*y=y := by rw [← add_mul,hab,one_mul]
    constructor <;> nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxy.le),
      mul_nonneg hb.le (sub_nonneg.mpr hxy.le)]
  have hh := isoperimetricProfile_chord hx.1 hy.2 hxy (a*x+b*y) hmem
  have he : isoperimetricProfile x+(a*x+b*y-x)*
      (isoperimetricProfile y-isoperimetricProfile x)/(y-x)=
        a*isoperimetricProfile x+b*isoperimetricProfile y := by
    have ha' : a=1-b := by linarith
    rw [ha']
    field_simp [sub_ne_zero.mpr hxy.ne']
    ring
  rw [he] at hh
  exact hh

theorem monotoneOn_isoperimetricProfile_half :
    MonotoneOn isoperimetricProfile (Icc (0 : ℝ) (1/2)) := by
  intro x hx y hy hxy
  by_cases he : x=1/2
  · have hyx : y=x := le_antisymm (by linarith [hy.2]) hxy
    simp only [hyx,le_refl]
  have hxlt : x<1/2 := lt_of_le_of_ne hx.2 he
  have hxx : x<1-x := by linarith
  have hc := isoperimetricProfile_chord hx.1 (by linarith [hx.1] : 1-x≤1) hxx
    y ⟨hxy,by linarith [hy.2,hx.2]⟩
  rw [isoperimetricProfile_compl ⟨hx.1,by linarith [hx.2]⟩,sub_self,mul_zero,zero_div,add_zero] at hc
  exact hc

theorem antitoneOn_isoperimetricProfile_half :
    AntitoneOn isoperimetricProfile (Icc (1/2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hc := monotoneOn_isoperimetricProfile_half
    (show 1-y∈Icc (0 : ℝ) (1/2) from ⟨by linarith [hy.2],by linarith [hy.1]⟩)
    (show 1-x∈Icc (0 : ℝ) (1/2) from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
    (by linarith : 1-y≤1-x)
  rwa [isoperimetricProfile_compl ⟨by linarith [hy.1],hy.2⟩,
    isoperimetricProfile_compl ⟨by linarith [hx.1],hx.2⟩] at hc

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_CMC_upper_support {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (C : ℝ → ℝ),
      IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧
      deriv C V=H/2 ∧ deriv (deriv C) V≤0 := by
  obtain ⟨P,H,A,hP,hPe,hA,hA0,hdA,hddA,habove,μ,hμ,hCMC⟩ :=
    Periodic.isMinimizerAt_affine_volume_support_with_CMC hV hE hmin
  let C : ℝ → ℝ := fun W ↦ A ((W-V)/P)/2
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun W : ℝ ↦ (W-V)/P) := by fun_prop
  have hrV : (V-V)/P=0 := by simp
  have hC : ContDiffAt ℝ (⊤ : ℕ∞) C V := by
    have ha : ContDiffAt ℝ (⊤ : ℕ∞) A ((V-V)/P) := hrV.symm ▸ hA
    exact (ha.comp V hr.contDiffAt).div_const 2
  refine ⟨μ,H,C,hμ,hCMC,⟨hC.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),?_,?_⟩,?_,?_⟩
  · simp only [C,sub_self,zero_div,hA0,hPe,isoperimetricProfile_eq_of_isMinimizerAt hmin]
  · have ht : Tendsto (fun W : ℝ ↦ (W-V)/P) (𝓝 V) (𝓝 0) := by
      simpa only [sub_self,zero_div] using hr.continuous.continuousAt.tendsto (x := V)
    filter_upwards [ht.eventually habove] with W hW
    have hi : V+(W-V)/P*P=W := by rw [div_mul_cancel₀ _ hP.ne']; ring
    simpa only [hi,C] using hW
  · change deriv (fun W ↦ A ((W-V)/P)/2) V=H/2
    rw [deriv_div_const,deriv_volume_reparam,sub_self,zero_div,hdA,mul_div_cancel_right₀ _ hP.ne']
  · change deriv (deriv (fun W ↦ A ((W-V)/P)/2)) V≤0
    rw [second_deriv_volume_reparam,sub_self,zero_div]
    exact div_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hddA hP.le) hP.le)
      (by norm_num)

theorem profile_upper_support_slope_nonneg {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    0≤deriv C V := by
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  apply ge_of_tendsto ht
  have hh : Iio (1/2 : ℝ)∈𝓝 V := Iio_mem_nhds hV.2
  filter_upwards [hs.above.filter_mono nhdsWithin_le_nhds,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hh,self_mem_nhdsWithin] with W hW hWh hWV
  have he := (monotoneOn_isoperimetricProfile_half
    ⟨hV.1.le,hV.2.le⟩ ⟨hV.1.le.trans hWV.le,hWh.le⟩ hWV.le).trans hW
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hs.contact ▸ he)) (sub_nonneg.mpr hWV.le)

theorem profile_upper_support_slope_nonpos {V : ℝ} (hV : V∈Ioo (1/2) 1)
    {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    deriv C V≤0 := by
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto ht
  have hh : Ioi (1/2 : ℝ)∈𝓝 V := Ioi_mem_nhds hV.1
  filter_upwards [hs.above.filter_mono nhdsWithin_le_nhds,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hh,self_mem_nhdsWithin] with W hW hWh hWV
  have he := (antitoneOn_isoperimetricProfile_half
    ⟨hWh.le,hWV.le.trans hV.2.le⟩ ⟨hV.1.le,hV.2.le⟩ hWV.le).trans hW
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hs.contact ▸ he)) (sub_nonpos.mpr hWV.le)

theorem isMinimizerAt_CMC_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (V<1/2 → 0≤H) ∧ (1/2<V → H≤0) := by
  obtain ⟨μ,H,C,hμ,hCMC,hs,hd,_⟩ := isMinimizerAt_CMC_upper_support hV hE hmin
  refine ⟨μ,H,hμ,hCMC,?_,?_⟩
  · intro hhalf
    have hn := profile_upper_support_slope_nonneg ⟨hV.1,hhalf⟩ hs
    rw [hd] at hn
    linarith
  · intro hhalf
    have hn := profile_upper_support_slope_nonpos ⟨hhalf,hV.2⟩ hs
    rw [hd] at hn
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem profile_hessian_of_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ (N : Cover → Cover) (C : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) N ∧ (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      (isoperimetricProfile V)^2*deriv (deriv C) V=
        -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle))/8 := by
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  obtain ⟨l,_hl,hflux,harea,hsecond⟩ := normal_chain_support_jets hμ hCMC hN hp hn
  have hpos : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  obtain ⟨i,f,hf,hpf,hfpos⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1)
  obtain ⟨b,hbi,hbf⟩ := exists_variation_of_function i hf hpf
  have hB : directionalFlux E b.coordinate b.function≠0 := by simpa [hbi,hbf] using hfpos.ne'
  obtain ⟨γ,hγ,hγ0,hdγ,hddγ,hvol⟩ := chain_linear_volume_correction l b hE hB
  let A : ℝ → ℝ := correctedChainArea l b γ μ
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) A 0 := correctedChainArea_smoothAt l b hγ hγ0 μ
  have hA0 : A 0=(μ.mass : ℝ) := correctedChainArea_zero l b hγ0 μ
  have hdA : deriv A 0=H*(μ.mass : ℝ) := by
    rw [correctedChainArea_deriv_zero_speed l b hγ hγ0 hdγ μ,harea]
  have hddA : deriv (deriv A) 0=
      -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)) := by
    rw [correctedChainArea_second_zero_speed l b hγ hγ0 hdγ μ,
      coordinateCMC_of_global hμ hCMC b]
    have he : deriv (deriv γ) 0*(H*directionalFlux E b.coordinate b.function)=
        -H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
      calc _ = H*(deriv (deriv γ) 0*directionalFlux E b.coordinate b.function) := by ring
           _ = _ := by rw [hddγ]; ring
    rw [he]
    simpa only [sub_eq_add_neg,neg_mul] using hsecond
  have habove : ∀ᶠ t in 𝓝 (0 : ℝ),isoperimetricProfile (V+t*(μ.mass : ℝ))≤A t/2 := by
    have hVI : ∀ᶠ t in 𝓝 (0 : ℝ),V+t*(μ.mass : ℝ)∈Icc 0 1 := by
      have hct : ContinuousAt (fun t : ℝ ↦ V+t*(μ.mass : ℝ)) 0 := by fun_prop
      exact hct.eventually (Icc_mem_nhds (by simpa using hV.1) (by simpa using hV.2))
    filter_upwards [hvol,hVI] with t ht hvt
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hve : torusVolume (chainRegion (correctedChain l b γ t) E)=
        ENNReal.ofReal (V+t*(μ.mass : ℝ)) := by
      have hv' := ht.2
      simp only [hflux,Measure.real,hmin.2.1,ENNReal.toReal_ofReal hV.1.le] at hv'
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _),hv']
    have hprofile := isoperimetricProfile_le_competitor hvt hfin hve
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (perimeter_chainRegion_le_normalArea ht.1 hE hμ)
    rw [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _)] at hreal
    exact hprofile.trans (div_le_div_of_nonneg_right hreal (by norm_num))
  let C : ℝ → ℝ := fun W ↦ A ((W-V)/(μ.mass : ℝ))/2
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun W : ℝ ↦ (W-V)/(μ.mass : ℝ)) := by fun_prop
  have hC : ContDiffAt ℝ (⊤ : ℕ∞) C V := by
    have ha : ContDiffAt ℝ (⊤ : ℕ∞) A ((V-V)/(μ.mass : ℝ)) := by simpa using hA
    exact (ha.comp V hr.contDiffAt).div_const 2
  have hCV : C V=isoperimetricProfile V := by
    simp only [C,sub_self,zero_div,hA0,hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hmin]
  refine ⟨N,C,hN,hp,hn,
    ⟨hC.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),hCV,?_⟩,?_,?_⟩
  · have ht : Tendsto (fun W : ℝ ↦ (W-V)/(μ.mass : ℝ)) (𝓝 V) (𝓝 0) := by
      simpa only [sub_self,zero_div] using hr.continuous.continuousAt.tendsto (x := V)
    filter_upwards [ht.eventually habove] with W hW
    have hi : V+(W-V)/(μ.mass : ℝ)*(μ.mass : ℝ)=W := by
      rw [div_mul_cancel₀ _ hpos.ne']; ring
    simpa only [hi,C] using hW
  · change deriv (fun W ↦ A ((W-V)/(μ.mass : ℝ))/2) V=H/2
    rw [deriv_div_const,deriv_volume_reparam,sub_self,zero_div,hdA,mul_div_cancel_right₀ _ hpos.ne']
  · rw [← hCV]
    change (A ((V-V)/(μ.mass : ℝ))/2)^2*
      deriv (deriv (fun W ↦ A ((W-V)/(μ.mass : ℝ))/2)) V=_
    rw [second_deriv_volume_reparam,sub_self,zero_div,hA0,hddA]
    field_simp [hpos.ne']
    ring

theorem isMinimizerAt_exact_profile_hessian {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover) (C : ℝ → ℝ),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      (isoperimetricProfile V)^2*deriv (deriv C) V=
        -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle))/8 := by
  obtain ⟨μ,H,hμ,hCMC,_⟩ := isMinimizerAt_ambient_stability hV hE hmin
  obtain ⟨N,C,hN,hp,hae,hs,hd,hdd⟩ := profile_hessian_of_CMC hV hE hmin hμ hCMC
  exact ⟨μ,H,N,C,hμ,hN,hp,hae,hCMC,hs,hd,hdd⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_profile_power_jet {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ C : ℝ → ℝ,Reduction.UpperSupport isoperimetricProfile C V ∧
      2*C V*deriv (deriv C) V+(deriv C V)^2≤0 := by
  obtain ⟨μ,H,N,C,hμ,hN,hp,hn,hCMC,hs,hd,hdd⟩ :=
    isMinimizerAt_exact_profile_hessian hV hE hmin
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hH := weakCMC_normal_extension hCMC hN hp hn
  have hpoint : ∀ᵐ z ∂(μ : Measure NormalBundle),H^2≤
      2*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) := by
    filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU,
      hn,hH] with z hz hnz hHz
    rw [← hHz]
    exact isMinimizerAt_mean_curvature_bound hV hE hmin hμ hN hp
      (hn.mono fun _ h ↦ h.1) z.1 hz hnz.2
  have hint := integral_mono_ae (integrable_const (H^2))
    ((integrable_normal_base (normal_curvature_continuous hN) μ).const_mul 2) hpoint
  rw [integral_const,integral_const_mul,smul_eq_mul] at hint
  have hmass : (μ : Measure NormalBundle).real univ=2*isoperimetricProfile V := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)=_
    rw [hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hmin]
    ring
  rw [hmass] at hint
  refine ⟨C,hs,?_⟩
  rw [hs.contact,hd]
  have hpos := isoperimetricProfile_pos hV
  have hmul : isoperimetricProfile V*
      (2*isoperimetricProfile V*deriv (deriv C) V+(H/2)^2)≤0 := by
    nlinarith [hdd]
  exact nonpos_of_mul_nonpos_right hmul hpos

end Periodic
end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus.Reduction

lemma second_deriv_three_halves {C : ℝ → ℝ} {x : ℝ}
    (hC : ContDiffAt ℝ 2 C x) (hp : 0<C x) :
    deriv (deriv (fun y ↦ C y^(3/2 : ℝ))) x=
      (3/4 : ℝ)*C x^(-1/2 : ℝ)*(2*C x*deriv (deriv C) x+(deriv C x)^2) := by
  have hd := (hC.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hC.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have he : deriv (fun y ↦ C y^(3/2 : ℝ)) =ᶠ[𝓝 x]
      (fun y ↦ deriv C y*(3/2 : ℝ)*C y^(1/2 : ℝ)) := by
    filter_upwards [hC.eventually (by norm_num),hC.continuousAt.eventually (Ioi_mem_nhds hp)]
      with y hy hpy
    rw [deriv_rpow_const (hy.differentiableAt (by norm_num)) (Or.inl (ne_of_gt hpy))]
    norm_num
  rw [he.deriv_eq]
  have hh := hd.rpow_const (p := (1/2 : ℝ)) (Or.inl hp.ne')
  have hprod := ((hdd.mul_const (3/2 : ℝ)).mul hh).deriv
  change deriv (fun y ↦ deriv C y*(3/2 : ℝ)*C y^(1/2 : ℝ)) x=_ at hprod
  rw [hprod]
  have hpow : C x^(1/2 : ℝ)=C x*C x^(-1/2 : ℝ) := by
    calc _ = C x^((1 : ℝ)+(-1/2 : ℝ)) := by norm_num
         _ = _ := by rw [Real.rpow_add hp,Real.rpow_one]
  norm_num only [show (1/2 : ℝ)-1=(-1/2 : ℝ) by norm_num]
  rw [hpow]
  ring_nf

theorem UpperSupport.three_halves {I C : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hI : ∀ y,0≤I y) (hp : 0<I x)
    (hj : 2*C x*deriv (deriv C) x+(deriv C x)^2≤0) :
    UpperSupport (fun y ↦ I y^(3/2 : ℝ)) (fun y ↦ C y^(3/2 : ℝ)) x ∧
      deriv (deriv (fun y ↦ C y^(3/2 : ℝ))) x≤0 := by
  have hCx : 0<C x := hs.contact ▸ hp
  refine ⟨⟨hs.smooth.rpow_const_of_ne hCx.ne',by rw [hs.contact],?_⟩,?_⟩
  · filter_upwards [hs.above] with y hy
    exact Real.rpow_le_rpow (hI y) hy (by norm_num)
  · rw [second_deriv_three_halves hs.smooth hCx]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hj

end CubicTorus.Reduction

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma candidateProfile_nonnegative {V : ℝ} (hV : V∈Icc 0 1) : 0≤candidateProfile V := by
  have hv : 0 ≤ min V (1-V) := le_min hV.1 (sub_nonneg.mpr hV.2)
  unfold candidateProfile
  dsimp only
  positivity

lemma continuous_candidateProfile : Continuous candidateProfile := by
  unfold candidateProfile
  fun_prop (disch := norm_num)

lemma candidateProfile_at_zero : candidateProfile 0=0 := by
  norm_num [candidateProfile]

lemma candidateProfile_at_one : candidateProfile 1=0 := by
  norm_num [candidateProfile]

theorem isoperimetricProfile_le_candidate {V : ℝ} (hV : V∈Icc 0 1) :
    isoperimetricProfile V≤candidateProfile V/2 := by
  rcases eq_or_lt_of_le hV.1 with h0|h0
  · rw [← h0,isoperimetricProfile_zero,candidateProfile_at_zero]; norm_num
  rcases eq_or_lt_of_le hV.2 with h1|h1
  · rw [h1,isoperimetricProfile_one,candidateProfile_at_one]; norm_num
  obtain ⟨E,hE⟩ := exists_isMinimizerAt ⟨h0,h1⟩
  rw [isoperimetricProfile_eq_of_isMinimizerAt hE]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (isMinimizerAt_perimeter_le_candidateProfile ⟨h0,h1⟩ hE)
  rwa [ENNReal.toReal_ofReal (candidateProfile_nonnegative hV)] at hh

theorem continuousOn_isoperimetricProfile :
    ContinuousOn isoperimetricProfile (Icc (0 : ℝ) 1) := by
  intro V hV
  have hc : Continuous (fun W ↦ candidateProfile W/2) := continuous_candidateProfile.div_const 2
  have hu : ∀ᶠ W in 𝓝[Icc (0 : ℝ) 1] V,isoperimetricProfile W≤candidateProfile W/2 := by
    filter_upwards [self_mem_nhdsWithin] with W hW
    exact isoperimetricProfile_le_candidate hW
  rcases eq_or_lt_of_le hV.1 with h0|h0
  · have ht := squeeze_zero' (Filter.Eventually.of_forall isoperimetricProfile_nonneg) hu
      (show Tendsto (fun W ↦ candidateProfile W/2) (𝓝[Icc (0 : ℝ) 1] V) (𝓝 0) from by
        have hh := hc.continuousAt.continuousWithinAt (s := Icc (0 : ℝ) 1) (x := V)
        simpa only [ContinuousWithinAt,← h0,candidateProfile_at_zero,zero_div] using hh)
    simpa only [ContinuousWithinAt,← h0,isoperimetricProfile_zero] using ht
  rcases eq_or_lt_of_le hV.2 with h1|h1
  · have ht := squeeze_zero' (Filter.Eventually.of_forall isoperimetricProfile_nonneg) hu
      (show Tendsto (fun W ↦ candidateProfile W/2) (𝓝[Icc (0 : ℝ) 1] V) (𝓝 0) from by
        have hh := hc.continuousAt.continuousWithinAt (s := Icc (0 : ℝ) 1) (x := V)
        simpa only [ContinuousWithinAt,h1,candidateProfile_at_one,zero_div] using hh)
    simpa only [ContinuousWithinAt,h1,isoperimetricProfile_one] using ht
  have hi := concaveOn_isoperimetricProfile.continuousOn_interior
  rw [interior_Icc] at hi
  exact ((hi V ⟨h0,h1⟩).continuousAt (Ioo_mem_nhds h0 h1)).continuousWithinAt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isoperimetricProfile_power_upper_support {V : ℝ} (hV : V∈Ioo 0 1) :
    ∃ D : ℝ → ℝ,Reduction.UpperSupport (fun W ↦ isoperimetricProfile W^(3/2 : ℝ)) D V ∧
      deriv (deriv D) V≤0 := by
  obtain ⟨E,hE⟩ := exists_isMinimizerAt hV
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmin : IsMinimizerAt V F := (isMinimizerAt_congr_ae hE.1.1.toMeasurable_ae_eq).2 hE
  obtain ⟨C,hs,hj⟩ := Periodic.isMinimizerAt_profile_power_jet hV hF hmin
  exact ⟨fun W ↦ C W^(3/2 : ℝ),hs.three_halves isoperimetricProfile_nonneg
    (isoperimetricProfile_pos hV) hj⟩

theorem concaveOn_isoperimetricProfile_three_halves :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun V ↦ isoperimetricProfile V^(3/2 : ℝ)) := by
  let J : ℝ → ℝ := fun V ↦ isoperimetricProfile V^(3/2 : ℝ)
  have hJ : ContinuousOn J (Icc (0 : ℝ) 1) := by
    exact (Real.continuous_rpow_const (by norm_num : 0≤(3/2 : ℝ))).comp_continuousOn
      continuousOn_isoperimetricProfile
  have hchord {a b : ℝ} (ha : 0≤a) (hb : b≤1) (hab : a<b) :
      ∀ x∈Icc a b,J a+(x-a)*(J b-J a)/(b-a)≤J x := by
    apply Reduction.chord_below_of_lowerSemicontinuous_upper_support hab
    · exact hJ.lowerSemicontinuousOn.mono (Icc_subset_Icc ha hb)
    · intro x hx
      exact isoperimetricProfile_power_upper_support ⟨ha.trans_lt hx.1,hx.2.trans_le hb⟩
  change ConcaveOn ℝ (Icc (0 : ℝ) 1) J
  apply LinearOrder.concaveOn_of_lt (convex_Icc (0 : ℝ) 1)
  intro x hx y hy hxy a b ha hb hab
  have hmem : a*x+b*y∈Icc x y := by
    have hax : a*x+b*x=x := by rw [← add_mul,hab,one_mul]
    have hay : a*y+b*y=y := by rw [← add_mul,hab,one_mul]
    constructor <;> nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxy.le),
      mul_nonneg hb.le (sub_nonneg.mpr hxy.le)]
  have hh := hchord hx.1 hy.2 hxy (a*x+b*y) hmem
  have he : J x+(a*x+b*y-x)*(J y-J x)/(y-x)=a*J x+b*J y := by
    have ha' : a=1-b := by linarith
    rw [ha']
    field_simp [sub_ne_zero.mpr hxy.ne']
    ring
  rw [he] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
