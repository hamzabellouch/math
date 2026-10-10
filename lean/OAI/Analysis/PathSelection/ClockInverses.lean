import Mathlib
import OAI.Analysis.PathSelection.ClockDerivatives

namespace OAI

/-! Clock inversion, logarithmic strips and exponential inverse charts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
open scoped NNReal
namespace DegeneratingTrees.Clock

lemma approximates_identity_of_deriv {f : ℂ → ℂ} {s : Set ℂ} {c : ℝ≥0}
    (hs : Convex ℝ s) (hf : AnalyticOnNhd ℂ f s)
    (hd : ∀ z ∈ s, ‖deriv f z-1‖ ≤ (c:ℝ)) :
    ApproximatesLinearOn f (ContinuousLinearEquiv.refl ℂ ℂ : ℂ →L[ℂ] ℂ) s c := by
  intro x hx y hy
  have hdf : ∀ z ∈ s, DifferentiableAt ℂ (fun w => f w-w) z :=
    fun z hz => (hf z hz).differentiableAt.sub differentiableAt_id
  have hb : ∀ z ∈ s, ‖deriv (fun w => f w-w) z‖ ≤ (c:ℝ) := by
    intro z hz
    have he : deriv (fun w => f w-w) z = deriv f z-1 := by
      simpa only [Pi.sub_apply,id_eq] using!
        ((hf z hz).differentiableAt.hasDerivAt.sub (hasDerivAt_id z)).deriv
    rw [he]
    exact hd z hz
  have h := hs.norm_image_sub_le_of_norm_deriv_le hdf hb hy hx
  change ‖f x-f y-(x-y)‖ ≤ (c:ℝ)*‖x-y‖
  convert h using 1; congr 1; ring

 

theorem analytic_near_identity_inverse {f : ℂ → ℂ} {s : Set ℂ} {c : ℝ≥0}
    (hs : IsOpen s) (hsc : Convex ℝ s) (hc : c < 1)
    (hf : AnalyticOnNhd ℂ f s) (hd : ∀ z ∈ s, ‖deriv f z-1‖ ≤ (c:ℝ)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' s) ∧
      (∀ z ∈ s, g (f z) = z) ∧
      (∀ w ∈ f '' s, g w ∈ s ∧ f (g w) = w) ∧
      (∀ z ∈ s, ∀ w ∈ s, (1-(c:ℝ))*‖z-w‖ ≤ ‖f z-f w‖) ∧
      (∀ z : ℂ, ∀ r : ℝ, 0 ≤ r → closedBall z r ⊆ s →
        closedBall (f z) ((1-(c:ℝ))*r) ⊆ f '' s) := by
  have ha := approximates_identity_of_deriv hsc hf hd
  have hcc : Subsingleton ℂ ∨ c <
      ‖((ContinuousLinearEquiv.refl ℂ ℂ).symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
    right
    simpa using hc
  let e := ha.toOpenPartialHomeomorph f s hcc hs
  have heS : e.source = s := rfl
  have heT : e.target = f '' s := rfl
  have heF : (e : ℂ → ℂ) = f := rfl
  have hdz : ∀ z ∈ s, deriv f z ≠ 0 := by
    intro z hz he
    have h1 := hd z hz
    simp only [he,zero_sub,norm_neg,norm_one] at h1
    exact (not_le_of_gt (show (c:ℝ)<1 from hc)) h1
  refine ⟨e.symm,?_,?_,?_,?_,?_⟩
  · apply (Complex.analyticOnNhd_iff_differentiableOn (by simpa [heT] using e.open_target)).mpr
    intro w hw
    have hw' : w ∈ e.target := hw
    have hg : e.symm w ∈ s := e.map_target hw'
    exact (e.hasDerivAt_symm hw' (hdz _ hg)
      (by simpa [heF] using (hf _ hg).differentiableAt.hasDerivAt)).differentiableAt.differentiableWithinAt
  · intro z hz
    exact e.left_inv hz
  · intro w hw
    exact ⟨e.map_target hw,e.right_inv hw⟩
  · intro z hz w hw
    have h := ha z hz w hw
    have ht : ‖z-w‖ ≤ ‖f z-f w‖+‖f z-f w-(z-w)‖ := by
      calc
        ‖z-w‖ = ‖(f z-f w)-(f z-f w-(z-w))‖ := by congr 1; ring
        _ ≤ ‖f z-f w‖+‖f z-f w-(z-w)‖ := norm_sub_le _ _
    change ‖f z-f w-(z-w)‖ ≤ (c:ℝ)*‖z-w‖ at h
    nlinarith
  · intro z r hr hrs
    simpa using ha.closedBall_subset_target hcc hs hr hrs

 

def horizontalTail (A R : ℝ) : Set ℂ := {z | A < z.re ∧ |z.im| < R}

lemma horizontalTail_open (A R : ℝ) : IsOpen (horizontalTail A R) :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im.abs continuous_const)

lemma horizontalTail_convex (A R : ℝ) : Convex ℝ (horizontalTail A R) := by
  have h := (convex_halfSpace_re_gt A).inter
    ((convex_halfSpace_im_gt (-R)).inter (convex_halfSpace_im_lt R))
  simpa only [horizontalTail,abs_lt,Set.ofPred_and] using h

lemma closedBall_real_subset_horizontalTail {A R r t : ℝ}
    (hr : r < R) (ht : A+r < t) : closedBall (t:ℂ) r ⊆ horizontalTail A R := by
  intro z hz
  have hn : ‖z-(t:ℂ)‖ ≤ r := mem_closedBall_iff_norm.mp hz
  have hre := (abs_re_le_norm (z-(t:ℂ))).trans hn
  have him := (abs_im_le_norm (z-(t:ℂ))).trans hn
  simp only [sub_re,sub_im,ofReal_re,ofReal_im,sub_zero] at hre him
  exact ⟨by have := (abs_le.mp hre).1; linarith,him.trans_lt hr⟩

 

theorem analytic_inverse_on_tail_strip {A R d : ℝ} (hd : 0 < d) (hdR : 2*d < R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (horizontalTail A R))
    (hderiv : ∀ z ∈ horizontalTail A R, ‖deriv f z-1‖ ≤ (1/2:ℝ))
    (hreal : ∀ t : ℝ, A < t → (f (t:ℂ)).im = 0)
    (hlim : Tendsto (fun t : ℝ => (f (t:ℂ)).re) atTop atTop) :
    ∃ (T : ℝ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g (horizontalTail T d) ∧
      (∀ w ∈ horizontalTail T d, g w ∈ horizontalTail A R ∧ f (g w) = w) ∧
      (∀ t : ℝ, A < t → f (t:ℂ) ∈ horizontalTail T d → g (f (t:ℂ)) = (t:ℂ)) ∧
      (∀ w ∈ horizontalTail T d, ∃ t : ℝ, A+2*d < t ∧
        (f (t:ℂ)).re = w.re ∧ ‖g w-(t:ℂ)‖ ≤ 2*|w.im|) := by
  have hR : 0 < R := lt_trans (by positivity) hdR
  obtain ⟨g,hga,hgf,hfg,hmetric,hball⟩ := analytic_near_identity_inverse
    (horizontalTail_open A R) (horizontalTail_convex A R)
    (c := (1/2:ℝ≥0)) (by norm_num) hf (by simpa using hderiv)
  let a := A+2*d+1
  have ha : A+2*d < a := by dsimp [a]; linarith
  have hat : A < a := by linarith
  have hcont : ContinuousOn (fun t:ℝ => (f (t:ℂ)).re) (Ici a) := by
    intro t ht
    have htf : (t:ℂ) ∈ horizontalTail A R := ⟨lt_of_lt_of_le hat ht,by simpa using hR⟩
    exact (continuous_re.continuousAt.comp ((hf _ htf).continuousAt.comp continuous_ofReal.continuousAt)).continuousWithinAt
  let T := (f (a:ℂ)).re
  have htarget : ∀ w ∈ horizontalTail T d, ∃ t : ℝ, A+2*d < t ∧
      (f (t:ℂ)).re = w.re ∧ w ∈ f '' horizontalTail A R := by
    intro w hw
    obtain ⟨t,ht,he⟩ := intermediate_value_Ici hcont hlim hw.1.le
    have hat' : A+2*d < t := ha.trans_le ht
    refine ⟨t,hat',he,?_⟩
    apply hball (t:ℂ) (2*d) (by positivity)
      (closedBall_real_subset_horizontalTail hdR hat')
    have hdiff : w-f (t:ℂ) = w.im*Complex.I := by
      apply Complex.ext <;> simp [he,hreal t (by linarith)]
    rw [mem_closedBall_iff_norm,hdiff]
    simpa only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      (show |w.im| ≤ (1-(1/2:ℝ))*(2*d) by linarith [hw.2])
  have hsub : horizontalTail T d ⊆ f '' horizontalTail A R :=
    fun w hw => (htarget w hw).choose_spec.2.2
  refine ⟨T,g,hga.mono hsub,fun w hw => hfg w (hsub hw),?_,?_⟩
  · intro t ht htf
    exact hgf (t:ℂ) ⟨ht,by simpa using hR⟩
  · intro w hw
    obtain ⟨t,ht,he,hwt⟩ := htarget w hw
    refine ⟨t,ht,he,?_⟩
    have htS : (t:ℂ) ∈ horizontalTail A R := ⟨by change A<t; linarith,by simpa using hR⟩
    have hm := hmetric (g w) (hfg w hwt).1 (t:ℂ) htS
    rw [(hfg w hwt).2] at hm
    have hdiff : w-f (t:ℂ) = w.im*Complex.I := by
      apply Complex.ext <;> simp [he,hreal t (by linarith)]
    rw [hdiff] at hm
    simp only [norm_mul, norm_real,Real.norm_eq_abs,norm_I,mul_one] at hm
    norm_num at hm
    linarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
namespace DegeneratingTrees.Clock

def stripInfinity : Filter ℂ where
  sets := {s | ∀ R : ℝ,∃ A : ℝ,horizontalTail A R ⊆ s}
  univ_sets := fun _ => ⟨0,subset_univ _⟩
  sets_of_superset := fun h hs R => by obtain ⟨A,hA⟩ := h R; exact ⟨A,hA.trans hs⟩
  inter_sets := fun h k R => by
    obtain ⟨A,hA⟩ := h R
    obtain ⟨B,hB⟩ := k R
    exact ⟨max A B,fun z hz => ⟨hA ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩,
      hB ⟨(le_max_right _ _).trans_lt hz.1,hz.2⟩⟩⟩

lemma eventually_stripInfinity {P : ℂ → Prop} :
    (∀ᶠ z in stripInfinity,P z) ↔ ∀ R : ℝ,∃ A : ℝ,∀ z∈horizontalTail A R,P z := Iff.rfl

instance stripInfinity_neBot : NeBot stripInfinity := by
  refine ⟨?_⟩
  intro h
  have hem : (∅ : Set ℂ)∈stripInfinity := by rw [h]; simp
  obtain ⟨A,hA⟩ := hem 1
  exact hA (show ((A+1:ℝ):ℂ)∈horizontalTail A 1 from ⟨by simp,by simp⟩)

lemma stripInfinity_le_sectorInfinity : stripInfinity ≤ sectorInfinity := by
  intro s hs
  obtain ⟨ω,S,hω,hS⟩ := hs
  intro R
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hω.real_discs S)
  refine ⟨max T (4*R),?_⟩
  intro z hz
  apply hS z ((hT z.re ((le_max_left _ _).trans hz.1.le)).2 ?_)
  rw [mem_closedBall_iff_norm]
  have he : z-(z.re:ℂ)=(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have hr := (le_max_right T (4*R)).trans_lt hz.1
  linarith [hz.2]

lemma tendsto_real_stripInfinity : Tendsto (fun t : ℝ => (t:ℂ)) atTop stripInfinity := by
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨A,hA⟩ := hs 1
  filter_upwards [eventually_gt_atTop A] with t ht
  exact hA ⟨ht,by simp⟩

lemma tendsto_re_stripInfinity : Tendsto Complex.re stripInfinity atTop := by
  apply Filter.tendsto_atTop.mpr
  intro A R
  exact ⟨A,fun z hz => hz.1.le⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma SectorExpansion.log_deriv_tendsto {F : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F E b) (ha : ∀ β∈E,∀ᶠ z in sectorInfinity,AnalyticAt ℂ (b β) z)
    {β : ℝ} (hβ : β∈E) (hmax : ∀ γ∈E,γ≤β)
    (hb0 : ∀ᶠ z in sectorInfinity,b β z≠0) (hbi : SectorSlow (fun z => (b β z)⁻¹))
    (hq : Tendsto (fun z => _root_.deriv (b β) z/b β z) sectorInfinity (𝓝 0)) :
    Tendsto (fun z => _root_.deriv F z/F z) sectorInfinity (𝓝 (β:ℂ)) := by
  have hFd := hF.deriv ha
  have herr := ((hFd.leading_error hβ hmax).mul (ExpBound.cexp (-β))).mul_slow hbi
  simp only [add_neg_cancel] at herr
  have hn : Tendsto (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*(b β z)⁻¹*_root_.deriv F z)
      sectorInfinity (𝓝 (β:ℂ)) := by
    have ht := herr.tendsto_zero.add ((tendsto_const_nhds (x := (β:ℂ))).add hq)
    simp only [add_zero,zero_add] at ht
    apply ht.congr'
    filter_upwards [hb0] with z hz
    have he : Complex.exp (((-β:ℝ):ℂ)*z)=(Complex.exp ((β:ℂ)*z))⁻¹ := by
      rw [←Complex.exp_neg]; congr 1; push_cast; ring
    rw [he]
    field_simp [hz,Complex.exp_ne_zero]
    ring
  have hu := hF.uniform_leading_tendsto hβ hmax hb0 hbi
  have ht := hn.div hu (by norm_num : (1:ℂ)≠0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [hb0,hF.eventually_ne_of_leading hβ hmax hb0 hbi] with z hz hFz
  change (Complex.exp (((-β:ℝ):ℂ)*z)*(b β z)⁻¹*_root_.deriv F z) /
    (Complex.exp (((-β:ℝ):ℂ)*z)*(b β z)⁻¹*F z)=_root_.deriv F z/F z
  field_simp [hz,hFz,Complex.exp_ne_zero]

 

theorem ExpansionOver.puiseux_log_deriv {F : ℂ → ℂ} (hF : ExpansionOver PuiseuxSector F)
    (hne : ¬ (fun t : ℝ => F (t:ℂ)) =ᶠ[atTop] fun _ => 0) :
    ∃ β : ℝ,∃ b : ℂ → ℂ,b∈PuiseuxSector ∧
      (¬ (fun t : ℝ => b (t:ℂ)) =ᶠ[atTop] fun _ => 0) ∧
      ExpSmall 0 (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*(b z)⁻¹*F z-1) ∧
      (∀ᶠ z in sectorInfinity,F z≠0) ∧
      Tendsto (fun z => deriv F z/F z) sectorInfinity (𝓝 (β:ℂ)) := by
  obtain ⟨E,b,hF,hb⟩ := hF
  have ht := hF.trim_zero (fun β hβ => (hb β hβ).1)
  have hn : (nonzeroRaySupport E b).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he] at ht
    exact hne ht.empty
  obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above ht.finite_above hn
  have hbi := puiseux_lowerSectorData.slow (puiseux_lowerSectorData.inv_mem (hb β hβ.1))
  have hb0 : ∀ᶠ z in sectorInfinity,b β z≠0 := by
    rcases puiseux_lowerSectorData.zero_or_ne (hb β hβ.1) with hz | hz
    · exact False.elim (hβ.2 (tendsto_real_sectorInfinity.eventually hz))
    · exact hz
  exact ⟨β,b β,hb β hβ.1,hβ.2,ht.uniform_leading hβ hmax hb0 hbi,
    ht.eventually_ne_of_leading hβ hmax hb0 hbi,
    ht.log_deriv_tendsto (fun γ hγ => (hb γ hγ.1).1) hβ hmax hb0 hbi
      (PuiseuxSector.log_deriv_tendsto (hb β hβ.1) hβ.2)⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma analytic_log_on_convex {S : Set ℂ} (hSo : IsOpen S) (hSc : Convex ℝ S)
    (hSn : S.Nonempty) {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H S)
    (hH0 : ∀ z∈S,H z≠0) :
    ∃ L : ℂ → ℂ,AnalyticOnNhd ℂ L S ∧ (∀ z∈S,Complex.exp (L z)=H z) ∧
      ∀ z∈S,deriv L z=deriv H z/H z := by
  let := hSc.contractibleSpace hSn
  have hsim : IsSimplyConnected S := by change SimplyConnectedSpace S; infer_instance
  obtain ⟨L,hLc,hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsim hSo hH.continuousOn
    (by rintro ⟨z,hz,he⟩; exact hH0 z hz he)
  have hd (z : ℂ) (hz : z∈S) : HasDerivAt L (deriv H z/H z) z := by
    have hh := HasDerivAt.of_comp_left ((hLc z hz).continuousAt (hSo.mem_nhds hz))
      (Complex.hasDerivAt_exp (L z)) (hH z hz).differentiableAt.hasDerivAt
      (Complex.exp_ne_zero _) (Filter.Eventually.mono (hSo.mem_nhds hz) (fun w hw => hLe hw))
    simpa only [show Complex.exp (L z)=H z from hLe hz] using hh
  refine ⟨L,?_,fun z hz => hLe hz,fun z hz => (hd z hz).deriv⟩
  exact (Complex.analyticOnNhd_iff_differentiableOn hSo).mpr
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)

lemma analytic_ray_deriv_im_zero {H : ℂ → ℂ} {A t : ℝ} (ht : A<t)
    (ha : AnalyticAt ℂ H (t:ℂ)) (hr : ∀ t : ℝ,A<t → (H (t:ℂ)).im=0) :
    (deriv H (t:ℂ)).im=0 := by
  have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ha.differentiableAt.hasDerivAt.comp_ofReal
  have he : (fun s : ℝ => (H (s:ℂ)).im) =ᶠ[𝓝 t] fun _ => 0 :=
    (eventually_gt_nhds ht).mono (fun s hs => hr s hs)
  have hz : HasDerivAt (fun s : ℝ => (H (s:ℂ)).im) 0 t :=
    (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he
  exact hh.unique hz

 

theorem analytic_real_log_on_strip {A R : ℝ} (hR : 0<R) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H (horizontalTail A R))
    (hH0 : ∀ z∈horizontalTail A R,H z≠0)
    (hreal : ∀ t : ℝ,A<t → (H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re) :
    ∃ L : ℂ → ℂ,AnalyticOnNhd ℂ L (horizontalTail A R) ∧
      (∀ z∈horizontalTail A R,Complex.exp (L z)=H z) ∧
      (∀ z∈horizontalTail A R,deriv L z=deriv H z/H z) ∧
      ∀ t : ℝ,A<t → L (t:ℂ)=(Real.log (H (t:ℂ)).re : ℂ) := by
  have hray (t : ℝ) (ht : A<t) : (t:ℂ)∈horizontalTail A R := ⟨ht,by simpa using hR⟩
  obtain ⟨L,hLa,hLe,hLd⟩ := analytic_log_on_convex (horizontalTail_open A R)
    (horizontalTail_convex A R) ⟨((A+1:ℝ):ℂ),hray _ (by linarith)⟩ hH hH0
  have himder (t : ℝ) (ht : A<t) : HasDerivAt (fun t : ℝ => (L (t:ℂ)).im) 0 t := by
    have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (hLa _ (hray t ht)).differentiableAt.hasDerivAt.comp_ofReal
    have hHz : (deriv H (t:ℂ)).im=0 := analytic_ray_deriv_im_zero ht
      (hH _ (hray t ht)) (fun s hs => (hreal s hs).1)
    have hi : (deriv L (t:ℂ)).im=0 := by
      rw [hLd _ (hray t ht),Complex.div_im,hHz,(hreal t ht).1]
      simp
    change HasDerivAt (fun t : ℝ => (L (t:ℂ)).im) (deriv L (t:ℂ)).im t at hd
    rwa [hi] at hd
  have himconst (t : ℝ) (ht : A<t) : (L (t:ℂ)).im=(L ((A+1:ℝ):ℂ)).im := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi A).isPreconnected
      (fun t ht => (himder t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (himder t ht).deriv) ht (by change A<A+1; linarith)
  let t0 : ℝ := A+1
  have ht0 : A<t0 := by dsimp [t0]; linarith
  have h0eq : H (t0:ℂ) = ((H (t0:ℂ)).re:ℂ) := Complex.ext (by simp) (by simp [(hreal t0 ht0).1])
  let K : ℂ → ℂ := fun z => L z-L (t0:ℂ)+(Real.log (H (t0:ℂ)).re:ℂ)
  have hKexp (z : ℂ) (hz : z∈horizontalTail A R) : Complex.exp (K z)=H z := by
    dsimp [K]
    rw [Complex.exp_add,Complex.exp_sub,hLe _ hz,hLe _ (hray t0 ht0),←Complex.ofReal_exp,
      Real.exp_log (hreal t0 ht0).2,←h0eq]
    exact div_mul_cancel₀ _ (hH0 _ (hray t0 ht0))
  refine ⟨K,fun z hz => ((hLa z hz).sub analyticAt_const).add analyticAt_const,
    hKexp,?_,?_⟩
  · intro z hz
    have hd := ((hLa z hz).differentiableAt.hasDerivAt.sub_const (L (t0:ℂ))).add_const
      (Real.log (H (t0:ℂ)).re:ℂ)
    exact hd.deriv.trans (hLd z hz)
  · intro t ht
    have hi : (K (t:ℂ)).im=0 := by simp only [K,sub_im,add_im,ofReal_im,add_zero]; exact sub_eq_zero.mpr (himconst t ht)
    have hn := congrArg norm (hKexp (t:ℂ) (hray t ht))
    rw [Complex.norm_exp] at hn
    have hnorm : ‖H (t:ℂ)‖=(H (t:ℂ)).re := by
      have heq : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext (by simp) (by simp [(hreal t ht).1])
      rw [heq,Complex.norm_of_nonneg (hreal t ht).2.le]
      rfl
    rw [hnorm] at hn
    have hre := congrArg Real.log hn
    rw [Real.log_exp] at hre
    exact Complex.ext (by simpa using hre) (by simpa using hi)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

 

theorem normalized_log_inverse {H : ℂ → ℂ} {b d R : ℝ}
    (hb : 0<b) (hd : 0<d) (hdR : 2*d<R)
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (h0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hlim : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hq : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ))) :
    ∃ (A T : ℝ) (f g : ℂ → ℂ),
      AnalyticOnNhd ℂ f (horizontalTail A R) ∧
      (∀ z∈horizontalTail A R,Complex.exp ((b:ℂ)*f z)=H z) ∧
      (∀ z∈horizontalTail A R,‖deriv f z-1‖≤(1/2:ℝ)) ∧
      (∀ z∈horizontalTail A R,deriv f z=(deriv H z/H z)/(b:ℂ)) ∧
      (∀ t : ℝ,A<t → f (t:ℂ)=((Real.log (H (t:ℂ)).re/b:ℝ):ℂ)) ∧
      AnalyticOnNhd ℂ g (horizontalTail T d) ∧
      (∀ w∈horizontalTail T d,g w∈horizontalTail A R ∧ f (g w)=w) ∧
      (∀ t : ℝ,A<t → f (t:ℂ)∈horizontalTail T d → g (f (t:ℂ))=(t:ℂ)) ∧
      (∀ w∈horizontalTail T d,∃ t : ℝ,A+2*d<t ∧
        (f (t:ℂ)).re=w.re ∧ ‖g w-(t:ℂ)‖≤2*|w.im|) := by
  have hR : 0<R := lt_trans (by positivity) hdR
  have hb0 : (b:ℂ)≠0 := by exact_mod_cast hb.ne'
  have he : ∀ᶠ z in stripInfinity,‖deriv H z/H z-(b:ℂ)‖<b/2 := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hq (b/2) (by positivity)
  obtain ⟨A₀,hA₀⟩ := eventually_stripInfinity.mp ((ha.and h0).and he) R
  obtain ⟨A₁,hA₁⟩ := eventually_atTop.mp hr
  let A := max A₀ A₁
  have hs : horizontalTail A R ⊆ horizontalTail A₀ R :=
    fun z hz => ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩
  have hreal (t : ℝ) (ht : A<t) := hA₁ t ((le_max_right _ _).trans ht.le)
  obtain ⟨L,hLa,hLe,hLd,hLr⟩ := analytic_real_log_on_strip hR
    (fun z hz => (hA₀ z (hs hz)).1.1) (fun z hz => (hA₀ z (hs hz)).1.2) hreal
  let f : ℂ → ℂ := fun z => L z/(b:ℂ)
  have hfa : AnalyticOnNhd ℂ f (horizontalTail A R) := fun z hz => (hLa z hz).div_const
  have hfd (z : ℂ) (hz : z∈horizontalTail A R) : deriv f z=(deriv H z/H z)/(b:ℂ) := by
    rw [show deriv f z=deriv L z/(b:ℂ) from ((hLa z hz).differentiableAt.hasDerivAt.div_const (b:ℂ)).deriv]
    rw [hLd z hz]
  have hfn (z : ℂ) (hz : z∈horizontalTail A R) : ‖deriv f z-1‖≤(1/2:ℝ) := by
    rw [hfd z hz,show (deriv H z/H z)/(b:ℂ)-1=(deriv H z/H z-(b:ℂ))/(b:ℂ) by field_simp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
    exact (div_le_iff₀ hb).mpr (by linarith [(hA₀ z (hs hz)).2])
  have hfr (t : ℝ) (ht : A<t) : f (t:ℂ)=((Real.log (H (t:ℂ)).re/b:ℝ):ℂ) := by
    dsimp [f]; rw [hLr t ht]; push_cast; rfl
  have hfl : Tendsto (fun t : ℝ => (f (t:ℂ)).re) atTop atTop := by
    apply ((Real.tendsto_log_atTop.comp hlim).atTop_div_const hb).congr'
    filter_upwards [eventually_gt_atTop A] with t ht
    rw [hfr t ht,Complex.ofReal_re]
    rfl
  obtain ⟨T,g,hga,hgf,hfg,hgb⟩ := analytic_inverse_on_tail_strip hd hdR hfa hfn
    (fun t ht => by rw [hfr t ht]; simp) hfl
  refine ⟨A,T,f,g,hfa,?_,hfn,hfd,hfr,hga,hgf,hfg,hgb⟩
  intro z hz
  simpa [f,mul_div_cancel₀ _ hb0] using hLe z hz

 

theorem positive_exponential_inverse {H : ℂ → ℂ} {b : ℝ} (hb : 0<b)
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (h0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hlim : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hq : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ))) :
    ∃ A T : ℝ,0<T ∧ ∃ x : ℂ → ℂ,
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → ∃ t : ℝ,A<t ∧
        H (t:ℂ)=(‖w‖:ℂ) ∧ ‖x w-(t:ℂ)‖≤2*|w.arg|/b) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) := by
  let d := Real.pi/(2*b)+1
  let R := 2*d+1
  have hd : 0<d := by dsimp [d]; positivity
  have hdR : 2*d<R := by dsimp [R]; linarith
  obtain ⟨A,T₀,f,g,hfa,hfe,hfn,hfd,hfr,hga,hgf,hfg,hgb⟩ :=
    normalized_log_inverse hb hd hdR ha h0 hr hlim hq
  let T := Real.exp (b*T₀)
  let x : ℂ → ℂ := fun w => g (Complex.log w/(b:ℂ))
  have hmap (w : ℂ) (hw : 0<w.re) (hT : T<‖w‖) :
      Complex.log w/(b:ℂ)∈horizontalTail T₀ d := by
    constructor
    · rw [Complex.div_ofReal_re,Complex.log_re]
      apply (lt_div_iff₀ hb).mpr
      have hh := Real.log_lt_log (Real.exp_pos (b*T₀)) hT
      rw [Real.log_exp] at hh
      nlinarith
    · rw [Complex.div_ofReal_im,Complex.log_im,abs_div,abs_of_pos hb]
      have hh := (Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hw)
      apply lt_trans ((div_lt_div_iff_of_pos_right hb).mpr hh)
      dsimp [d]; rw [div_div]; linarith
  have hzero (w : ℂ) (hw : 0<w.re) : w≠0 := by intro he; simp [he] at hw
  refine ⟨A,T,Real.exp_pos _,x,?_,?_,?_,?_⟩
  · intro w hw
    exact (hga _ (hmap w hw.1 hw.2)).comp (f := fun w => Complex.log w/(b:ℂ))
      ((analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hw.1))).div_const)
  · intro w hw hT
    have hh := hgf _ (hmap w hw hT)
    rw [←hfe _ hh.1,hh.2,mul_div_cancel₀ _ (show (b:ℂ)≠0 by exact_mod_cast hb.ne')]
    exact Complex.exp_log (hzero w hw)
  · intro w hw hT
    obtain ⟨t,ht,htr,htb⟩ := hgb _ (hmap w hw hT)
    have hat : A<t := by linarith
    refine ⟨t,hat,?_,?_⟩
    · rw [hfr t hat,Complex.ofReal_re,Complex.div_ofReal_re,Complex.log_re] at htr
      have hh : Real.log (H (t:ℂ)).re=Real.log ‖w‖ := (div_left_inj' hb.ne').mp htr
      have htS : (t:ℂ)∈horizontalTail A R := ⟨hat,by simpa using (show 0<R by linarith)⟩
      rw [←hfe _ htS,hfr t hat,←Complex.ofReal_mul]
      rw [mul_div_cancel₀ _ hb.ne',hh,←Complex.ofReal_exp,Real.exp_log (lt_trans (Real.exp_pos _) hT)]
    · simpa only [x,Complex.div_ofReal_im,Complex.log_im,abs_div,abs_of_pos hb,mul_div_assoc] using htb
  · have htlim : Tendsto (fun t : ℝ => (f (t:ℂ)).re) atTop atTop := by
      apply ((Real.tendsto_log_atTop.comp hlim).atTop_div_const hb).congr'
      filter_upwards [eventually_gt_atTop A] with t ht
      rw [hfr t ht,Complex.ofReal_re]
      rfl
    filter_upwards [eventually_gt_atTop A,hr,htlim.eventually (eventually_gt_atTop T₀)] with t ht hrt hft
    have hfstrip : f (t:ℂ)∈horizontalTail T₀ d := ⟨hft,by rw [hfr t ht]; simpa using hd⟩
    have hHreal : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext (by simp) (by simp [hrt.1])
    have hh : Complex.log (H (t:ℂ))/(b:ℂ)=f (t:ℂ) := by
      rw [hHreal,←Complex.ofReal_log hrt.2.le,hfr t ht,Complex.ofReal_div]
    dsimp [x]; rw [hh]; exact hfg t ht hfstrip

end DegeneratingTrees.Clock
end

end OAI
