import Mathlib
import OAI.Analysis.PathSelection.PuiseuxCalculus

namespace OAI

/-! Puiseux inverses, composition and sector bounds. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma rootCoord_inverse_power {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (rootCoord n x)^(-(n:ℤ)) = x := by
  rw [rootCoord_zpow hx]
  have hd : -(-((n:ℤ):ℝ))/(n:ℝ) = 1 := by
    push_cast
    field_simp
  push_cast at *
  rw [hd,Real.rpow_one]

lemma rootCoord_monomial {k : ℕ} (hk : 0 < k) {u a : ℝ}
    (hu : 0 < u) (ha : 0 < a) :
    rootCoord k (u^(-(k:ℤ))*a) = u * (a^(-(k:ℝ)⁻¹)) := by
  rw [rootCoord,Real.mul_rpow (zpow_pos hu _).le ha.le]
  congr 1
  rw [←Real.rpow_intCast,←Real.rpow_mul hu.le]
  have hd : ((-(k:ℤ)):ℝ)*(-(k:ℝ)⁻¹) = 1 := by
    push_cast
    field_simp
  push_cast at *
  rw [hd,Real.rpow_one]

 

lemma tail_right_inverse {f : ℝ → ℝ}
    (hf : ∀ᶠ x in atTop, ContinuousAt f x) (hlim : Tendsto f atTop atTop) :
    ∃ g : ℝ → ℝ, Tendsto g atTop atTop ∧
      (∀ᶠ y in atTop, f (g y) = y) := by
  classical
  obtain ⟨T,hT⟩ := eventually_atTop.mp hf
  have hc : ContinuousOn f (Ici T) := fun x hx => (hT x hx).continuousWithinAt
  have he (y : ℝ) (hy : f T ≤ y) : ∃ x ∈ Ici T, f x = y :=
    intermediate_value_Ici hc hlim hy
  choose a ha using he
  let g : ℝ → ℝ := fun y => if hy : f T ≤ y then a y hy else T
  have hg (y : ℝ) (hy : f T ≤ y) : T ≤ g y ∧ f (g y) = y := by
    simpa only [g,dite_eq_left hy,Set.mem_Ici] using ha y hy
  refine ⟨g,?_,(eventually_ge_atTop (f T)).mono (fun y hy => (hg y hy).2)⟩
  rw [Filter.tendsto_atTop]
  intro M
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := T) (b := max T M)).bddAbove_image
    (hc.mono (Icc_subset_Ici_self))
  filter_upwards [eventually_ge_atTop (f T),eventually_gt_atTop B] with y hy hyB
  by_contra h
  have hM : g y ∈ Icc T (max T M) := ⟨(hg y hy).1,(not_le.mp h).le.trans (le_max_right _ _)⟩
  have := hB (mem_image_of_mem f hM)
  rw [(hg y hy).2] at this
  linarith

lemma Puiseux.normalize_unbounded_real {f : ℝ → ℝ}
    (hf : Puiseux (fun x => (f x:ℂ))) (hlim : Tendsto f atTop atTop) :
    ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ ∃ F : ℂ → ℂ,
      AnalyticAt ℂ F 0 ∧ 0 < (F 0).re ∧ (F 0).im = 0 ∧
      (fun x => (f x:ℂ)) =ᶠ[atTop]
        fun x => ((rootCoord n x)^(-(k:ℤ)) : ℝ) • F (rootCoord n x) := by
  have hne : ¬ (fun x => (f x:ℂ)) =ᶠ[atTop] fun _ => 0 := by
    intro he
    have hz : f =ᶠ[atTop] fun _ => 0 := he.mono fun x hx => by simpa only [Pi.ofNat_apply,Complex.ofReal_eq_zero] using hx
    exact not_tendsto_nhds_of_tendsto_atTop hlim 0 (tendsto_const_nhds.congr' hz.symm)
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.normalize hne
  have hm : m < 0 := by
    by_contra h
    have hm : 0 ≤ m := le_of_not_gt h
    have ht := ((rootCoord_tendsto_zero hn).pow m.toNat).smul
      (hF.continuousAt.tendsto.comp (rootCoord_complex_tendsto_zero hn))
    have ht' : Tendsto (fun x => (f x:ℂ)) atTop (𝓝 (((0:ℝ)^m.toNat) • F 0)) := by
      apply ht.congr'
      filter_upwards [he] with x hx
      simpa only [←zpow_natCast,Int.toNat_of_nonneg hm,Function.comp_def] using hx.symm
    have hr := Complex.continuous_re.continuousAt.tendsto.comp ht'
    exact not_tendsto_nhds_of_tendsto_atTop hlim _ (by simpa only [Function.comp_def,Complex.ofReal_re] using hr)
  let k := (-m).toNat
  have hk : 0 < k := by dsimp [k]; omega
  have hmk : m = -(k:ℤ) := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (neg_nonneg.mpr hm.le),neg_neg]
  have hreal : ∀ᶠ x : ℝ in atTop, (F (rootCoord n x)).im = 0 ∧
      0 < (F (rootCoord n x)).re := by
    filter_upwards [he,eventually_gt_atTop (0:ℝ),hlim.eventually (eventually_gt_atTop (0:ℝ))]
      with x hx hxpos hfpos
    have hp : 0 < (rootCoord n x)^m := zpow_pos (rootCoord_pos hxpos) _
    have hi := congrArg Complex.im hx
    have hr := congrArg Complex.re hx
    simp only [Complex.ofReal_im,Complex.smul_im,Complex.ofReal_re,Complex.smul_re,smul_eq_mul] at hi hr
    exact ⟨(mul_eq_zero.mp hi.symm).resolve_left hp.ne',by nlinarith⟩
  have him : (F 0).im = 0 := by
    have hi := Complex.continuous_im.continuousAt.tendsto.comp
      (hF.continuousAt.tendsto.comp (rootCoord_complex_tendsto_zero hn))
    exact tendsto_nhds_unique hi ((tendsto_const_nhds (x := (0:ℝ))).congr' (hreal.mono fun x hx => hx.1.symm))
  have hre : 0 ≤ (F 0).re := ge_of_tendsto
    (Complex.continuous_re.continuousAt.tendsto.comp
      (hF.continuousAt.tendsto.comp (rootCoord_complex_tendsto_zero hn)))
    (hreal.mono fun x hx => hx.2.le)
  have hrne : (F 0).re ≠ 0 := by
    intro hz
    exact hF0 (Complex.ext hz him)
  exact ⟨n,k,hn,hk,F,hF,lt_of_le_of_ne hre hrne.symm,him,by simpa only [hmk] using he⟩

 
lemma analytic_inverse_factor {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (hQ0 : Q 0 ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      ∀ᶠ u in 𝓝 (0:ℂ), (u*Q u)*H (u*Q u) = u := by
  let P : ℂ → ℂ := fun u => u*Q u
  have hP : AnalyticAt ℂ P 0 := analyticAt_id.mul hQ
  have hP0 : P 0 = 0 := by simp [P]
  have hd : deriv P 0 = Q 0 := by
    simpa [P,Pi.mul_def,id_eq] using ((hasDerivAt_id (0:ℂ)).mul hQ.differentiableAt.hasDerivAt).deriv
  have hd0 : deriv P 0 ≠ 0 := hd ▸ hQ0
  let G := hP.hasStrictDerivAt.localInverse _ _ _ hd0
  have hG : AnalyticAt ℂ G 0 := hP0 ▸ hP.analyticAt_localInverse hd0
  have he : ∀ᶠ u in 𝓝 (0:ℂ), G (P u) = u :=
    hP.hasStrictDerivAt.eventually_left_inverse hd0
  have hG0 : G 0 = 0 := by simpa only [hP0] using he.self_of_nhds
  have hdG : deriv G 0 = (deriv P 0)⁻¹ := by
    simpa only [hP0] using (hP.hasStrictDerivAt.to_localInverse hd0).hasDerivAt.deriv
  refine ⟨dslope G 0,hG.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt,?_,?_⟩
  · simpa only [dslope_same,hdG,ne_eq,inv_eq_zero] using hd0
  · filter_upwards [he] with u hu
    have h := sub_smul_dslope G 0 (P u)
    simpa only [sub_zero,hG0,smul_eq_mul,hu] using h

 

theorem Puiseux.inverse_change {f : ℝ → ℝ}
    (hf : Puiseux (fun x => (f x:ℂ))) (hlim : Tendsto f atTop atTop) :
    ∃ g : ℝ → ℝ, Puiseux (fun y => (g y:ℂ)) ∧ Tendsto g atTop atTop ∧
      (∀ᶠ y in atTop, f (g y) = y) ∧ (∀ᶠ x in atTop, g (f x) = x) := by
  obtain ⟨n,k,hn,hk,F,hF,hFre,hFim,he⟩ := hf.normalize_unbounded_real hlim
  let Q : ℂ → ℂ := fun u => (F u)^(-(k:ℂ)⁻¹)
  have hslit : F 0 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hFre)
  have hQ : AnalyticAt ℂ Q 0 := hF.cpow analyticAt_const hslit
  have hF0 : F 0 ≠ 0 := by intro hz; simp [hz] at hFre
  have hQ0 : Q 0 ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hF0)
  obtain ⟨H,hH,hH0,hHinv⟩ := analytic_inverse_factor hQ hQ0
  have hcoord : ∀ᶠ x : ℝ in atTop,
      (rootCoord k (f x):ℂ)*H (rootCoord k (f x)) = (rootCoord n x:ℂ) := by
    filter_upwards [he,eventually_gt_atTop (0:ℝ),hlim.eventually (eventually_gt_atTop (0:ℝ)),
      (rootCoord_complex_tendsto_zero hn).eventually hHinv] with x hx hxp hfpos hInv
    have hpow : 0 < (rootCoord n x)^(-(k:ℤ)) := zpow_pos (rootCoord_pos hxp) _
    have hi := congrArg Complex.im hx
    have hr := congrArg Complex.re hx
    simp only [Complex.ofReal_im,Complex.smul_im,Complex.ofReal_re,Complex.smul_re,smul_eq_mul] at hi hr
    have him : (F (rootCoord n x)).im = 0 := (mul_eq_zero.mp hi.symm).resolve_left hpow.ne'
    have hre : 0 < (F (rootCoord n x)).re := by nlinarith
    have hreal : F (rootCoord n x) = ((F (rootCoord n x)).re:ℂ) := by
      apply Complex.ext <;> simp [him]
    have hroot : (rootCoord k (f x):ℂ) = (rootCoord n x:ℂ)*Q (rootCoord n x) := by
      rw [hr,rootCoord_monomial hk (rootCoord_pos hxp) hre,Complex.ofReal_mul,
        Complex.ofReal_cpow hre.le]
      simp only [Q,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_natCast]
      rw [hreal]
      simp only [Complex.ofReal_re]
    simpa only [hroot] using hInv
  obtain ⟨g,hg,hfg⟩ := tail_right_inverse
    (hf.real_eventually_analytic.mono fun _ h => h.continuousAt) hlim
  have hgcoord : ∀ᶠ y : ℝ in atTop,
      ((rootCoord k y:ℂ)*H (rootCoord k y))^(-(n:ℤ)) = (g y:ℂ) := by
    filter_upwards [hg.eventually hcoord,hfg,hg.eventually (eventually_gt_atTop (0:ℝ))]
      with y hy hfy hgy
    rw [hfy] at hy
    rw [hy,←Complex.ofReal_zpow,rootCoord_inverse_power hn hgy]
  have hgP : Puiseux (fun y => (g y:ℂ)) := by
    refine ⟨k,hk,-(n:ℤ),fun u => (H u)^(-(n:ℤ)),hH.zpow hH0,?_⟩
    filter_upwards [hgcoord] with y hy
    rw [←hy,mul_zpow,←Complex.ofReal_zpow,Complex.real_smul]
  refine ⟨g,hgP,hg,hfg,?_⟩
  filter_upwards [hcoord,hlim.eventually hgcoord,eventually_gt_atTop (0:ℝ)] with x hx hgf hxp
  apply Complex.ofReal_injective
  rw [←hgf,hx,←Complex.ofReal_zpow,rootCoord_inverse_power hn hxp]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

 

def radialInfinity : Filter ℂ := comap norm atTop

def complexRoot (n : ℕ) (z : ℂ) : ℂ := z ^ ((-(n:ℝ)⁻¹ : ℝ):ℂ)

lemma complexRoot_norm (n : ℕ) (z : ℂ) :
    ‖complexRoot n z‖ = rootCoord n ‖z‖ := Complex.norm_cpow_real _ _

lemma complexRoot_real {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    complexRoot n (x:ℂ) = (rootCoord n x:ℂ) := (Complex.ofReal_cpow hx _).symm

lemma complexRoot_tendsto_zero {n : ℕ} (hn : 0 < n) :
    Tendsto (complexRoot n) radialInfinity (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [complexRoot_norm,Function.comp_def,radialInfinity] using
    (rootCoord_tendsto_zero hn).comp (tendsto_comap : Tendsto (norm : ℂ → ℝ) radialInfinity atTop)

lemma complexRoot_analytic {n : ℕ} {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (complexRoot n) z :=
  analyticAt_id.cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hz))

lemma complexRoot_zpow (n : ℕ) (m : ℤ) (z : ℂ) :
    (complexRoot n z)^m = z ^ ((-(m:ℝ)/(n:ℝ):ℝ):ℂ) := by
  rw [complexRoot,←Complex.cpow_mul_int]
  congr 1
  push_cast
  ring

lemma radial_eventually {P : ℂ → Prop} (hP : ∀ᶠ z in radialInfinity, P z) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → P z := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (eventually_comap.mp hP)
  exact ⟨R,fun z hz => hR ‖z‖ hz.le z rfl⟩

 

theorem Puiseux.sector_leading {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    ∃ (q : ℚ) (C : ℂ) (G : ℂ → ℂ) (R : ℝ), C ≠ 0 ∧
      (∀ z : ℂ, R < ‖z‖ → 0 < z.re → AnalyticAt ℂ G z) ∧
      f =ᶠ[atTop] (fun t => G (t:ℂ)) ∧
      Tendsto (fun z => (z ^ ((q:ℝ):ℂ))⁻¹ * G z) radialInfinity (𝓝 C) := by
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.normalize hne
  let q : ℚ := -(m:ℚ)/(n:ℚ)
  let G : ℂ → ℂ := fun z => (complexRoot n z)^m * F (complexRoot n z)
  have hqa : ((q:ℝ):ℂ) = ((-(m:ℝ)/(n:ℝ):ℝ):ℂ) := by dsimp [q]; push_cast; rfl
  obtain ⟨R,hR⟩ := radial_eventually ((complexRoot_tendsto_zero hn).eventually hF.eventually_analyticAt)
  refine ⟨q,F 0,G,R,hF0,?_,?_,?_⟩
  · intro z hz hzre
    have hr := complexRoot_analytic (n := n) hzre
    have hr0 : complexRoot n z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by intro h; simp [h] at hzre))
    exact (hr.zpow hr0).mul ((hR z hz).comp hr)
  · filter_upwards [he,eventually_gt_atTop (0:ℝ)] with t ht htpos
    simpa only [G,complexRoot_real htpos.le,←Complex.ofReal_zpow,Complex.real_smul] using ht
  · apply (hF.continuousAt.tendsto.comp (complexRoot_tendsto_zero hn)).congr'
    have hpos : ∀ᶠ z in radialInfinity, (0:ℝ) < ‖z‖ :=
      (tendsto_comap : Tendsto (norm : ℂ → ℝ) radialInfinity atTop).eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp hz
    have hpow : z^((q:ℝ):ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
    simp only [G,complexRoot_zpow,←hqa,inv_mul_cancel_left₀ hpow,Function.comp_def]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma rootCoord_scaled_power {n k : ℕ} (hn : 0 < n) {v a : ℝ}
    (hv : 0 < v) (ha : 0 < a) :
    rootCoord n (v^(-((n*k:ℕ):ℤ))*a) = v^k * (a^(-(n:ℝ)⁻¹)) := by
  rw [rootCoord,Real.mul_rpow (zpow_pos hv _).le ha.le]
  congr 1
  rw [←Real.rpow_intCast,←Real.rpow_mul hv.le,←Real.rpow_natCast]
  congr 1
  push_cast
  field_simp

 

theorem Puiseux.comp_unbounded {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf : Puiseux f) (hg : Puiseux (fun t => (g t:ℂ)))
    (hgt : Tendsto g atTop atTop) : Puiseux (fun t => f (g t)) := by
  obtain ⟨n,hn,a,F,hF,he⟩ := hf
  obtain ⟨m,k,hm,hk,G,hG,hGre,hGim,hge⟩ := hg.normalize_unbounded_real hgt
  let A : ℂ → ℂ := fun v => G (v^n)
  let Q : ℂ → ℂ := fun v => (A v)^(-(n:ℂ)⁻¹)
  have hA : AnalyticAt ℂ A 0 := by
    have hG' : AnalyticAt ℂ G ((0:ℂ)^n) := by simpa only [zero_pow hn.ne'] using hG
    exact hG'.comp (f := fun v : ℂ => v^n) (analyticAt_id.pow n)
  have hA0 : A 0 = G 0 := by simp [A,zero_pow hn.ne']
  have hQ : AnalyticAt ℂ Q 0 := hA.cpow analyticAt_const
    (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa only [hA0] using hGre)))
  have hQ0 : Q 0 ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by
    intro h; have := hGre; rw [←hA0,h] at this; norm_num at this))
  let H : ℂ → ℂ := fun v => (Q v)^a * F (v^k*Q v)
  have hH : AnalyticAt ℂ H 0 := (hQ.zpow hQ0).mul (by
    have h := (analyticAt_id.pow k).mul hQ
    have hf : AnalyticAt ℂ F ((0:ℂ)^k*Q 0) := by simpa only [zero_pow hk.ne',zero_mul] using hF
    exact hf.comp (f := fun v : ℂ => v^k*Q v) h)
  refine ⟨m*n,Nat.mul_pos hm hn,(k:ℤ)*a,H,hH,?_⟩
  filter_upwards [hge,hgt.eventually he,eventually_gt_atTop (0:ℝ),
    hgt.eventually (eventually_gt_atTop (0:ℝ))]
    with t hge he ht hgtpos
  let v : ℝ := rootCoord (m*n) t
  have hv : 0 < v := rootCoord_pos ht
  have hvn : v^n = rootCoord m t := rootCoord_pow hm hn ht
  have haim : (A (v:ℂ)).im = 0 := by
    have hi := congrArg Complex.im hge
    have hp : (rootCoord m t)^(-(k:ℤ)) ≠ 0 := (zpow_pos (rootCoord_pos ht) _).ne'
    simp only [Complex.ofReal_im,Complex.smul_im,smul_eq_mul] at hi
    have hzero := (mul_eq_zero.mp hi.symm).resolve_left hp
    simpa only [A,←Complex.ofReal_pow,hvn] using hzero
  have hare : 0 < (A (v:ℂ)).re := by
    have hr := congrArg Complex.re hge
    have hp : 0 < (rootCoord m t)^(-(k:ℤ)) := zpow_pos (rootCoord_pos ht) _
    simp only [Complex.ofReal_re,Complex.smul_re,smul_eq_mul] at hr
    have hapos : 0 < (G (rootCoord m t)).re := by nlinarith
    simpa only [A,←Complex.ofReal_pow,hvn] using hapos
  have hrealA : A (v:ℂ) = ((A (v:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using haim)
  have hgval : g t = v^(-((n*k:ℕ):ℤ)) * (A (v:ℂ)).re := by
    have hr := congrArg Complex.re hge
    simp only [Complex.ofReal_re,Complex.smul_re,smul_eq_mul] at hr
    rw [←hvn] at hr
    calc
      g t = (v^n)^(-(k:ℤ)) * (A (v:ℂ)).re := by
        simpa only [A,←Complex.ofReal_pow] using hr
      _ = v^(-((n*k:ℕ):ℤ)) * (A (v:ℂ)).re := by
        rw [←zpow_natCast,←zpow_mul]
        congr 2
        push_cast
        ring
  have hroot : (rootCoord n (g t):ℂ) = (v:ℂ)^k * Q (v:ℂ) := by
    rw [hgval,rootCoord_scaled_power hn hv hare]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow]
    congr 1
    change _ = (A (v:ℂ))^(-(n:ℂ)⁻¹)
    conv_rhs => rw [hrealA]
    rw [Complex.ofReal_cpow hare.le]
    push_cast
    rfl
  rw [he,Complex.real_smul,Complex.ofReal_zpow,hroot]
  simp only [H,mul_zpow,←zpow_natCast,←zpow_mul,Complex.real_smul,Complex.ofReal_zpow,mul_assoc]
  rfl

 

theorem Puiseux.change_coordinate {H : ℝ → ℝ}
    (hH : Puiseux (fun t => (H t:ℂ))) (hHt : Tendsto H atTop atTop) :
    ∃ I : ℝ → ℝ, Puiseux (fun t => (I t:ℂ)) ∧ Tendsto I atTop atTop ∧
      (∀ᶠ t in atTop, H (I t)=t) ∧ (∀ᶠ t in atTop, I (H t)=t) ∧
      ∀ f : ℝ → ℂ, Puiseux f → Puiseux (fun t => f (I t)) := by
  obtain ⟨I,hI,hIt,hl,hr⟩ := hH.inverse_change hHt
  exact ⟨I,hI,hIt,hl,hr,fun f hf => hf.comp_unbounded hI hIt⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma radial_real_tendsto : Tendsto (fun t : ℝ => (t:ℂ)) atTop radialInfinity := by
  rw [radialInfinity,tendsto_comap_iff]
  simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs] using
    (tendsto_abs_atTop_atTop : Tendsto (abs : ℝ → ℝ) atTop atTop)

lemma radial_norm_equivalent {q : ℝ} {C : ℂ} {F : ℂ → ℂ}
    (hC : C ≠ 0)
    (hF : Tendsto (fun z => (z^(q:ℂ))⁻¹*F z) radialInfinity (𝓝 C)) :
    ∀ᶠ z in radialInfinity,
      ‖C‖/2 * ‖z‖^q ≤ ‖F z‖ ∧ ‖F z‖ ≤ 2*‖C‖*‖z‖^q := by
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hn := hF.norm
  have hbounds := ((eventually_gt_nhds (show ‖C‖/2 < ‖C‖ by linarith)).and
    (eventually_lt_nhds (show ‖C‖ < 2*‖C‖ by linarith)))
  filter_upwards [hn.eventually hbounds,
    (tendsto_comap : Tendsto (norm : ℂ → ℝ) radialInfinity atTop).eventually (eventually_gt_atTop 0)]
    with z hz hzpos
  have hp : 0 < ‖z‖^q := Real.rpow_pos_of_pos hzpos _
  simp only [norm_mul,norm_inv,Complex.norm_cpow_real] at hz
  have hz' : ‖C‖/2 < ‖F z‖ / ‖z‖^q ∧ ‖F z‖ / ‖z‖^q < 2*‖C‖ := by
    simpa only [div_eq_mul_inv,mul_comm] using hz
  exact ⟨((lt_div_iff₀ hp).mp hz'.1).le,((div_lt_iff₀ hp).mp hz'.2).le⟩

 

theorem Puiseux.sector_modulus_comparable {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    ∃ (G : ℂ → ℂ) (R : ℝ),
      (∀ z : ℂ, R < ‖z‖ → 0 < z.re → AnalyticAt ℂ G z) ∧
      f =ᶠ[atTop] (fun t => G (t:ℂ)) ∧
      ∀ z : ℂ, R < ‖z‖ → ‖f ‖z‖‖/4 ≤ ‖G z‖ ∧ ‖G z‖ ≤ 4*‖f ‖z‖‖ := by
  obtain ⟨q,C,G,R,hC,hGa,he,hlim⟩ := hf.sector_leading hne
  have hb := radial_norm_equivalent hC hlim
  obtain ⟨S,hS⟩ := radial_eventually hb
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  refine ⟨G,max R (max S (max T 0)),?_,he,?_⟩
  · intro z hz hzre
    exact hGa z ((le_max_left _ _).trans_lt hz) hzre
  · intro z hz
    have hSlt : S < ‖z‖ := (le_max_of_le_right (le_max_left _ _)).trans_lt hz
    have hTle : T ≤ ‖z‖ := (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hz.le
    have hnorm : 0 ≤ ‖z‖ := norm_nonneg _
    have hreal := hS (‖z‖:ℂ) (by simpa only [Complex.norm_of_nonneg hnorm] using hSlt)
    have heq : f ‖z‖ = G (‖z‖:ℂ) := hT _ hTle
    rw [←heq] at hreal
    simp only [Complex.norm_of_nonneg hnorm] at hreal
    have hc := hS z hSlt
    constructor <;> linarith

end DegeneratingTrees.Clock
end

end OAI
