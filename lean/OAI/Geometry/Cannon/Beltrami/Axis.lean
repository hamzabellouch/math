import Mathlib
import OAI.Geometry.Cannon.Conformal.Sphere
import OAI.Geometry.Cannon.Beltrami.MultiplyLp

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

open FourierTransform
open scoped ENNReal

lemma multiplier_strong_convergence_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → ℂ → ℂ) (ν : ℂ → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) volume) (hn : AEStronglyMeasurable ν volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ z ∂volume, ‖μ n z‖ ≤ k)
    (hc : ∀ᵐ z ∂volume, ‖ν z‖ ≤ k)
    (ht : ∀ᵐ z ∂volume, Tendsto (fun n => μ n z) l (𝓝 (ν z))) (f : PlaneL2) :
    Tendsto (fun n => multiplier (μ n) (hm n) hk (hb n) f) l
      (𝓝 (multiplier ν hn hk hc f)) := by
  let Q (n : ι) := multiplier (μ n) (hm n) hk (hb n) f-multiplier ν hn hk hc f
  let F (n : ι) (z : ℂ) := (μ n z-ν z)*f z
  have he (n : ι) : Q n =ᵐ[volume] F n := by
    filter_upwards [Lp.coeFn_sub (multiplier (μ n) (hm n) hk (hb n) f)
      (multiplier ν hn hk hc f),multiplier_ae (μ n) (hm n) hk (hb n) f,
      multiplier_ae ν hn hk hc f] with z h1 h2 h3
    dsimp only [Q,F]
    simp only [Pi.sub_apply] at h1
    rw [h1,h2,h3,sub_mul]
  have hF (n : ι) : MemLp (F n) 2 volume := MemLp.ae_eq (he n) (Lp.memLp (Q n))
  have hdom (n : ι) : ∀ᵐ z ∂volume, ‖F n z‖ ≤ ‖((2*k:ℝ):ℂ)*f z‖ := by
    filter_upwards [hb n,hc] with z h2 h3
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hk)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith)
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun n => F n z) l (𝓝 0) := by
    filter_upwards [ht] with z h2
    simpa only [F,sub_self,zero_mul] using (h2.sub_const (ν z)).mul_const (f z)
  have H := dominated_toLp_zero_filter hF
    ((Lp.memLp f).const_mul ((2*k:ℝ):ℂ)) hdom hlim
  have hE (n : ι) : (hF n).toLp (F n)=Q n := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hF n)).trans (he n).symm
  simp only [hE] at H
  exact (tendsto_sub_nhds_zero_iff).mp H

lemma multiplier_variable_convergence {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → ℂ → ℂ) (ν : ℂ → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) volume) (hn : AEStronglyMeasurable ν volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ z ∂volume, ‖μ n z‖ ≤ k)
    (hc : ∀ᵐ z ∂volume, ‖ν z‖ ≤ k)
    (ht : ∀ᵐ z ∂volume, Tendsto (fun n => μ n z) l (𝓝 (ν z)))
    (f : ι → PlaneL2) (g : PlaneL2) (hf : Tendsto f l (𝓝 g)) :
    Tendsto (fun n => multiplier (μ n) (hm n) hk (hb n) (f n)) l
      (𝓝 (multiplier ν hn hk hc g)) := by
  have hzero : Tendsto (fun n => multiplier (μ n) (hm n) hk (hb n) (f n-g)) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_multiplyLp_le (μ n) (hm n) hk (hb n) (f n-g))
    simpa using (hf.sub_const g).norm.const_mul k
  have hconst := multiplier_strong_convergence_filter μ ν hm hn hk hb hc ht g
  simpa only [map_sub,sub_add_cancel,zero_add] using hzero.add hconst

lemma multiplier_coefficient_slope (a : ℝ → ℂ → ℂ)
    (hm : ∀ t, AEStronglyMeasurable (a t) volume)
    {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ z ∂volume, ‖a t z‖ ≤ k)
    (hq : ∀ t, ∀ᵐ z ∂volume, ‖t⁻¹ • (a t z-a 0 z)‖ ≤ C)
    (t : ℝ) (f : PlaneL2) :
    multiplier (fun z => t⁻¹ • (a t z-a 0 z))
      (((hm t).sub (hm 0)).const_smul t⁻¹) hC (hq t) f=
      t⁻¹ • (multiplier (a t) (hm t) hk (hb t) f-
        multiplier (a 0) (hm 0) hk (hb 0) f) := by
  apply Lp.ext
  filter_upwards [multiplier_ae (fun z => t⁻¹ • (a t z-a 0 z)) _ hC (hq t) f,
    Lp.coeFn_smul t⁻¹ (multiplier (a t) (hm t) hk (hb t) f-
      multiplier (a 0) (hm 0) hk (hb 0) f),
    Lp.coeFn_sub (multiplier (a t) (hm t) hk (hb t) f)
      (multiplier (a 0) (hm 0) hk (hb 0) f),
    multiplier_ae (a t) (hm t) hk (hb t) f,
    multiplier_ae (a 0) (hm 0) hk (hb 0) f] with z h1 h2 h3 h4 h5
  simp only [Pi.smul_apply,Pi.sub_apply] at h2 h3
  rw [h1,h2,h3,h4,h5,smul_mul_assoc,sub_mul]

theorem hasDerivAt_multiplier_product (a : ℝ → ℂ → ℂ) (d : ℂ → ℂ)
    (hm : ∀ t, AEStronglyMeasurable (a t) volume) (hdm : AEStronglyMeasurable d volume)
    {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ z ∂volume, ‖a t z‖ ≤ k)
    (hq : ∀ t, ∀ᵐ z ∂volume, ‖t⁻¹ • (a t z-a 0 z)‖ ≤ C)
    (hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ C)
    (hd : ∀ᵐ z ∂volume, HasDerivAt (fun t => a t z) (d z) 0)
    (f : ℝ → PlaneL2) (f' : PlaneL2) (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => multiplier (a t) (hm t) hk (hb t) (f t))
      (multiplier (a 0) (hm 0) hk (hb 0) f'+multiplier d hdm hC hdb (f 0)) 0 := by
  let am : ∀ t, AEStronglyMeasurable (fun z => t⁻¹ • (a t z-a 0 z)) volume :=
    fun t => ((hm t).sub (hm 0)).const_smul t⁻¹
  have ht : ∀ᵐ z ∂volume, Tendsto (fun t : ℝ => a t z) (𝓝[≠] 0) (𝓝 (a 0 z)) :=
    hd.mono fun z hz => hz.continuousAt.tendsto.mono_left inf_le_left
  have hqt : ∀ᵐ z ∂volume,
      Tendsto (fun t : ℝ => t⁻¹ • (a t z-a 0 z)) (𝓝[≠] 0) (𝓝 (d z)) := by
    filter_upwards [hd] with z hz
    simpa only [zero_add] using hz.tendsto_slope_zero
  have hfirst := multiplier_variable_convergence a (a 0) hm (hm 0) hk hb (hb 0) ht
    (fun t : ℝ => t⁻¹ • (f t-f 0)) f' (by simpa using hf.tendsto_slope_zero)
  have hsecond := multiplier_strong_convergence_filter
    (fun t z => t⁻¹ • (a t z-a 0 z)) d am hdm hC hq hdb hqt (f 0)
  have he (t : ℝ) :
      multiplier (a t) (hm t) hk (hb t) (t⁻¹ • (f t-f 0))+
      multiplier (fun z => t⁻¹ • (a t z-a 0 z)) (am t) hC (hq t) (f 0)=
      t⁻¹ • (multiplier (a t) (hm t) hk (hb t) (f t)-
        multiplier (a 0) (hm 0) hk (hb 0) (f 0)) := by
    rw [multiplier_coefficient_slope a hm hk hC hb hq]
    have hsmul : multiplier (a t) (hm t) hk (hb t) (t⁻¹ • (f t-f 0))=
        t⁻¹ • multiplier (a t) (hm t) hk (hb t) (f t-f 0) :=
      (multiplier (a t) (hm t) hk (hb t)).toLinearMap.map_smul_of_tower _ _
    rw [hsmul]
    simp only [map_sub,smul_sub]
    abel
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add,he] using hfirst.add hsecond

lemma translate_multiplier (a : ℂ) (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (f : PlaneL2) :
    translateL2 a (multiplier μ hm hk hb f)=
      multiplier (fun z => μ (z+a))
        (hm.comp_quasiMeasurePreserving (measurePreserving_add_right volume a).quasiMeasurePreserving)
        hk ((measurePreserving_add_right volume a).quasiMeasurePreserving.ae hb)
        (translateL2 a f) := by
  apply Lp.ext
  filter_upwards [translateL2_ae a (multiplier μ hm hk hb f),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
      (multiplier_ae μ hm hk hb f),
    multiplier_ae (fun z => μ (z+a)) _ hk _ (translateL2 a f),translateL2_ae a f]
      with z h1 h2 h3 h4
  simp only [Function.comp_def] at h2
  rw [h1,h2,h3,h4]

lemma lipschitz_coefficient_quotient (μ : ℂ → ℂ) {L : NNReal}
    (hL : LipschitzWith L μ) (v z : ℂ) (t : ℝ) :
    ‖t⁻¹ • (μ (z+t • v)-μ z)‖ ≤ L*‖v‖ := by
  by_cases ht : t=0
  · simp only [ht,inv_zero,zero_smul,norm_zero]
    positivity
  have hh := hL.dist_le_mul (z+t • v) z
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hh
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    |t|⁻¹*‖μ (z+t • v)-μ z‖ ≤ |t|⁻¹*(L*(|t| *‖v‖)) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
    _ = L*‖v‖ := by field_simp

theorem hasDerivAt_translate_multiplier (μ d : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) (hdm : AEStronglyMeasurable d volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    {L : NNReal} (hL : LipschitzWith L μ) (v : ℂ)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • v)) (d z) 0)
    (hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖v‖)
    (f f' : PlaneL2) (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) f' 0) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) (multiplier μ hm hk hb f))
      (multiplier μ hm hk hb f'+
        multiplier d hdm (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdb f) 0 := by
  let am (t : ℝ) := hm.comp_quasiMeasurePreserving
    (measurePreserving_add_right volume (t • v)).quasiMeasurePreserving
  let ab (t : ℝ) := (measurePreserving_add_right volume (t • v)).quasiMeasurePreserving.ae hb
  have hq (t : ℝ) : ∀ᵐ z ∂volume,
      ‖t⁻¹ • (μ (z+t • v)-μ (z+(0:ℝ) • v))‖ ≤ L*‖v‖ := by
    exact .of_forall fun z => by simpa using lipschitz_coefficient_quotient μ hL v z t
  have ht := hasDerivAt_multiplier_product (fun t z => μ (z+t • v)) d am hdm hk
    (mul_nonneg L.coe_nonneg (norm_nonneg v)) ab hq hdb (.of_forall hd)
    (fun t : ℝ => translateL2 (t • v) f) f' hf
  have he : (fun t : ℝ => multiplier (fun z => μ (z+t • v)) (am t) hk (ab t)
      (translateL2 (t • v) f))=
      (fun t : ℝ => translateL2 (t • v) (multiplier μ hm hk hb f)) := by
    funext t
    exact (translate_multiplier (t • v) μ hm hk hb f).symm
  rw [he] at ht
  simpa only [zero_smul,add_zero,translateL2_zero] using ht

theorem differentiated_beltrami (μ d : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) (hdm : AEStronglyMeasurable d volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    {L : NNReal} (hL : LipschitzWith L μ) (v : ℂ)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • v)) (d z) 0)
    (hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖v‖)
    (h b h' b' : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    (hh : HasDerivAt (fun t : ℝ => translateL2 (t • v) h) h' 0)
    (hb' : HasDerivAt (fun t : ℝ => translateL2 (t • v) b) b' 0) :
    h'-multiplier μ hm hk hb (beurling h')=
      b'+multiplier d hdm (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdb (beurling h) := by
  have hs : HasDerivAt (fun t : ℝ => translateL2 (t • v) (beurling h)) (beurling h') 0 := by
    have ht := (beurling.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hh
    change HasDerivAt (fun t : ℝ => beurling (translateL2 (t • v) h)) (beurling h') 0 at ht
    simpa only [translate_beurling] using ht
  have hp := hasDerivAt_translate_multiplier μ d hm hdm hk hb hL v hd hdb (beurling h) (beurling h') hs
  have ht := hh.sub hp
  have hf : (fun t : ℝ => translateL2 (t • v) h-
      translateL2 (t • v) (multiplier μ hm hk hb (beurling h)))=
      (fun t : ℝ => translateL2 (t • v) b) := by
    funext t
    rw [← map_sub,he]
  change HasDerivAt (fun t : ℝ => translateL2 (t • v) h-
      translateL2 (t • v) (multiplier μ hm hk hb (beurling h))) _ 0 at ht
  rw [hf] at ht
  have hu := ht.unique hb'
  rw [← hu]
  abel

lemma translateL2_comp (a b : ℂ) (f : PlaneL2) :
    translateL2 a (translateL2 b f)=translateL2 (a+b) f := by
  apply Lp.ext
  filter_upwards [translateL2_ae a (translateL2 b f),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (translateL2_ae b f),
    translateL2_ae (a+b) f] with z h1 h2 h3
  simp only [Function.comp_def] at h2
  rw [h1,h2,h3,add_assoc]

lemma hasDerivAt_translateL2_at (f f' : PlaneL2) (v : ℂ)
    (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) f' 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translateL2 (s • v) f) (translateL2 (t • v) f') t := by
  have ht : Tendsto (fun s : ℝ => s⁻¹ • (translateL2 (s • v) f-f))
      (𝓝[≠] 0) (𝓝 f') := by
    simpa only [zero_add,zero_smul,translateL2_zero] using hf.tendsto_slope_zero
  have hmap := (translateL2 (t • v)).continuous.continuousAt.tendsto.comp ht
  have he (s : ℝ) : translateL2 (t • v) (s⁻¹ • (translateL2 (s • v) f-f))=
      s⁻¹ • (translateL2 ((t+s) • v) f-translateL2 (t • v) f) := by
    have hsmul : translateL2 (t • v) (s⁻¹ • (translateL2 (s • v) f-f))=
        s⁻¹ • translateL2 (t • v) (translateL2 (s • v) f-f) :=
      (translateL2 (t • v)).toLinearMap.map_smul_of_tower _ _
    rw [hsmul,map_sub,translateL2_comp,← add_smul]
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [Function.comp_def,he] using hmap

lemma translation_line_bound (f f' : PlaneL2) (v : ℂ)
    (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) f' 0) (t : ℝ) :
    ‖translateL2 (t • v) f-f‖ ≤ ‖f'‖*|t| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ (Set.univ : Set ℝ)) => (hasDerivAt_translateL2_at f f' v hf s).hasDerivWithinAt)
    (fun s (_ : s ∈ (Set.univ : Set ℝ)) => (translateL2 (s • v)).norm_map f' |>.le)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ (0:ℝ)) (Set.mem_univ t)
  simpa only [zero_smul,translateL2_zero,sub_zero,Real.norm_eq_abs] using hh

theorem translation_bound_of_coordinate_derivatives (f fx fy : PlaneL2)
    (hx : HasDerivAt (fun t : ℝ => translateL2 (t • (1:ℂ)) f) fx 0)
    (hy : HasDerivAt (fun t : ℝ => translateL2 (t • Complex.I) f) fy 0) (a : ℂ) :
    ‖translateL2 a f-f‖ ≤ (‖fx‖+‖fy‖)*‖a‖ := by
  have ha : a=(a.re : ℝ) • (1:ℂ)+(a.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have he : ‖translateL2 a f-translateL2 (a.re • (1:ℂ)) f‖=
      ‖translateL2 (a.im • Complex.I) f-f‖ := by
    rw [show translateL2 a f = translateL2 (a.re • 1) (translateL2 (a.im • Complex.I) f) by
      rw [translateL2_comp, ← ha], ← map_sub]
    exact (translateL2 (a.re • (1:ℂ))).norm_map _
  calc
    ‖translateL2 a f-f‖ ≤ ‖translateL2 a f-translateL2 (a.re • (1:ℂ)) f‖+
        ‖translateL2 (a.re • (1:ℂ)) f-f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖translateL2 (a.im • Complex.I) f-f‖+‖translateL2 (a.re • (1:ℂ)) f-f‖ := by rw [he]
    _ ≤ ‖fy‖*|a.im|+‖fx‖*|a.re| :=
      add_le_add (translation_line_bound f fy Complex.I hy a.im)
        (translation_line_bound f fx 1 hx a.re)
    _ ≤ (‖fx‖+‖fy‖)*‖a‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm a) (norm_nonneg fy),
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm a) (norm_nonneg fx)]

theorem beltrami_solution_difference
    (μ ν : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    (hn : AEStronglyMeasurable ν volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (hc : ∀ᵐ z ∂volume, ‖ν z‖ ≤ k)
    (h h' b b' : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    (he' : h'-multiplier ν hn hk hc (beurling h')=b') :
    ‖h'-h‖ ≤ (‖b'-b‖+
      ‖multiplier ν hn hk hc (beurling h)-multiplier μ hm hk hb (beurling h)‖)/(1-k) := by
  let M := multiplier μ hm hk hb
  let N := multiplier ν hn hk hc
  have hid : h'-h = N (beurling (h'-h))+(b'-b)+(N (beurling h)-M (beurling h)) := by
    rw [map_sub,map_sub]
    change h-M (beurling h)=b at he
    change h'-N (beurling h')=b' at he'
    rw [← he,← he']
    abel
  have hnorm : ‖h'-h‖ ≤ k*‖h'-h‖+‖b'-b‖+‖N (beurling h)-M (beurling h)‖ := by
    calc
      ‖h'-h‖ = ‖N (beurling (h'-h))+(b'-b)+(N (beurling h)-M (beurling h))‖ := congrArg norm hid
      _ ≤ ‖N (beurling (h'-h))‖+‖b'-b‖+‖N (beurling h)-M (beurling h)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ k*‖h'-h‖+‖b'-b‖+‖N (beurling h)-M (beurling h)‖ := by
        gcongr
        exact (norm_multiplyLp_le ν hn hk hc (beurling (h'-h))).trans_eq
          (by rw [norm_beurling])
  apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
  nlinarith

theorem beltrami_translation_estimate (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (h b : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    (a : ℂ) {c : ℝ} (hc : ∀ᵐ z ∂volume, ‖μ (z+a)-μ z‖ ≤ c) :
    ‖translateL2 a h-h‖ ≤ (‖translateL2 a b-b‖+c*‖h‖)/(1-k) := by
  let hm' := hm.comp_quasiMeasurePreserving
    (measurePreserving_add_right volume a).quasiMeasurePreserving
  let hb' := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hb
  have he' : translateL2 a h-
      multiplier (fun z => μ (z+a)) hm' hk hb' (beurling (translateL2 a h))=
      translateL2 a b := by
    have ht := congrArg (translateL2 a) he
    rw [map_sub,translate_multiplier,translate_beurling] at ht
    exact ht
  have hd := beltrami_solution_difference μ (fun z => μ (z+a)) hm hm' hk hk1 hb hb'
    h (translateL2 a h) b (translateL2 a b) he he'
  refine hd.trans (div_le_div_of_nonneg_right (add_le_add le_rfl ?_) (sub_pos.mpr hk1).le)
  rw [← norm_beurling h]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub
    (multiplier (fun z => μ (z+a)) hm' hk hb' (beurling h))
    (multiplier μ hm hk hb (beurling h)),
    multiplier_ae (fun z => μ (z+a)) hm' hk hb' (beurling h),
    multiplier_ae μ hm hk hb (beurling h),hc] with z h1 h2 h3 h4
  simp only [Pi.sub_apply] at h1
  rw [h1,h2,h3,← sub_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)

theorem beltrami_difference_quotient_bound (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (h b : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b)
    {L : NNReal} (hL : LipschitzWith L μ) {B : ℝ}
    (hB : ∀ a : ℂ, ‖translateL2 a b-b‖ ≤ B*‖a‖) (a : ℂ) :
    ‖translateL2 a h-h‖ ≤ ((B+L*‖h‖)/(1-k))*‖a‖ := by
  have hc : ∀ᵐ z ∂volume, ‖μ (z+a)-μ z‖ ≤ L*‖a‖ := by
    apply Filter.Eventually.of_forall
    intro z
    simpa only [dist_eq_norm,add_sub_cancel_left] using hL.dist_le_mul (z+a) z
  have hh := beltrami_translation_estimate μ hm hk hk1 hb h b he a hc
  calc
    ‖translateL2 a h-h‖ ≤ (‖translateL2 a b-b‖+(L*‖a‖)*‖h‖)/(1-k) := hh
    _ ≤ (B*‖a‖+(L*‖a‖)*‖h‖)/(1-k) :=
      div_le_div_of_nonneg_right (add_le_add (hB a) le_rfl) (sub_pos.mpr hk1).le
    _ = _ := by ring

def axis (b : Bool) : ℂ := if b then Complex.I else 1

def Sobolev : ℕ → PlaneL2 → Prop
  | 0, _ => True
  | n+1, f => Sobolev n f ∧ ∀ b : Bool, ∃ df : PlaneL2,
      HasDerivAt (fun t : ℝ => translateL2 (t • axis b) f) df 0 ∧ Sobolev n df

def BoundedSmooth : ℕ → (ℂ → ℂ) → Prop
  | 0, μ => AEStronglyMeasurable μ volume ∧ ∃ K : NNReal, ∀ z, ‖μ z‖ ≤ K
  | n+1, μ => BoundedSmooth n μ ∧ ∃ L : NNReal, LipschitzWith L μ ∧
      ∀ b : Bool, ∃ d : ℂ → ℂ, BoundedSmooth n d ∧
        ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • axis b)) (d z) 0

lemma BoundedSmooth.zero {n : ℕ} {μ : ℂ → ℂ} (h : BoundedSmooth n μ) :
    BoundedSmooth 0 μ := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.1

lemma Sobolev.add {n : ℕ} {f g : PlaneL2} (hf : Sobolev n f) (hg : Sobolev n g) :
    Sobolev n (f+g) := by
  induction n generalizing f g with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1 hg.1, fun b => ?_⟩
    obtain ⟨df, hdf, hrf⟩ := hf.2 b
    obtain ⟨dg, hdg, hrg⟩ := hg.2 b
    refine ⟨df+dg, ?_, ih hrf hrg⟩
    convert hdf.add hdg using 1; try rfl
    funext t
    exact map_add (translateL2 (t • axis b)) f g

lemma hasDerivAt_translate_beurling {f df : PlaneL2} {v : ℂ}
    (hf : HasDerivAt (fun t : ℝ => translateL2 (t • v) f) df 0) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) (beurling f)) (beurling df) 0 := by
  have ht := (beurling.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf
  change HasDerivAt (fun t : ℝ => beurling (translateL2 (t • v) f)) (beurling df) 0 at ht
  simpa only [translate_beurling] using ht

lemma Sobolev.beurling {n : ℕ} {f : PlaneL2} (hf : Sobolev n f) :
    Sobolev n (beurling f) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1, fun b => ?_⟩
    obtain ⟨df, hdf, hrf⟩ := hf.2 b
    exact ⟨CannonBeltrami.beurling df, hasDerivAt_translate_beurling hdf, ih hrf⟩

lemma coefficient_derivative_bound (μ d : ℂ → ℂ) {L : NNReal}
    (hL : LipschitzWith L μ) (v : ℂ)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • v)) (d z) 0) (z : ℂ) :
    ‖d z‖ ≤ L*‖v‖ := by
  have ht : Tendsto (fun t : ℝ => ‖t⁻¹ • (μ (z+t • v)-μ z)‖)
      (𝓝[≠] 0) (𝓝 ‖d z‖) := by
    simpa only [zero_add,zero_smul,add_zero] using (hd z).tendsto_slope_zero.norm
  exact le_of_tendsto ht (.of_forall fun t => lipschitz_coefficient_quotient μ hL v z t)

lemma Sobolev.multiplier {n : ℕ} {f : PlaneL2} (hf : Sobolev n f)
    (μ : ℂ → ℂ) (hμ : BoundedSmooth n μ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) :
    Sobolev n (multiplier μ hm hk hb f) := by
  induction n generalizing f μ k with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1 μ hμ.1 hm hk hb, fun b => ?_⟩
    obtain ⟨L,hL,hds⟩ := hμ.2
    obtain ⟨d,hd,he⟩ := hds b
    obtain ⟨df,hdf,hrf⟩ := hf.2 b
    have hdb : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖axis b‖ :=
      Filter.Eventually.of_forall (coefficient_derivative_bound μ d hL (axis b) he)
    let M := CannonBeltrami.multiplier d hd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg (axis b))) hdb
    refine ⟨CannonBeltrami.multiplier μ hm hk hb df + M f, ?_, ?_⟩
    · exact hasDerivAt_translate_multiplier μ d hm hd.zero.1 hk hb hL (axis b) he hdb f df hdf
    · exact (ih hrf μ hμ.1 hm hk hb).add
        (ih hf.1 d hd hd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg (axis b))) hdb)

lemma Sobolev.translation_bound {n : ℕ} {f : PlaneL2} (hf : Sobolev (n+1) f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℂ, ‖translateL2 a f-f‖ ≤ B*‖a‖ := by
  obtain ⟨fx,hx,_⟩ := hf.2 false
  obtain ⟨fy,hy,_⟩ := hf.2 true
  refine ⟨‖fx‖+‖fy‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  exact translation_bound_of_coordinate_derivatives f fx fy hx hy

theorem beltrami_sobolev {n : ℕ} (μ : ℂ → ℂ) (hμ : BoundedSmooth n μ)
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) (h b : PlaneL2)
    (he : h-multiplier μ hm hk hb (beurling h)=b) (hrb : Sobolev n b) :
    Sobolev n h := by
  induction n generalizing h b with
  | zero => trivial
  | succ n ih =>
    have hrh : Sobolev n h := ih hμ.1 h b he hrb.1
    obtain ⟨L,hL,hds⟩ := hμ.2
    obtain ⟨B,hB,hBt⟩ := hrb.translation_bound
    let C : ℝ := (B+L*‖h‖)/(1-k)
    have hC : 0 ≤ C := div_nonneg (add_nonneg hB (mul_nonneg L.coe_nonneg (norm_nonneg _)))
      (sub_pos.mpr hk1).le
    have hCt (a : ℂ) : ‖translateL2 a h-h‖ ≤ C*‖a‖ :=
      beltrami_difference_quotient_bound μ hm hk hk1 hb h b he hL hBt a
    refine ⟨hrh, fun j => ?_⟩
    let v := axis j
    let hd := (memLp_directionSymbol_of_translation_bound h hC hCt v).1
    let dh := planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier h z))
    have hdh : HasDerivAt (fun t : ℝ => translateL2 (t • v) h) dh 0 :=
      hasDerivAt_translateL2 h v hd
    obtain ⟨d,hrd,hder⟩ := hds j
    obtain ⟨db,hdb,hrdb⟩ := hrb.2 j
    have hdbound : ∀ᵐ z ∂volume, ‖d z‖ ≤ L*‖v‖ :=
      Filter.Eventually.of_forall (coefficient_derivative_bound μ d hL v hder)
    let M := multiplier d hrd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdbound
    have hde : dh-multiplier μ hm hk hb (beurling dh)=db+M (beurling h) :=
      differentiated_beltrami μ d hm hrd.zero.1 hk hb hL v hder hdbound h b dh db he hdh hdb
    have hrs : Sobolev n (db+M (beurling h)) := hrdb.add
      (hrh.beurling.multiplier d hrd hrd.zero.1 (mul_nonneg L.coe_nonneg (norm_nonneg v)) hdbound)
    exact ⟨dh, hdh, ih hμ.1 dh (db+M (beurling h)) hde hrs⟩

open scoped SchwartzMap LineDeriv FourierTransform

lemma schwartz_lipschitz (f : SchwartzMap ℂ ℂ) : ∃ L : NNReal, LipschitzWith L f := by
  let d := SchwartzMap.fderivCLM ℝ ℂ ℂ f
  let K : NNReal := ⟨SchwartzMap.seminorm ℝ 0 0 d, apply_nonneg _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le f.differentiable ?_⟩
  intro z
  change ‖fderiv ℝ f z‖₊ ≤ K
  exact_mod_cast d.norm_le_seminorm ℝ z

lemma schwartz_line_derivative (f : SchwartzMap ℂ ℂ) (v z : ℂ) :
    HasDerivAt (fun t : ℝ => f (z+t • v)) (∂_{v} f z) 0 := by
  have ht := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hf := (f.hasFDerivAt (z+(0:ℝ) • v)).comp_hasDerivAt 0 ht
  convert hf using 1 <;> simp only [zero_smul,add_zero,one_smul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,Function.comp_def,id_eq]

lemma schwartz_boundedSmooth (n : ℕ) (f : SchwartzMap ℂ ℂ) : BoundedSmooth n f := by
  induction n generalizing f with
  | zero =>
    exact ⟨f.continuous.aestronglyMeasurable,
      ⟨⟨SchwartzMap.seminorm ℝ 0 0 f, apply_nonneg _ _⟩, f.norm_le_seminorm ℝ⟩⟩
  | succ n ih =>
    obtain ⟨L,hL⟩ := schwartz_lipschitz f
    exact ⟨ih f, L,hL,fun b => ⟨(∂_{axis b} f : SchwartzMap ℂ ℂ), ih _, schwartz_line_derivative f (axis b)⟩⟩

lemma fourier_schwartz_derivative_ae (f : SchwartzMap ℂ ℂ) (v : ℂ) :
    planeFourier ((∂_{v} f).toLp 2) =ᵐ[volume]
      fun z => directionSymbol v z*planeFourier (f.toLp 2) z := by
  have hd : planeFourier ((∂_{v} f).toLp 2)=(𝓕 (∂_{v} f)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq _
  have hf : planeFourier (f.toLp 2)=(𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq _
  rw [hd,hf]
  filter_upwards [(𝓕 (∂_{v} f)).coeFn_toLp 2 volume,(𝓕 f).coeFn_toLp 2 volume] with z h1 h2
  rw [h1,h2,SchwartzMap.fourier_lineDerivOp_eq]
  have htemp : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [smul_apply,SchwartzMap.smulLeftCLM_apply_apply htemp]
  simp [directionSymbol,real_inner_comm,smul_eq_mul,mul_assoc]

lemma hasDerivAt_translateL2_of_fourier (f df : PlaneL2) (v : ℂ)
    (hae : planeFourier df =ᵐ[volume] fun z => directionSymbol v z*planeFourier f z) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) f) df 0 := by
  have hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume :=
    MemLp.ae_eq hae (Lp.memLp (planeFourier df))
  have he : hd.toLp (fun z => directionSymbol v z*planeFourier f z)=planeFourier df := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hd).trans hae.symm
  have hh := hasDerivAt_translateL2 f v hd
  have hi : planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z))=df := by
    rw [he,planeFourier.symm_apply_apply]
  rw [hi] at hh
  exact hh

lemma schwartz_translation_derivative (f : SchwartzMap ℂ ℂ) (v : ℂ) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) (f.toLp 2)) ((∂_{v} f).toLp 2) 0 :=
  hasDerivAt_translateL2_of_fourier (f.toLp 2) ((∂_{v} f).toLp 2) v
    (fourier_schwartz_derivative_ae f v)

lemma schwartz_sobolev (n : ℕ) (f : SchwartzMap ℂ ℂ) : Sobolev n (f.toLp 2) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    exact ⟨ih f, fun b => ⟨(∂_{axis b} f).toLp 2,
      schwartz_translation_derivative f (axis b), ih _⟩⟩

theorem solve_schwartz_beltrami (μ b : SchwartzMap ℂ ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ h : PlaneL2,
      h-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h)=b.toLp 2 ∧
      ‖h‖ ≤ ‖b.toLp 2‖/(1-k) ∧ ∀ n : ℕ, Sobolev n h := by
  obtain ⟨h,he,hn,hu⟩ := solve_beltrami_l2 μ μ.continuous.aestronglyMeasurable hk hk1
    (.of_forall hb) (b.toLp 2)
  exact ⟨h,he,hn,fun n => beltrami_sobolev μ (schwartz_boundedSmooth n μ)
    μ.continuous.aestronglyMeasurable hk hk1 (.of_forall hb) h (b.toLp 2) he (schwartz_sobolev n b)⟩

lemma Sobolev.smul {n : ℕ} {f : PlaneL2} (hf : Sobolev n f) (c : ℂ) :
    Sobolev n (c • f) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hf.1, fun b => ?_⟩
    obtain ⟨df, hdf, hrf⟩ := hf.2 b
    refine ⟨c • df, ?_, ih hrf⟩
    convert hdf.const_smul c using 1; try rfl
    funext t
    exact map_smul (translateL2 (t • axis b)) c f

lemma Sobolev.sub {n : ℕ} {f g : PlaneL2} (hf : Sobolev n f) (hg : Sobolev n g) :
    Sobolev n (f-g) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using hf.add (hg.smul (-1))

def SmoothL2 (f : PlaneL2) : Prop := ∀ n : ℕ, Sobolev n f

lemma SmoothL2.derivative {f : PlaneL2} (hf : SmoothL2 f) (j : Bool) :
    ∃ df : PlaneL2, SmoothL2 df ∧
      planeFourier df =ᵐ[volume] fun z => directionSymbol (axis j) z*planeFourier f z := by
  obtain ⟨C,hC,hCt⟩ := (hf 1).translation_bound
  let hd := (memLp_directionSymbol_of_translation_bound f hC hCt (axis j)).1
  let df := planeFourier.symm (hd.toLp (fun z => directionSymbol (axis j) z*planeFourier f z))
  have hdf : HasDerivAt (fun t : ℝ => translateL2 (t • axis j) f) df 0 :=
    hasDerivAt_translateL2 f (axis j) hd
  refine ⟨df,?_,?_⟩
  · intro n
    obtain ⟨g,hg,hrg⟩ := (hf (n+1)).2 j
    rwa [hdf.unique hg]
  · change planeFourier (planeFourier.symm _) =ᵐ[volume] _
    rw [planeFourier.apply_symm_apply]
    exact MemLp.coeFn_toLp hd

lemma directionSymbol_square_sum (z : ℂ) :
    directionSymbol 1 z ^ 2 + directionSymbol Complex.I z ^ 2 =
      -(4*Real.pi^2:ℂ)*(‖z‖^2:ℝ) := by
  have hx : inner ℝ (1:ℂ) z=z.re := by
    simp [real_inner_eq_re_inner,RCLike.inner_apply]
  have hy : inner ℝ Complex.I z=z.im := by
    simp [real_inner_eq_re_inner,RCLike.inner_apply]
  rw [directionSymbol,directionSymbol,hx,hy,Complex.sq_norm,Complex.normSq_apply]
  push_cast
  calc
    (2*↑Real.pi*Complex.I*↑z.re)^2+(2*↑Real.pi*Complex.I*↑z.im)^2 =
      4*↑Real.pi^2*Complex.I^2*((z.re:ℂ)^2+(z.im:ℂ)^2) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

lemma bessel_pointwise (z w : ℂ) :
    w-(4*Real.pi^2:ℂ)⁻¹*
      (directionSymbol 1 z*(directionSymbol 1 z*w)+
       directionSymbol Complex.I z*(directionSymbol Complex.I z*w)) =
      (1+(‖z‖^2:ℝ):ℂ)*w := by
  have hpi : (4*Real.pi^2:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0:ℝ)<4*Real.pi^2))
  calc
    _ = w-(4*Real.pi^2:ℂ)⁻¹*
      ((directionSymbol 1 z^2+directionSymbol Complex.I z^2)*w) := by ring
    _ = _ := by rw [directionSymbol_square_sum]; field_simp; ring

lemma fourier_bessel_ae (f dxx dyy : PlaneL2) :
    planeFourier (f-(4*Real.pi^2:ℂ)⁻¹ • (dxx+dyy)) =ᵐ[volume]
      fun z => planeFourier f z-(4*Real.pi^2:ℂ)⁻¹*
        (planeFourier dxx z+planeFourier dyy z) := by
  let c : ℂ := (4*Real.pi^2:ℂ)⁻¹
  rw [map_sub,map_smul,map_add]
  filter_upwards [Lp.coeFn_sub (planeFourier f) (c • (planeFourier dxx+planeFourier dyy)),
    Lp.coeFn_smul c (planeFourier dxx+planeFourier dyy),
    Lp.coeFn_add (planeFourier dxx) (planeFourier dyy)] with z h1 h2 h3
  simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply] at h1 h2 h3
  rw [h1,h2,h3]
  rfl

lemma SmoothL2.bessel_step {f : PlaneL2} (hf : SmoothL2 f) :
    ∃ g : PlaneL2, SmoothL2 g ∧
      planeFourier g =ᵐ[volume] fun z => (1+(‖z‖^2:ℝ):ℂ)*planeFourier f z := by
  obtain ⟨dx,hrx,hx⟩ := hf.derivative false
  obtain ⟨dy,hry,hy⟩ := hf.derivative true
  obtain ⟨dxx,hrxx,hxx⟩ := hrx.derivative false
  obtain ⟨dyy,hryy,hyy⟩ := hry.derivative true
  let c : ℂ := (4*Real.pi^2:ℂ)⁻¹
  refine ⟨f-c • (dxx+dyy),fun n => (hf n).sub (((hrxx n).add (hryy n)).smul c),?_⟩
  filter_upwards [hx,hy,hxx,hyy,fourier_bessel_ae f dxx dyy] with z hx hy hxx hyy hz
  rw [hz,hxx,hyy,hx,hy]
  exact bessel_pointwise z (planeFourier f z)

lemma SmoothL2.fourier_weighted_memLp {f : PlaneL2} (hf : SmoothL2 f) (n : ℕ) :
    MemLp (fun z => ((1+‖z‖^2)^n:ℝ)*planeFourier f z) 2 volume := by
  induction n generalizing f with
  | zero => simpa using Lp.memLp (planeFourier f)
  | succ n ih =>
    obtain ⟨g,hrg,hg⟩ := hf.bessel_step
    apply MemLp.ae_eq (hf_Lp:=ih hrg)
    filter_upwards [hg] with z hz
    rw [hz]
    push_cast
    ring

open scoped ContDiff

lemma inverse_weight_memLp : MemLp (fun z : ℂ => (1+‖z‖^2)⁻¹) 2 volume := by
  have hc : Continuous (fun z : ℂ => (1+‖z‖^2)⁻¹) :=
    (continuous_const.add (continuous_norm.pow 2)).inv₀ (fun z : ℂ => show 1+‖z‖^2 ≠ 0 from ne_of_gt (by positivity))
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hdim : (Module.finrank ℝ ℂ:ℝ)<4 := by norm_num
  have hi : Integrable (fun z : ℂ => Real.rpow (1+‖z‖^2) (-4/2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (E:=ℂ) hdim
  apply hi.congr
  filter_upwards with z
  norm_num [Real.rpow_neg (by positivity : (0:ℝ)≤1+‖z‖^2),Real.rpow_two,inv_pow]

lemma SmoothL2.fourier_weighted_integrable {f : PlaneL2} (hf : SmoothL2 f) (n : ℕ) :
    Integrable (fun z => (1+‖z‖^2)^n*‖planeFourier f z‖) volume := by
  have hi := inverse_weight_memLp.integrable_mul (hf.fourier_weighted_memLp (n+1)).norm
  apply hi.congr
  filter_upwards with z
  change (1+‖z‖^2)⁻¹*‖((1+‖z‖^2)^(n+1):ℝ)*planeFourier f z‖=_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (1+‖z‖^2)^(n+1)),pow_succ]
  have hn : (1+‖z‖^2) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  rw [pow_succ]
  ring

lemma SmoothL2.fourier_moments {f : PlaneL2} (hf : SmoothL2 f) (n : ℕ) :
    Integrable (fun z => ‖z‖^n*‖planeFourier f z‖) volume := by
  apply (hf.fourier_weighted_integrable n).mono'
    (((continuous_norm.pow n).aestronglyMeasurable).mul
      (Lp.memLp (planeFourier f)).aestronglyMeasurable.norm)
  apply Filter.Eventually.of_forall
  intro z
  change ‖‖z‖^n*‖planeFourier f z‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  nlinarith [sq_nonneg (‖z‖-1)]

lemma SmoothL2.fourier_integrable {f : PlaneL2} (hf : SmoothL2 f) :
    Integrable (planeFourier f : ℂ → ℂ) volume := by
  apply integrable_norm_iff (Lp.memLp (planeFourier f)).aestronglyMeasurable |>.mp
  simpa using hf.fourier_moments 0

def smoothRepresentative (f : PlaneL2) : ℂ → ℂ := 𝓕⁻ (planeFourier f : ℂ → ℂ)

lemma SmoothL2.contDiff {f : PlaneL2} (hf : SmoothL2 f) :
    ContDiff ℝ ∞ (smoothRepresentative f) := by
  have hc : ContDiff ℝ ∞ (𝓕 (planeFourier f : ℂ → ℂ)) :=
    Real.contDiff_fourier (fun n _ => hf.fourier_moments n)
  have he : smoothRepresentative f=(fun z => (𝓕 (planeFourier f : ℂ → ℂ)) (-z)) := by
    funext z
    exact Real.fourierInv_eq_fourier_neg _ _
  rw [he]
  exact hc.comp contDiff_neg

end CannonBeltrami

end
end
end
end
end
end
end
end

end OAI
