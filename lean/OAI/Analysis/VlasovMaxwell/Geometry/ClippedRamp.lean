import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.AbsolutelyContinuousIntervalContinuousDerivative

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def clippedRamp (a ℓ t : ℝ) : ℝ := min 1 (max 0 ((t-a)/ℓ))

def directionWeight (a b ℓ t : ℝ) : ℝ := clippedRamp a ℓ t-clippedRamp (b-ℓ) ℓ t

lemma clippedRamp_lipschitz (a ℓ : ℝ) : LipschitzWith ‖ℓ⁻¹‖₊ (clippedRamp a ℓ) := by
  have h : LipschitzWith ‖ℓ⁻¹‖₊ (fun t : ℝ=>(t-a)/ℓ) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [Real.dist_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [←sub_div,sub_sub_sub_cancel_right,abs_div]
    simp only [div_eq_mul_inv,abs_inv]
    exact le_of_eq (mul_comm _ _)
  exact (h.const_max 0).const_min 1

lemma clippedRamp_of_le {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : t≤a) : clippedRamp a ℓ t=0 := by
  rw [clippedRamp,max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hℓ.le)]
  norm_num

lemma clippedRamp_of_ge {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : a+ℓ≤t) : clippedRamp a ℓ t=1 := by
  have h : 1≤(t-a)/ℓ := (le_div_iff₀ hℓ).mpr (by linarith)
  rw [clippedRamp,min_eq_left (le_trans h (le_max_right _ _))]

lemma clippedRamp_of_between {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : t∈Icc a (a+ℓ)) :
    clippedRamp a ℓ t=(t-a)/ℓ := by
  have h0 : 0≤(t-a)/ℓ := div_nonneg (sub_nonneg.mpr ht.1) hℓ.le
  have h1 : (t-a)/ℓ≤1 := (div_le_iff₀ hℓ).mpr (by linarith [ht.2])
  rw [clippedRamp,max_eq_right h0,min_eq_right h1]

lemma directionWeight_lipschitz (a b ℓ : ℝ) :
    LipschitzWith (‖ℓ⁻¹‖₊+‖ℓ⁻¹‖₊) (directionWeight a b ℓ) :=
  (clippedRamp_lipschitz a ℓ).sub (clippedRamp_lipschitz (b-ℓ) ℓ)

lemma directionWeight_left {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Icc a (a+ℓ)) : directionWeight a b ℓ t=(t-a)/ℓ := by
  rw [directionWeight,clippedRamp_of_between hℓ ht,clippedRamp_of_le hℓ (by linarith [ht.2]),sub_zero]

lemma directionWeight_middle {a b ℓ t : ℝ} (hℓ : 0<ℓ) (_hab : 2*ℓ≤b-a)
    (ht : t∈Icc (a+ℓ) (b-ℓ)) : directionWeight a b ℓ t=1 := by
  rw [directionWeight,clippedRamp_of_ge hℓ ht.1,clippedRamp_of_le hℓ ht.2,sub_zero]

lemma directionWeight_right {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Icc (b-ℓ) b) : directionWeight a b ℓ t=(b-t)/ℓ := by
  rw [directionWeight,clippedRamp_of_ge hℓ (by linarith [ht.1]),
    clippedRamp_of_between hℓ (by simpa only [sub_add_cancel] using ht)]
  field_simp
  ring

lemma directionWeight_endpoints {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    directionWeight a b ℓ a=0 ∧ directionWeight a b ℓ b=0 := by
  constructor
  · rw [directionWeight_left hℓ hab ⟨le_rfl,by linarith⟩,sub_self,zero_div]
  · rw [directionWeight_right hℓ hab ⟨by linarith,le_rfl⟩,sub_self,zero_div]

lemma directionWeight_bounds {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    0≤directionWeight a b ℓ t ∧ directionWeight a b ℓ t≤1 := by
  have hmon : clippedRamp (b-ℓ) ℓ t≤clippedRamp a ℓ t := by
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    exact div_le_div_of_nonneg_right (by linarith) hℓ.le
  have h0 (c : ℝ) : 0≤clippedRamp c ℓ t := le_min (by norm_num) (le_max_left _ _)
  have h1 (c : ℝ) : clippedRamp c ℓ t≤1 := min_le_left _ _
  unfold directionWeight
  constructor
  · exact sub_nonneg.mpr hmon
  · linarith [h0 (b-ℓ),h1 a]

lemma directionWeight_deriv_left {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo a (a+ℓ)) : deriv (directionWeight a b ℓ) t=ℓ⁻¹ := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun u=>(u-a)/ℓ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_left hℓ hab (Ioo_subset_Icc_self hu)
  have hd := (((hasDerivAt_id t).sub_const a).div_const ℓ).congr_of_eventuallyEq he
  simpa only [one_div] using hd.deriv

lemma directionWeight_deriv_middle {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo (a+ℓ) (b-ℓ)) : deriv (directionWeight a b ℓ) t=0 := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun _=>1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_middle hℓ hab (Ioo_subset_Icc_self hu)
  exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

lemma directionWeight_deriv_right {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo (b-ℓ) b) : deriv (directionWeight a b ℓ) t= -ℓ⁻¹ := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun u=>(b-u)/ℓ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_right hℓ hab (Ioo_subset_Icc_self hu)
  have hd := (((hasDerivAt_id t).const_sub b).div_const ℓ).congr_of_eventuallyEq he
  simpa only [neg_div,one_div] using hd.deriv

lemma directionWeight_signed_average {a b ℓ : ℝ} {g g' : ℝ→Vec}
    (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t) :
    (∫t in a..b,directionWeight a b ℓ t • g' t)=
      ℓ⁻¹ • ((∫t in b-ℓ..b,g t)-(∫t in a..a+ℓ,g t)) := by
  have hab' : a≤b := by linarith
  have hL : a≤a+ℓ := by linarith
  have hC : a+ℓ≤b-ℓ := by linarith
  have hR : b-ℓ≤b := by linarith
  have hψ := (directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b) |>.absolutelyContinuousOnInterval
  have hu : ContinuousOn g (uIcc a b) := by simpa only [uIcc_of_le hab'] using hg
  have hi := hψ.intervalIntegrable_deriv.smul_continuousOn hu
  have hiL : IntervalIntegrable (fun t=>deriv (directionWeight a b ℓ) t • g t) volume a (a+ℓ) :=
    hi.mono_set (by rw [uIcc_of_le hL,uIcc_of_le hab']; exact Icc_subset_Icc le_rfl (hC.trans hR))
  have hiR : IntervalIntegrable (fun t=>deriv (directionWeight a b ℓ) t • g t) volume (b-ℓ) b :=
    hi.mono_set (by rw [uIcc_of_le hR,uIcc_of_le hab']; exact Icc_subset_Icc (hL.trans hC) le_rfl)
  have hiC : IntervalIntegrable (fun t=>deriv (directionWeight a b ℓ) t • g t) volume (a+ℓ) (b-ℓ) :=
    hi.mono_set (by rw [uIcc_of_le hC,uIcc_of_le hab']; exact Icc_subset_Icc hL hR)
  have eL : (∫t in a..a+ℓ,deriv (directionWeight a b ℓ) t • g t)=ℓ⁻¹ • ∫t in a..a+ℓ,g t := by
    rw [←intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_left hℓ hab (by simpa only [uIoo_of_le hL] using ht)]
  have eR : (∫t in b-ℓ..b,deriv (directionWeight a b ℓ) t • g t)= -ℓ⁻¹ • ∫t in b-ℓ..b,g t := by
    rw [←intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_right hℓ hab (by simpa only [uIoo_of_le hR] using ht)]
  have eC : (∫t in a+ℓ..b-ℓ,deriv (directionWeight a b ℓ) t • g t)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a+ℓ) (b:=b-ℓ)]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_middle hℓ hab (by simpa only [uIoo_of_le hC] using ht),zero_smul]
  rw [ac_weighted_vector_ibp_closed hab' hψ hg hg' hd,
    (directionWeight_endpoints hℓ hab).1,(directionWeight_endpoints hℓ hab).2]
  simp only [zero_smul,sub_self]
  rw [←intervalIntegral.integral_add_adjacent_intervals hiL (hiC.trans hiR),
    ←intervalIntegral.integral_add_adjacent_intervals hiC hiR,eL,eC,eR,zero_add,zero_sub]
  rw [neg_smul,smul_sub]
  abel

lemma interval_average_error {a b ε : ℝ} {g : ℝ→Vec} {v : Vec}
    (hab : a<b) (hg : ContinuousOn g (Icc a b))
    (hb : ∀t∈Icc a b,‖g t-v‖≤ε) :
    ‖(b-a)⁻¹ • (∫t in a..b,g t)-v‖≤ε := by
  have hpos : 0<b-a := sub_pos.mpr hab
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  have he : (b-a)⁻¹ • (∫t in a..b,g t)-v =
      (b-a)⁻¹ • (∫t in a..b,g t-v) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const,smul_sub,smul_smul,inv_mul_cancel₀ hpos.ne',one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)]
  have hb' : ‖∫t in a..b,g t-v‖≤ε*(b-a) := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht=>hb t ?_) using 1
    · rw [abs_of_pos hpos]
    · rw [uIoc_of_le hab.le] at ht
      exact Ioc_subset_Icc_self ht
  calc
    _ ≤ (b-a)⁻¹*(ε*(b-a)) := mul_le_mul_of_nonneg_left hb' (inv_pos.mpr hpos).le
    _ = ε := by field_simp

lemma directionWeight_signed_error {a b ℓ ε : ℝ} {g g' : ℝ→Vec}
    (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t)
    (hleft : ∀t∈Icc a (a+ℓ),‖g t-g a‖≤ε)
    (hright : ∀t∈Icc (b-ℓ) b,‖g t-g b‖≤ε) :
    ‖(∫t in a..b,directionWeight a b ℓ t • g' t)-(g b-g a)‖≤2*ε := by
  have hL : ‖ℓ⁻¹ • (∫t in a..a+ℓ,g t)-g a‖≤ε := by
    simpa only [add_sub_cancel_left] using interval_average_error (by linarith : a<a+ℓ)
      (hg.mono (Icc_subset_Icc le_rfl (by linarith))) hleft
  have hR : ‖ℓ⁻¹ • (∫t in b-ℓ..b,g t)-g b‖≤ε := by
    simpa only [sub_sub_cancel] using interval_average_error (by linarith : b-ℓ<b)
      (hg.mono (Icc_subset_Icc (by linarith) le_rfl)) hright
  rw [directionWeight_signed_average hℓ hab hg hg' hd,smul_sub]
  have he : ℓ⁻¹ • (∫t in b-ℓ..b,g t)-ℓ⁻¹ • (∫t in a..a+ℓ,g t)-(g b-g a)=
      (ℓ⁻¹ • (∫t in b-ℓ..b,g t)-g b)-(ℓ⁻¹ • (∫t in a..a+ℓ,g t)-g a) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

lemma directionWeight_signed_exit {a b ℓ δ : ℝ} {g g' : ℝ→Vec}
    (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t)
    (hleft : ∀t∈Icc a (a+ℓ),‖g t-g a‖≤δ/4)
    (hright : ∀t∈Icc (b-ℓ) b,‖g t-g b‖≤δ/4)
    (hexit : δ≤‖g b-g a‖) :
    δ/2≤‖∫t in a..b,directionWeight a b ℓ t • g' t‖ := by
  have he := directionWeight_signed_error hℓ hab hg hg' hd hleft hright
  have hn := norm_sub_norm_le (g b-g a) (∫t in a..b,directionWeight a b ℓ t • g' t)
  rw [norm_sub_rev (g b-g a) (∫t in a..b,directionWeight a b ℓ t • g' t)] at hn
  linarith

lemma directionWeight_total_variation {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 := by
  have hab' : a≤b := by linarith
  have hL : a≤a+ℓ := by linarith
  have hC : a+ℓ≤b-ℓ := by linarith
  have hR : b-ℓ≤b := by linarith
  have hψ := (directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b) |>.absolutelyContinuousOnInterval
  have hi : IntervalIntegrable (fun t=>|deriv (directionWeight a b ℓ) t|) volume a b :=
    hψ.intervalIntegrable_deriv.norm
  have hiL := hi.mono_set (show uIcc a (a+ℓ)⊆uIcc a b by
    rw [uIcc_of_le hL,uIcc_of_le hab']; exact Icc_subset_Icc le_rfl (hC.trans hR))
  have hiC := hi.mono_set (show uIcc (a+ℓ) (b-ℓ)⊆uIcc a b by
    rw [uIcc_of_le hC,uIcc_of_le hab']; exact Icc_subset_Icc hL hR)
  have hiR := hi.mono_set (show uIcc (b-ℓ) b⊆uIcc a b by
    rw [uIcc_of_le hR,uIcc_of_le hab']; exact Icc_subset_Icc (hL.trans hC) le_rfl)
  have eL : (∫t in a..a+ℓ,|deriv (directionWeight a b ℓ) t|)=1 := by
    calc
      _ = ∫t in a..a+ℓ,ℓ⁻¹ := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        dsimp only
        rw [directionWeight_deriv_left hℓ hab (by simpa only [uIoo_of_le hL] using ht),
          abs_of_pos (inv_pos.mpr hℓ)]
      _ = 1 := by rw [intervalIntegral.integral_const]; simp [hℓ.ne']
  have eR : (∫t in b-ℓ..b,|deriv (directionWeight a b ℓ) t|)=1 := by
    calc
      _ = ∫t in b-ℓ..b,ℓ⁻¹ := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        dsimp only
        rw [directionWeight_deriv_right hℓ hab (by simpa only [uIoo_of_le hR] using ht),
          abs_neg,abs_of_pos (inv_pos.mpr hℓ)]
      _ = 1 := by rw [intervalIntegral.integral_const]; simp [hℓ.ne']
  have eC : (∫t in a+ℓ..b-ℓ,|deriv (directionWeight a b ℓ) t|)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a+ℓ) (b:=b-ℓ)]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_middle hℓ hab (by simpa only [uIoo_of_le hC] using ht),abs_zero]
  rw [←intervalIntegral.integral_add_adjacent_intervals hiL (hiC.trans hiR),
    ←intervalIntegral.integral_add_adjacent_intervals hiC hiR,eL,eC,eR]
  norm_num

end RVM

end

end OAI
