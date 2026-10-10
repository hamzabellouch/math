import OAI.Combinatorics.HoneycombChords.CharacteristicProducts
import OAI.Combinatorics.HoneycombChords.ResidualMeans

namespace OAI

/-!
# Asymptotic estimates for strip residual means

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology Asymptotics

lemma movingPole_sq_ge {N : ℕ} (hN : 1 ≤ N) : (N:ℝ) ≤ (movingPole N)^2 := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  rw [movingPole,← Real.rpow_natCast _ 2,←Real.rpow_mul (Nat.cast_nonneg N)]
  calc
    (N:ℝ) = (N:ℝ)^(1:ℝ) := (rpow_one _).symm
    _ ≤ _ := rpow_le_rpow_of_exponent_le hN' (by norm_num)

lemma prefix_penalty_uniform {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    (1+c/(movingPole N)^2)^(2*N+1) ≤ Real.exp (3*c) := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hT:0<(movingPole N)^2 := lt_of_lt_of_le (by linarith) (movingPole_sq_ge hN)
  have hbase: 1+c/(movingPole N)^2 ≤ Real.exp (c/(movingPole N)^2) := by
    linarith [Real.add_one_le_exp (c/(movingPole N)^2)]
  calc
    _ ≤ (Real.exp (c/(movingPole N)^2))^(2*N+1) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((2*N+1:ℕ)*(c/(movingPole N)^2)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (3*c) := by
      apply Real.exp_le_exp.mpr
      have hh : ((2*N+1:ℕ):ℝ) ≤ 3*(movingPole N)^2 := by
        push_cast
        nlinarith [movingPole_sq_ge hN]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hT).mpr
      nlinarith [mul_le_mul_of_nonneg_right hh hc]

lemma exponential_tail_below_power (a : ℝ) :
    ∀ᶠ N : ℕ in atTop,(2/3:ℝ)^N*Real.exp ((Real.log (3/2)/2)*N) ≤ ((N:ℝ)+1)^a := by
  let ε : ℝ:=Real.log (3/2)/2
  have he : 0<ε := by dsimp [ε]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hlim:=((isLittleO_exp_neg_mul_rpow_atTop he a).def (show (0:ℝ)<Real.exp (-ε) by positivity))
  have ht : Tendsto (fun N : ℕ=>(N:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hlim] with N hN
  have hpos : 0<(N:ℝ)+1 := by positivity
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.rpow_pos_of_pos hpos _)] at hN
  have heq : (2/3:ℝ)^N*Real.exp (ε*N)=Real.exp (-ε*N) := by
    rw [←Real.exp_log (by norm_num : (0:ℝ)<2/3),←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    dsimp [ε]
    rw [Real.log_div (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0),
      Real.log_div (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
    ring
  change (2/3:ℝ)^N*Real.exp (ε*N) ≤ _
  rw [heq]
  have hx : Real.exp (-ε*N)=Real.exp ε*Real.exp (-ε*((N:ℝ)+1)) := by
    rw [←Real.exp_add]
    congr 1; ring
  rw [hx]
  have h:=mul_le_mul_of_nonneg_left hN (le_of_lt (Real.exp_pos ε))
  have hc : Real.exp ε*Real.exp (-ε)=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  simpa only [←mul_assoc,hc,one_mul] using h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Real Filter Topology

lemma stripJet_familyGram (N : ℕ) (s t : ℝ) (w : ℝ → ℝ) :
    familyGram w (stripJetFamily N s) (stripJetFamily N t)=
      jetGram (n:=2*N+1) w (interiorKnotLabels N s) (interiorKnotLabels N t) := rfl

lemma jetFixedMean_bounds {u : ℝ} (hu : 0<u) (hu4 : u ≤ 4) :
    ∃ a A : ℝ,0<a ∧ 0<A ∧ ∀ᶠ N : ℕ in atTop,∀ s t : ℝ,0<s → s<angle → 0<t → t<angle →
      a*((N:ℝ)+1)^(3*(Real.sqrt u-8/3)/8) ≤ jetFixedMean N s t u ∧
      jetFixedMean N s t u ≤ A*((N:ℝ)+1)^(3*(Real.sqrt u-8/3)/8) := by
  have hs : Real.sqrt u < 8/3 := by
    have h:=Real.sqrt_le_sqrt hu4
    norm_num at h
    linarith
  obtain ⟨a,A,ha,hA,hb⟩:=first_oblique_characteristic_product_bounds (Real.sqrt_pos.mpr hu) hs
  refine ⟨a,A,ha,hA,?_⟩
  filter_upwards [hb] with N hN
  intro s t hs hsL ht htL
  simpa only [jetFixedMean,physicalFixedWeight_characteristic hu.le,stripJet_familyGram] using hN s t hs hsL ht htL

lemma jetMovingMean_bound {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s t : ℝ,0<s → s<angle → 0<t → t<angle →
      jetMovingMean N s t ((movingPole N)^2) ≤ Real.exp (ε*N) := by
  filter_upwards [first_oblique_moving_subexponential hε] with N hN
  intro s t hs hsL ht htL
  have hw : physicalMovingWeight ((movingPole N)^2)=characteristicRatio (Real.sqrt 2*movingPole N) (movingPole N) := by
    funext p
    simp only [physicalMovingWeight,characteristicRatio,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  simpa only [jetMovingMean,hw,stripJet_familyGram] using hN s t hs hsL ht htL

lemma physical_means_asymptotic {u : ℝ} (hu : 0<u) (hu4 : u ≤ 4) :
    ∃ a A : ℝ,0<a ∧ 0<A ∧ ∀ᶠ N : ℕ in atTop,∀ s t : ℝ,0<s → s<angle → 0<t → t<angle →
      let P:=((N:ℝ)+1)^(3*(Real.sqrt u-8/3)/8)
      a*P ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) (-u) ∧
      meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) (-u) ≤ A*P ∧
      a*P ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) (-u) ∧
      meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) (-u) ≤ A*P := by
  obtain ⟨a,A,ha,hA,hbound⟩:=jetFixedMean_bounds hu hu4
  let E : ℝ:=Real.exp (3*physicalPole 0)
  let ε : ℝ:=Real.log (3/2)/2
  have he : 0<ε := by dsimp [ε]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨a/2,2*E*A+2,by positivity,by dsimp [E];positivity,?_⟩
  filter_upwards [hbound,jetMovingMean_bound he,exponential_tail_below_power (3*(Real.sqrt u-8/3)/8),
    eventually_ge_atTop (1:ℕ)] with N hB hM htail hN
  intro s t hs hsL ht htL
  dsimp only
  let P : ℝ:=((N:ℝ)+1)^(3*(Real.sqrt u-8/3)/8)
  have hP : 0<P := by dsimp [P];positivity
  obtain ⟨hBl,hBu⟩:=hB s t hs hsL ht htL
  have hB0 : 0 ≤ jetFixedMean N s t u := le_of_lt (lt_of_lt_of_le (mul_pos ha hP) hBl)
  have hT : 0<(movingPole N)^2 := lt_of_lt_of_le (by exact_mod_cast (by omega : 0<N)) (movingPole_sq_ge hN)
  have hpen := prefix_penalty_uniform hN (physicalPole_pos 0).le
  have hup : (2*(1+physicalPole 0/(movingPole N)^2)^(2*N+1))*jetFixedMean N s t u+
      (2*(2/3:ℝ)^N)*jetMovingMean N s t ((movingPole N)^2) ≤ (2*E*A+2)*P := by
    have hfirst:=mul_le_mul_of_nonneg_right hpen hB0
    have hsecond:=mul_le_mul_of_nonneg_left (hM s t hs hsL ht htL) (show 0 ≤ (2/3:ℝ)^N by positivity)
    have hfixed:=mul_le_mul_of_nonneg_left hBu (show 0 ≤ E from (Real.exp_pos _).le)
    change (2/3:ℝ)^N*Real.exp (ε*N) ≤ P at htail
    change _ ≤ E at hpen
    nlinarith [Real.exp_pos (3*physicalPole 0)]
  have hl₀:=hZero_mean_lower hN hu.le hu4 hs hsL ht htL
  have hl₁:=hOne_mean_lower hN hu.le hu4 hs hsL ht htL
  have hu₀:=hZero_mean_upper hN hu.le hu4 hT hs hsL ht htL
  have hu₁:=hOne_mean_upper hN hu.le hu4 hT hs hsL ht htL
  refine ⟨?_,hu₀.trans hup,?_,hu₁.trans hup⟩
  · nlinarith [mul_pos ha hP]
  · linarith

/-- The two normalized residual means have exponent `-1/4`. -/
theorem physical_means_at_minus_four :
    ∃ a A : ℝ,0<a ∧ 0<A ∧ ∀ᶠ N : ℕ in atTop,∀ s t : ℝ,0<s → s<angle → 0<t → t<angle →
      let P:=((N:ℝ)+1)^(-1/4:ℝ)
      a*P ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) (-4) ∧
      meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) (-4) ≤ A*P ∧
      a*P ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) (-4) ∧
      meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) (-4) ≤ A*P := by
  have h:=physical_means_asymptotic (u:=4) (by norm_num) le_rfl
  norm_num at h ⊢
  exact h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology

noncomputable def parameterFamily (N : ℕ) (t : ℝ) : Fin (2*N+1) → ℝ → ℝ :=
  Function.update (fixedFamily N) (centralIndex N) (cosineKernelJet 0 0 (t^2))
lemma parameterFamily_interior (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    parameterFamily N t=stripJetFamily N t := fixedFamily_update_interior N ht htL

lemma familyGram_update_right {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (i : Fin n) (H : ℝ → ℝ) :
    familyGram w F (Function.update G i H)=
      (familyGram w F G).updateCol i (fun j=>∫ p in Set.Ioi 0,F j (p^2)*H (p^2)*w p) := by
  ext j k
  rw [Matrix.updateCol_apply]
  by_cases hk : k=i
  · subst k
    simp only [familyGram,Function.update_self,ite_true]
  · simp only [familyGram,Function.update_of_ne hk,ite_eq_right hk]

lemma cosineMoment_as_cosh (q : ℝ → ℝ) (t : ℝ) :
    (∫ p in Set.Ioi 0,q p*cosineKernelJet 0 0 (t^2) (p^2))=
      ∫ p in Set.Ioi 0,q p*Real.cosh (t*p) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  congr 1
  apply Complex.ofReal_injective
  rw [←C_eq_beta_square,C_sq _ hp.le]

lemma parameterGram_continuousOn {n : ℕ} (N : ℕ) (w : ℝ → ℝ) (F : Fin n → ℝ → ℝ)
    (hqm : ∀ i,Measurable (fun p=>F i (p^2)*w p))
    (hqi : ∀ i,IntegrableOn (fun p=>|F i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0)) :
    ContinuousOn (fun t : ℝ=>fun i : Fin n=>fun j : Fin (2*N+1)=>
      ∫ p in Set.Ioi 0,F i (p^2)*parameterFamily N t j (p^2)*w p) (Set.Icc 0 angle) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  by_cases hj : j=centralIndex N
  · subst j
    simp only [parameterFamily,Function.update_self]
    have he (t : ℝ) : (∫ p in Set.Ioi 0,F i (p^2)*cosineKernelJet 0 0 (t^2) (p^2)*w p)=
        ∫ p in Set.Ioi 0,(F i (p^2)*w p)*Real.cosh (t*p) := by
      rw [←cosineMoment_as_cosh]
      congr 1
      funext p
      ring
    simp_rw [he]
    exact cosh_pair_continuousOn _ (hqm i) (hqi i)
  · simp only [parameterFamily,Function.update_of_ne hj]
    exact continuousOn_const

lemma mixedGram_det_integral (N : ℕ) (w : ℝ → ℝ) (F : Fin (2*N+1) → ℝ → ℝ)
    (hqm : ∀ i,Measurable (fun p=>F i (p^2)*w p))
    (hqi : ∀ i,IntegrableOn (fun p=>|F i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0)) :
    (familyGram w F (mixedFamily N)).det=
      ∫ t in (0:ℝ)..angle,(familyGram w F (parameterFamily N t)).det := by
  have hvec : ContinuousOn (fun t=>fun j=>∫ p in Set.Ioi 0,(F j (p^2)*w p)*Real.cosh (t*p))
      (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact continuousOn_pi.mpr (fun j=>cosh_pair_continuousOn _ (hqm j) (hqi j))
  have he (i : Fin (2*N+1)) : (∫ p in Set.Ioi 0,F i (p^2)*realG (p^2)*w p)=
      ∫ t in (0:ℝ)..angle,∫ p in Set.Ioi 0,(F i (p^2)*w p)*Real.cosh (t*p) := by
    rw [←cosh_pair_fubini _ (hqm i) (hqi i)]
    congr 1
    funext p
    ring
  rw [mixedFamily,familyGram_update_right]
  simp_rw [he]
  rw [colDet_integral _ _ _ hvec.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  unfold parameterFamily
  rw [familyGram_update_right]
  congr 2
  funext i
  rw [←cosineMoment_as_cosh]
  congr 1
  funext p
  ring

lemma mixedGram_ratio_bounds (N : ℕ) (w : ℝ → ℝ) (F R : Fin (2*N+1) → ℝ → ℝ) (a A : ℝ)
    (hfm : ∀ i,Measurable (fun p=>F i (p^2)*w p))
    (hfi : ∀ i,IntegrableOn (fun p=>|F i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hrm : ∀ i,Measurable (fun p=>R i (p^2)*w p))
    (hri : ∀ i,IntegrableOn (fun p=>|R i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hd : 0<(familyGram w F (mixedFamily N)).det)
    (hdt : ∀ t,0<t → t<angle → 0<(familyGram w F (stripJetFamily N t)).det)
    (hb : ∀ t,0<t → t<angle →
      a ≤ (familyGram w R (stripJetFamily N t)).det/(familyGram w F (stripJetFamily N t)).det ∧
      (familyGram w R (stripJetFamily N t)).det/(familyGram w F (stripJetFamily N t)).det ≤ A) :
    a ≤ (familyGram w R (mixedFamily N)).det/(familyGram w F (mixedFamily N)).det ∧
    (familyGram w R (mixedFamily N)).det/(familyGram w F (mixedFamily N)).det ≤ A := by
  have hcontF : ContinuousOn (fun t=>(familyGram w F (parameterFamily N t)).det) (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact (continuous_id.matrix_det).comp_continuousOn (parameterGram_continuousOn N w F hfm hfi)
  have hcontR : ContinuousOn (fun t=>(familyGram w R (parameterFamily N t)).det) (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact (continuous_id.matrix_det).comp_continuousOn (parameterGram_continuousOn N w R hrm hri)
  have hlo:=intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) strip_angle_pos.le
    (hcontF.intervalIntegrable.const_mul a) hcontR.intervalIntegrable
    (fun t ht=>by
      rw [parameterFamily_interior N ht.1 ht.2]
      exact (le_div_iff₀ (hdt t ht.1 ht.2)).mp (hb t ht.1 ht.2).1)
  have hup:=intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) strip_angle_pos.le
    hcontR.intervalIntegrable (hcontF.intervalIntegrable.const_mul A)
    (fun t ht=>by
      rw [parameterFamily_interior N ht.1 ht.2]
      exact (div_le_iff₀ (hdt t ht.1 ht.2)).mp (hb t ht.1 ht.2).2)
  rw [intervalIntegral.integral_const_mul,←mixedGram_det_integral N w F hfm hfi,
    ←mixedGram_det_integral N w R hrm hri] at hlo
  rw [intervalIntegral.integral_const_mul,←mixedGram_det_integral N w F hfm hfi,
    ←mixedGram_det_integral N w R hrm hri] at hup
  exact ⟨(le_div_iff₀ hd).mpr hlo,(div_le_iff₀ hd).mpr hup⟩

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology

lemma fixedFamily_measurable (N : ℕ) (i : Fin (2*N+1)) :
    Measurable (fun p=>fixedFamily N i (p^2)*stripDensity p) := by
  have hc : Continuous (fun p : ℝ=>fixedFamily N i (p^2)) :=
    (cosineKernelJet_contDiff_right _ 0 _ 0).continuous.comp (by fun_prop)
  exact hc.measurable.mul (by unfold stripDensity;fun_prop)

lemma weighted_cosh_norm_integrable {q : ℝ → ℝ}
    (hi : IntegrableOn (fun p=>q p*Real.cosh (angle*p)) (Set.Ioi 0)) :
    IntegrableOn (fun p=>|q p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  apply hi.norm.congr
  filter_upwards with p
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.cosh_pos _)]

lemma weighted_cosh_signed_integrable {q : ℝ → ℝ} (hq : Measurable q)
    (hi : IntegrableOn (fun p=>|q p| *Real.cosh (angle*p)) (Set.Ioi 0)) :
    IntegrableOn (fun p=>q p*Real.cosh (angle*p)) (Set.Ioi 0) := by
  apply hi.mono' (hq.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with p
  simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.cosh_pos _),le_refl]

lemma fixedFamily_cosh_integrable (N : ℕ) (i : Fin (2*N+1)) :
    IntegrableOn (fun p=>|fixedFamily N i (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  apply weighted_cosh_norm_integrable
  have hi:=strip_jet_pair_integrable (interiorKnot_nonneg N i (angle/2)) (sq_nonneg angle)
    ((interiorKnot_le N i (half_pos strip_angle_pos) (by linarith [strip_angle_pos])).trans
      (by nlinarith [sq_nonneg angle])) le_rfl (nodalOrder (interiorKnotLabels N (angle/2)) i) 0
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have he : cosineKernelJet 0 0 (angle^2) (p^2)=Real.cosh (angle*p) := by
    apply Complex.ofReal_injective
    rw [←C_eq_beta_square,C_sq _ hp.le]
  change fixedFamily N i (p^2)*cosineKernelJet 0 0 (angle^2) (p^2)*stripDensity p=_
  rw [he]
  ring

lemma bounded_target_cosh_integrable (H : ℝ → ℝ) (hHm : Measurable (fun p=>H (p^2)))
    (hH : ∀ p : ℝ,0<p → 0 ≤ H (p^2) ∧ H (p^2) ≤ 1) :
    IntegrableOn (fun p=>|H (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  have hi:=strip_jet_pair_integrable (b:=0) (c:=angle^2)
    (by rfl) (sq_nonneg angle) (by positivity) le_rfl 0 0
  simp only [cosineKernelJet_at_zero,pow_zero,mul_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul] at hi
  apply hi.mono'
  · exact (((hHm.mul (by unfold stripDensity;fun_prop)).abs).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hw:=(stripDensity_pos hp).le
    have hH0:=(hH p hp).1
    have he : cosineKernelJet 0 0 (angle^2) (p^2)=Real.cosh (angle*p) := by
      apply Complex.ofReal_injective
      rw [←C_eq_beta_square,C_sq _ hp.le]
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le),
      abs_of_nonneg (mul_nonneg hH0 hw),he]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hH p hp).2) (mul_nonneg hw (Real.cosh_pos (angle*p)).le)]

lemma residual_cosh_integrable {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ) (a : ℝ)
    (hFm : ∀ i,Measurable (fun p=>F i (p^2)*stripDensity p))
    (hHm : Measurable (fun p=>H (p^2)*stripDensity p))
    (hFi : ∀ i,IntegrableOn (fun p=>|F i (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hHi : IntegrableOn (fun p=>|H (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0)) :
    ∀ i,Measurable (fun p=>residualFamily F H a i (p^2)*stripDensity p) ∧
      IntegrableOn (fun p=>|residualFamily F H a i (p^2)*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  intro i
  have he : (fun p=>residualFamily F H a i (p^2)*stripDensity p)=
      (fun p=>F i (p^2)*stripDensity p-(F i a/H a)*(H (p^2)*stripDensity p)) := by
    funext p
    simp only [residualFamily]
    ring
  rw [he]
  refine ⟨(hFm i).sub (hHm.const_mul _),?_⟩
  apply weighted_cosh_norm_integrable
  convert (weighted_cosh_signed_integrable (hFm i) (hFi i)).sub
    ((weighted_cosh_signed_integrable hHm hHi).const_mul (F i a/H a)) using 1
  funext p
  simp only [Pi.sub_apply,residualFamily]
  ring

lemma hZero_sq_measurable : Measurable (fun p=>(hZero (p^2)).re) := by
  have he : (fun p=>(hZero (p^2)).re)=fun p=>1/(2*Real.cosh (angle*Real.sqrt (p^2))-1) := by
    funext p
    simp only [hZero,D,C,ite_eq_left (sq_nonneg p)]
    norm_cast
    simp only [one_div]
  rw [he]
  fun_prop

lemma hOne_sq_measurable : Measurable (fun p=>(hOne (p^2)).re) := by
  have he : (fun p=>(hOne (p^2)).re)=fun p=>Real.cosh ((angle/2)*Real.sqrt (p^2))/(2*Real.cosh (angle*Real.sqrt (p^2))-1) := by
    funext p
    simp only [hOne,D,C,ite_eq_left (sq_nonneg p)]
    norm_cast
  rw [he]
  fun_prop

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

/-! The positive mixture retains the distinct left and right Gram families. -/
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology

lemma mixedMean_bounds (N : ℕ) (H : ℝ → ℝ) (x a A : ℝ)
    (hHm : Measurable (fun p=>H (p^2)))
    (hH : ∀ p : ℝ,0<p → 0 ≤ H (p^2) ∧ H (p^2) ≤ 1)
    (hb : ∀ t : ℝ,0<t → t<angle →
      a ≤ meanResidualRatio stripDensity (stripJetFamily N (angle/2)) (stripJetFamily N t) H x ∧
      meanResidualRatio stripDensity (stripJetFamily N (angle/2)) (stripJetFamily N t) H x ≤ A) :
    a ≤ meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) H x ∧
    meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) H x ≤ A := by
  have hm : Measurable (fun p=>H (p^2)*stripDensity p) := hHm.mul (by unfold stripDensity;fun_prop)
  have hr:=residual_cosh_integrable (fixedFamily N) H x (fixedFamily_measurable N) hm
    (fixedFamily_cosh_integrable N) (bounded_target_cosh_integrable H hHm hH)
  exact mixedGram_ratio_bounds N stripDensity (fixedFamily N) (residualFamily (fixedFamily N) H x) a A
    (fixedFamily_measurable N) (fixedFamily_cosh_integrable N) (fun i=>(hr i).1) (fun i=>(hr i).2)
    (fixed_mixed_Gram_det_pos N)
    (fun t ht htL=>stripJet_gram_det_pos N (half_pos strip_angle_pos) (by linarith [strip_angle_pos]) ht htL) hb

theorem mixed_physical_means_asymptotic {u : ℝ} (hu : 0<u) (hu4 : u ≤ 4) :
    ∃ a A : ℝ,0<a ∧ 0<A ∧ ∀ᶠ N : ℕ in atTop,
      let P:=((N:ℝ)+1)^(3*(Real.sqrt u-8/3)/8)
      a*P ≤ meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hZero x).re) (-u) ∧
      meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hZero x).re) (-u) ≤ A*P ∧
      a*P ≤ meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hOne x).re) (-u) ∧
      meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hOne x).re) (-u) ≤ A*P := by
  obtain ⟨a,A,ha,hA,hB⟩:=physical_means_asymptotic hu hu4
  refine ⟨a,A,ha,hA,?_⟩
  filter_upwards [hB] with N hN
  have hs : 0<angle/2 := half_pos strip_angle_pos
  have hsL : angle/2<angle := by linarith [strip_angle_pos]
  have h₀:=mixedMean_bounds N (fun x=>(hZero x).re) (-u) _ _ hZero_sq_measurable
    (fun _ hp=>hZero_sq_unit hp.le)
    (fun t ht htL=>⟨(hN (angle/2) t hs hsL ht htL).1,(hN (angle/2) t hs hsL ht htL).2.1⟩)
  have h₁:=mixedMean_bounds N (fun x=>(hOne x).re) (-u) _ _ hOne_sq_measurable
    (fun _ hp=>hOne_sq_unit hp.le)
    (fun t ht htL=>(hN (angle/2) t hs hsL ht htL).2.2)
  exact ⟨h₀.1,h₀.2,h₁⟩

/-- Normalized residuals for the two mixed families have exponent `-1/4`. -/
theorem mixed_physical_means_at_minus_four :
    ∃ a A : ℝ,0<a ∧ 0<A ∧ ∀ᶠ N : ℕ in atTop,
      let P:=((N:ℝ)+1)^(-1/4:ℝ)
      a*P ≤ meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hZero x).re) (-4) ∧
      meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hZero x).re) (-4) ≤ A*P ∧
      a*P ≤ meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hOne x).re) (-4) ∧
      meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(hOne x).re) (-4) ≤ A*P := by
  have h:=mixed_physical_means_asymptotic (u:=4) (by norm_num) le_rfl
  norm_num at h ⊢
  exact h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional
open Matrix MeasureTheory Filter Topology StripAsymptotic

lemma pairingDomain_real_integrable {N : ℕ} {H : ℝ → ℂ}
    (hr : ∀ x,((H x).re:ℂ)=H x) (hH : InPairingDomain N H) (j : Fin (2*N+1)) :
    IntegrableOn (fun p=>(H (p^2)).re*mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) := by
  apply (hH j).re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have he : H=fun x=>((H x).re:ℂ) := by funext x;exact (hr x).symm
  rw [he]
  change (pairingKernel (fun x=>((H x).re:ℂ)) (fun x=>(mixedFamily N j x:ℂ)) p).re=_
  rw [pairingKernel_ofReal _ _ hp.le,Complex.ofReal_re]
  rfl

lemma source_residual_mean {N : ℕ} {H : ℝ → ℂ} {a : ℝ}
    (hr : ∀ x,((H x).re:ℂ)=H x) (hH : InPairingDomain N H) (ha : (H a).re≠0) :
    obliqueResidual N H a=
      (((H a).re*meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) (fun x=>(H x).re) a:ℝ):ℂ) := by
  have he : H=(fun x=>((H x).re:ℂ)) := by funext x;exact (hr x).symm
  conv_lhs => rw [he]
  exact residual_ofReal_mean N _ ha (pairingDomain_real_integrable hr hH)

theorem source_h_residuals_at_minus_four :
    ∃ a A : ℝ,0<a ∧ 0<A ∧ ∀ᶠ N : ℕ in atTop,
      let P:=((N:ℝ)+1)^(-1/4:ℝ)
      a*P ≤ (obliqueResidual N hZero (-4)).re ∧ (obliqueResidual N hZero (-4)).re ≤ A*P ∧
      a*P ≤ (obliqueResidual N hOne (-4)).re ∧ (obliqueResidual N hOne (-4)).re ≤ A*P := by
  obtain ⟨a,A,ha,hA,hB⟩:=mixed_physical_means_at_minus_four
  have h₀ : 0<(hZero (-4)).re := hZero_re_pos le_rfl
  have h₁ : 0<(hOne (-4)).re := hOne_re_pos le_rfl
  refine ⟨min (hZero (-4)).re (hOne (-4)).re*a,
    max (hZero (-4)).re (hOne (-4)).re*A,mul_pos (lt_min h₀ h₁) ha,
      mul_pos (lt_max_of_lt_left h₀) hA,?_⟩
  filter_upwards [hB] with N hN
  rw [source_residual_mean hZero_ofReal_re (hZero_in_pairingDomain N) h₀.ne',
    source_residual_mean hOne_ofReal_re (hOne_in_pairingDomain N) h₁.ne']
  simp only [Complex.ofReal_re]
  dsimp only at hN ⊢
  have hp : 0<((N:ℝ)+1)^(-1/4:ℝ) := by positivity
  have hlo₀:=mul_le_mul_of_nonneg_left hN.1 h₀.le
  have hup₀:=mul_le_mul_of_nonneg_left hN.2.1 h₀.le
  have hlo₁:=mul_le_mul_of_nonneg_left hN.2.2.1 h₁.le
  have hup₁:=mul_le_mul_of_nonneg_left hN.2.2.2 h₁.le
  have haP:=mul_pos ha hp
  have hAP:=mul_pos hA hp
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right (min_le_left (hZero (-4)).re (hOne (-4)).re) haP.le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_left (hZero (-4)).re (hOne (-4)).re) hAP.le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right (min_le_right (hZero (-4)).re (hOne (-4)).re) haP.le]
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_right (hZero (-4)).re (hOne (-4)).re) hAP.le]

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

lemma residual_det_augment {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ)
    (hH : H 0=1) (x : Fin n → ℝ) :
    (-1:ℝ)^n * (evaluationMatrix (residualFamily F H 0) x).det =
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det := by
  let B:=evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)
  let A:=evaluationMatrix (Fin.lastCases H (residualFamily F H 0)) (Fin.cons 0 x)
  let c : Fin (n+1) → ℝ := Fin.lastCases 0 (fun i=> -F i 0)
  have he : A.det=B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c (Fin.last n) (by simp [c])
    intro i j
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [A,B,c,evaluationMatrix]
    · simp only [A,B,c,evaluationMatrix,Fin.lastCases_castSucc,Fin.lastCases_last,
        residualFamily,hH,div_one]
      ring
  rw [Matrix.det_succ_column_zero,Fin.sum_univ_castSucc] at he
  have hz : (∑ i : Fin n,(-1:ℝ)^(i.castSucc.val)*A i.castSucc 0*
      (A.submatrix i.castSucc.succAbove Fin.succ).det)=0 := by
    apply sum_eq_zero
    intro i _
    simp [A,evaluationMatrix,residualFamily,hH]
  rw [hz,zero_add] at he
  have hm : A.submatrix (Fin.last n).succAbove Fin.succ=
      evaluationMatrix (residualFamily F H 0) x := by
    ext i j
    simp [A,Matrix.submatrix,evaluationMatrix,Fin.succAbove_last]
  simpa only [hm,A,B,evaluationMatrix,Fin.lastCases_last,Fin.cons_zero,hH,
    Fin.val_last,mul_one] using he

lemma cThree_real (x : ℝ) : (C (3*angle/2) x).re=cosineKernelJet 0 0 ((3*angle/2)^2) x := by
  rw [C_eq_beta_square,Complex.ofReal_re]

lemma cThree_zero : (C (3*angle/2) 0).re=1 := by simp [C]

lemma extendedKnot_last (N : ℕ) :
    extendedKnotLabels N (2*N+1)=(3*angle/2)^2 := by
  simp [extendedKnotLabels]

lemma extendedKnot_last_order (N : ℕ) : nodalOrder (extendedKnotLabels N) (2*N+1)=0 := by
  unfold nodalOrder
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  simp only [mem_filter,mem_range] at hj
  have h:=interiorKnot_le N j (half_pos strip_angle_pos) (by linarith [strip_angle_pos])
  rw [extendedKnot_before N j hj.1,extendedKnot_last] at hj
  have hpos:=strip_angle_pos
  nlinarith [h]

lemma extended_family (N : ℕ) :
    (fun i : Fin (2*N+2)=>cosineKernelJet (nodalOrder (extendedKnotLabels N) i) 0
      (extendedKnotLabels N i))=Fin.lastCases (fun x=>(C (3*angle/2) x).re) (fixedFamily N) := by
  funext i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simp only [Fin.val_last,Fin.lastCases_last,extendedKnot_last_order,extendedKnot_last]
    funext x
    exact (cThree_real x).symm
  · simp only [Fin.lastCases_castSucc,Fin.val_castSucc,fixedFamily]
    rw [extendedKnot_before N i i.isLt,extendedKnot_order_before N i i.isLt]

lemma cThree_residual_evaluation_neg (N : ℕ) (x : Fin (2*N+1) → ℝ)
    (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    (evaluationMatrix (residualFamily (fixedFamily N) (fun x=>(C (3*angle/2) x).re) 0) x).det<0 := by
  have h:=residual_det_augment (fixedFamily N) (fun x=>(C (3*angle/2) x).re) cThree_zero x
  have hp : 0<(evaluationMatrix (Fin.lastCases (fun x=>(C (3*angle/2) x).re) (fixedFamily N))
      (Fin.cons 0 x)).det := by
    rw [←extended_family]
    apply jetEvaluation_det_pos (extendedKnotLabels N) (Fin.cons 0 x)
    · exact (extendedKnot_monotone N).comp (fun _ _ h=>h)
    · intro i j
      refine Fin.cases ?_ (fun i=>?_) i
      · refine Fin.cases (fun h=>False.elim (lt_irrefl _ h)) (fun j _=>hx0 j) j
      · refine Fin.cases (fun h=>False.elim (Fin.not_lt_zero _ h))
          (fun j h=>hx (Fin.succ_lt_succ_iff.mp h)) j
    · intro i
      exact extendedKnot_nonneg N i
    · exact Fin.cases le_rfl (fun i=>(hx0 i).le)
  have hn : (-1:ℝ)^(2*N+1)= -1 := by simp [pow_add,pow_mul]
  rw [hn] at h
  linarith

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Honeycomb370 Filter Topology Set

lemma evaluation_unitLast_column_det {n : ℕ} (F : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (x : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    ((evaluationMatrix (Fin.lastCases H F) x).updateCol i (Pi.single (Fin.last n) 1)).det =
      (-1:ℝ)^(n+i.val) * (evaluationMatrix F (x ∘ i.succAbove)).det := by
  rw [Matrix.det_succ_column _ i]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp only [Matrix.updateCol_self,Pi.single_eq_same,Fin.val_last,mul_one]
    congr 1
    congr 1
    ext a b
    simp [Matrix.submatrix,evaluationMatrix,Fin.succAbove_last,
      Fin.succAbove_ne]
  · intro j _ hj
    simp [hj]
  · simp

lemma augmented_monomial_det {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    (evaluationMatrix (Fin.lastCases (fun t : ℝ ↦ t^n)
      (fun i : Fin n ↦ fun t : ℝ ↦ t^i.val)) (Fin.cons a x)).det =
      (∏ i,(x i-a)) * (evaluationMatrix (fun i : Fin n ↦ fun t : ℝ ↦ t^i.val) x).det := by
  have he : Fin.lastCases (fun t : ℝ ↦ t^n)
      (fun i : Fin n ↦ fun t : ℝ ↦ t^i.val) = fun i : Fin (n+1) ↦ fun t : ℝ ↦ t^i.val := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  rw [he]
  change (Matrix.vandermonde (Fin.cons a x)).transpose.det =
    _ * (Matrix.vandermonde x).transpose.det
  rw [Matrix.det_transpose,Matrix.det_transpose,vandermonde_cons_det]

/-- Raising one ordered node raises the generalized interpolation error at
an earlier positive point. Both the original and augmented systems have
positive evaluation determinants; no monotonicity conclusion is an input. -/
lemma augmented_ratio_coordinate {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hA : PositiveEvaluation (Fin.lastCases H F))
    (x : Fin n → ℝ) (i : Fin n) (r a : ℝ)
    (ha : 0<a) (hax : ∀ j,a<x j) (hx : StrictMono x)
    (hr : x i ≤ r) (hy : StrictMono (Function.update x i r)) :
    (evaluationMatrix (Fin.lastCases H F) (Fin.cons a x)).det /
        (evaluationMatrix F x).det ≤
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons a (Function.update x i r))).det /
        (evaluationMatrix F (Function.update x i r)).det := by
  rcases hr.eq_or_lt with hr | hr
  · subst r; simp
  have hx0 j : 0<x j := ha.trans (hax j)
  have hy0 j : 0<Function.update x i r j := by
    by_cases hj : j=i
    · subst j; simpa using (hx0 i).trans hr
    · simpa [hj] using hx0 j
  have hmono : StrictMono (Fin.cons a x) := Fin.strictMono_cons.mpr ⟨hax,hx⟩
  have hp : ∀ j : Fin (n+1),0<(Fin.cons a x : Fin (n+1) → ℝ) j := by
    intro j
    exact Fin.cases ha (fun i ↦ hx0 i) j
  let P : Fin n → ℝ → ℝ := fun j t ↦ t^j.val
  let Q : ℝ → ℝ := fun t ↦ t^n
  have hP : PositiveEvaluation P := monomial_positiveEvaluation n
  have hQ : PositiveEvaluation (Fin.lastCases Q P) := by
    have he : Fin.lastCases Q P = fun j : Fin (n+1) ↦ fun t : ℝ ↦ t^j.val := by
      funext j
      refine Fin.lastCases ?_ (fun i ↦ ?_) j <;> simp [Q,P]
    rw [he]
    exact monomial_positiveEvaluation _
  let z : Fin (n+1) → ℝ := Fin.cons a x
  let k := i.succ
  let e : Fin (n+1) → ℝ := Pi.single (Fin.last n) 1
  have hk : (0 : Fin (n+1)) ≠ k := (Fin.succ_ne_zero i).symm
  have hsort : (evaluationMatrix (Fin.lastCases H F) z).det ≠ 0 :=
    (hA z hmono hp).ne'
  have hpsort : (evaluationMatrix (Fin.lastCases Q P) z).det ≠ 0 :=
    (hQ z hmono hp).ne'
  have hd:=determinant_column_diamond (evaluationMatrix (Fin.lastCases H F) z) hsort
    0 k hk e (fun j ↦ Fin.lastCases H F j r)
  have hpd:=determinant_column_diamond (evaluationMatrix (Fin.lastCases Q P) z) hpsort
    0 k hk e (fun j ↦ Fin.lastCases Q P j r)
  have hu (K : Fin (n+1) → ℝ → ℝ) :
      (evaluationMatrix K z).updateCol k (fun j ↦ K j r) =
        evaluationMatrix K (Fin.cons a (Function.update x i r)) := by
    ext j l
    refine Fin.cases ?_ (fun l ↦ ?_) l
    · simp [z,k,hk,evaluationMatrix]
    · by_cases hl : l=i <;> simp [z,k,evaluationMatrix,hl]
  have hv (K : Fin (n+1) → ℝ → ℝ) :
      (evaluationMatrix K z).updateCol 0 (fun j ↦ K j r) =
        evaluationMatrix K (Fin.cons r x) := by
    ext j l
    refine Fin.cases ?_ (fun l ↦ ?_) l <;>
      simp [z,evaluationMatrix]
  have hun (K : Fin n → ℝ → ℝ) (J : ℝ → ℝ) :
      (((evaluationMatrix (Fin.lastCases J K) z).updateCol 0 e).updateCol k
        (fun j ↦ Fin.lastCases J K j r)).det =
          (-1:ℝ)^n*(evaluationMatrix K (Function.update x i r)).det := by
    rw [Matrix.updateCol_comm _ hk,hu,evaluation_unitLast_column_det]
    simp only [Fin.val_zero,add_zero]
    congr 2
  have hzc : Function.Injective (Fin.cons r x) := by
    apply Fin.cons_injective_iff.mpr
    refine ⟨?_,hx.injective⟩
    rintro ⟨j,he⟩
    by_cases hji : j=i
    · subst j; exact hr.ne he
    · have heq : Function.update x i r i = Function.update x i r j := by simp [he,hji]
      exact hji (hy.injective heq).symm
  have hpz : ∀ j : Fin (n+1),0<(Fin.cons r x : Fin (n+1) → ℝ) j := by
    intro j
    exact Fin.cases ((hx0 i).trans hr) (fun l ↦ hx0 l) j
  have hcross₁ := evaluation_det_product_pos (Fin.lastCases H F) (Fin.lastCases Q P)
    hA hQ (Fin.cons r x) hzc hpz
  have hzmin : Function.Injective (z ∘ k.succAbove) := hmono.injective.comp Fin.succAbove_right_injective
  have hcross₂ := evaluation_det_product_pos F P hF hP (z ∘ k.succAbove)
    hzmin (fun j ↦ hp (k.succAbove j))
  have he0 (K : Fin n → ℝ → ℝ) (J : ℝ → ℝ) :
      ((evaluationMatrix (Fin.lastCases J K) z).updateCol 0 e).det =
        (-1:ℝ)^n*(evaluationMatrix K x).det := by
    rw [evaluation_unitLast_column_det]
    simp [z,Function.comp_def]
  rw [he0,hu,hun,hv,evaluation_unitLast_column_det] at hd hpd
  have hs : ((-1:ℝ)^(n+k.val))^2=1 := by rw [←pow_mul,mul_comm (n+k.val) 2,pow_mul]; norm_num
  have hcross : ( (-1:ℝ)^n *
      ((evaluationMatrix F x).det *
        (evaluationMatrix (Fin.lastCases H F) (Fin.cons a (Function.update x i r))).det -
        (evaluationMatrix (Fin.lastCases H F) z).det * (evaluationMatrix F (Function.update x i r)).det)) *
      ((-1:ℝ)^n *
      ((evaluationMatrix P x).det *
        (evaluationMatrix (Fin.lastCases Q P) (Fin.cons a (Function.update x i r))).det -
        (evaluationMatrix (Fin.lastCases Q P) z).det * (evaluationMatrix P (Function.update x i r)).det)) > 0 := by
    have hd' : (-1:ℝ)^n *
        ((evaluationMatrix F x).det *
          (evaluationMatrix (Fin.lastCases H F) (Fin.cons a (Function.update x i r))).det -
          (evaluationMatrix (Fin.lastCases H F) z).det * (evaluationMatrix F (Function.update x i r)).det) =
        (evaluationMatrix (Fin.lastCases H F) (Fin.cons r x)).det *
          ((-1:ℝ)^(n+k.val)*(evaluationMatrix F (z ∘ k.succAbove)).det) := by
      linear_combination hd
    have hpd' : (-1:ℝ)^n *
        ((evaluationMatrix P x).det *
          (evaluationMatrix (Fin.lastCases Q P) (Fin.cons a (Function.update x i r))).det -
          (evaluationMatrix (Fin.lastCases Q P) z).det * (evaluationMatrix P (Function.update x i r)).det) =
        (evaluationMatrix (Fin.lastCases Q P) (Fin.cons r x)).det *
          ((-1:ℝ)^(n+k.val)*(evaluationMatrix P (z ∘ k.succAbove)).det) := by
      linear_combination hpd
    rw [hd',hpd']
    have hmul:=mul_pos hcross₁ hcross₂
    have heq :
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons r x)).det *
        ((-1:ℝ)^(n+k.val)*(evaluationMatrix F (z ∘ k.succAbove)).det) *
      ((evaluationMatrix (Fin.lastCases Q P) (Fin.cons r x)).det *
        ((-1:ℝ)^(n+k.val)*(evaluationMatrix P (z ∘ k.succAbove)).det)) =
      ((-1:ℝ)^(n+k.val))^2 *
        ((evaluationMatrix (Fin.lastCases H F) (Fin.cons r x)).det *
          (evaluationMatrix (Fin.lastCases Q P) (Fin.cons r x)).det) *
        ((evaluationMatrix F (z ∘ k.succAbove)).det * (evaluationMatrix P (z ∘ k.succAbove)).det) := by ring
    rw [heq,hs,one_mul]
    exact hmul
  have hvprod : (∏ j,(x j-a)) ≤ ∏ j,(Function.update x i r j-a) := by
    apply Finset.prod_le_prod₀
    · intro j _; exact sub_nonneg.mpr (hax j).le
    · intro j _
      by_cases hj : j=i
      · subst j; simp; exact hr.le
      · simp [hj]
  have hdiff : 0 ≤ (evaluationMatrix P x).det *
      (evaluationMatrix (Fin.lastCases Q P) (Fin.cons a (Function.update x i r))).det -
      (evaluationMatrix (Fin.lastCases Q P) z).det * (evaluationMatrix P (Function.update x i r)).det := by
    dsimp only [P,Q,z]
    rw [augmented_monomial_det,augmented_monomial_det]
    have hl:=hP x hx hx0
    have hu:=hP _ hy hy0
    nlinarith [mul_nonneg (sub_nonneg.mpr hvprod) (mul_pos hl hu).le]
  have hn : ((-1:ℝ)^n)^2=1 := by rw [←pow_mul,mul_comm n 2,pow_mul]; norm_num
  have hdiffF : (evaluationMatrix (Fin.lastCases H F) z).det *
      (evaluationMatrix F (Function.update x i r)).det ≤
        (evaluationMatrix (Fin.lastCases H F) (Fin.cons a (Function.update x i r))).det *
          (evaluationMatrix F x).det := by
    have hcross' : 0 <
      ((evaluationMatrix F x).det *
        (evaluationMatrix (Fin.lastCases H F) (Fin.cons a (Function.update x i r))).det -
        (evaluationMatrix (Fin.lastCases H F) z).det * (evaluationMatrix F (Function.update x i r)).det) *
      ((evaluationMatrix P x).det *
        (evaluationMatrix (Fin.lastCases Q P) (Fin.cons a (Function.update x i r))).det -
        (evaluationMatrix (Fin.lastCases Q P) z).det * (evaluationMatrix P (Function.update x i r)).det) := by
      convert hcross using 1
      rw [show ∀ b c : ℝ, ((-1:ℝ)^n*b)*((-1:ℝ)^n*c)=((-1:ℝ)^n)^2*(b*c) by intros; ring,hn,one_mul]
    have hh:=pos_of_mul_pos_left hcross' hdiff
    linarith
  exact (div_le_div_iff₀ (hF x hx hx0) (hF _ hy hy0)).mpr hdiffF

lemma augmented_ratio_monotone_pos {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hA : PositiveEvaluation (Fin.lastCases H F))
    {x y : Fin n → ℝ} (hxy : x≤y) (hx : StrictMono x) (hy : StrictMono y)
    (a : ℝ) (ha : 0<a) (hax : ∀ i,a<x i) :
    (evaluationMatrix (Fin.lastCases H F) (Fin.cons a x)).det /
        (evaluationMatrix F x).det ≤
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons a y)).det /
        (evaluationMatrix F y).det := by
  exact monotone_ordered_of_coordinate a _
    (fun z i r hz hzmono hr hupdate ↦
      augmented_ratio_coordinate F H hF hA z i r a ha hz hzmono hr hupdate)
    hxy hax hx hy

lemma augmented_ratio_monotone_zero {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hA : PositiveEvaluation (Fin.lastCases H F))
    (hcF : ∀ i,Continuous (F i)) (hcH : Continuous H)
    {x y : Fin n → ℝ} (hxy : x≤y) (hx0 : ∀ i,0<x i)
    (hx : StrictMono x) (hy : StrictMono y) :
    (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det /
        (evaluationMatrix F x).det ≤
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 y)).det /
        (evaluationMatrix F y).det := by
  have hcA : ∀ i,Continuous (Fin.lastCases H F i) := by
    intro i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa using hcH
    · simpa using hcF i
  have hc (z : Fin n → ℝ) : Continuous (fun a : ℝ ↦
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons a z)).det /
        (evaluationMatrix F z).det) := by
    apply Continuous.div_const
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hcA i).comp (Fin.cases continuous_id (fun _ ↦ continuous_const) j)
  have hlarge : ∀ᶠ a : ℝ in nhds (0:ℝ),∀ i,a<x i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (isOpen_Iio.mem_nhds (hx0 i))
  have hlim₁ := ((hc x).continuousAt (x:=0)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
  have hlim₂ := ((hc y).continuousAt (x:=0)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
  apply le_of_tendsto_of_tendsto hlim₁ hlim₂
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hlarge,
    self_mem_nhdsWithin] with a hax ha
  exact augmented_ratio_monotone_pos F H hF hA hxy hx hy a ha hax

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
