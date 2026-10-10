import Mathlib
import OAI.Probability.SKFluctuations.RootSquareConvex
import OAI.Probability.SKFluctuations.ScalarIntervalPenalty

namespace OAI

/-! Scalar Zero Plateau. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarMinimizer_zero_head_balance_one {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ r ∈ Ico (0:ℝ) 1, α.val r = 0)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    T ≤ 2*(∫ s in 0..T, (scalarTailJet hT α 1).rootFilledSquare T s 0) := by
  have hd := (HeatJet.tendsto_root_mass_quotient (scalarTailJet_admissible hT α 1)
    (scalarTailJet_gradientTest hT α 1) hT.le 0).sub_const (T/4)
  have hdl : 0 ≤ (1/2:ℝ)*(∫ s in 0..T,
      (scalarTailJet hT α 1).rootFilledSquare T s 0)-T/4 := by
    apply ge_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ b : ℝ in 𝓝[>] 0, b < 1 from
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one : (0:ℝ)<1)))] with b hb hb1
    have hb' : 0 < b := hb
    let β := floorMassProfile α hb'.le hb1.le
    have hdiff := scalarParisiValue_zero_head_error hT (show (0:ℝ) < 1 by norm_num)
      (q:=1) (r:=1) le_rfl le_rfl α β hb' hf
      (fun s hs => floorMassProfile_head α hb'.le hb1.le hb'.le hf hs)
      (d:=b) (fun s hs => False.elim (not_lt_of_ge hs.1.le hs.2))
      (fun s hs => False.elim (not_lt_of_ge hs.1.le hs.2))
    simp only [sub_self,mul_zero,mul_one,one_pow] at hdiff
    have hminβ := hmin β (floorMassProfile_mem hα hb'.le hb1.le)
    have hh := (abs_le.mp hdiff).2
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hb').mpr
    nlinarith
  linarith

theorem scalarTailJet_observedSquare_le_one {T q m : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) :
    (scalarTailJet hT α q).observedSquare m (T*q) 0 ≤ 1 := by
  have hh := clockTest_abs_le (scalarTailJet hT α q).lipschitz
    (scalarTailJet hT α q).square.smoothA
    (scalarTailJet_square_bound hT α q) m (T*q) 0
  exact (le_abs_self _).trans hh

 

theorem scalarMinimizer_no_zero_first_gap {T q : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = 0)
    (hrise : ∀ r ∈ Ioc q 1, 0 < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) : False := by
  have hs := scalarProfileRoot_strict_chord (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) (mul_pos hT hq.1)
  change 2*(∫ s in 0..T*q, (scalarTailJet hT α q).rootFilledSquare (T*q) s 0) <
    T*q*(scalarTailJet hT α q).observedSquare 0 (T*q) 0 at hs
  obtain hq1 | hq1 := hq.2.lt_or_eq
  · have hb := scalarMinimizer_zero_head_balance hT ⟨hq.1,hq1⟩ α hα hf hrise hmin
    have hu := scalarMinimizer_zero_endpoint_le hT ⟨hq.1,hq1⟩ α hα hf
      (fun r hr => hrise r ⟨hr.1,hr.2.le⟩) hmin
    nlinarith [mul_le_mul_of_nonneg_left hu (mul_pos hT hq.1).le]
  · subst q
    simp only [mul_one] at hs
    have hb := scalarMinimizer_zero_head_balance_one hT α hα hf hmin
    have hu := scalarTailJet_observedSquare_le_one hT (q:=1) (m:=0) α
    simp only [mul_one] at hu
    nlinarith [mul_le_mul_of_nonneg_left hu hT.le]

theorem scalarMinimizer_no_zero_plateau {T q : ℝ} (hT : 0 < T) (hq : 0 < q)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = 0)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) : False := by
  obtain ⟨p,hp,hfp,hrise⟩ := scalar_first_rise hq α hα (zero_lt_one : (0:ℝ)<1) hf
  exact scalarMinimizer_no_zero_first_gap hT hp α hα hfp hrise hmin

 

theorem scalarMinimizer_mass_pos {T q : ℝ} (hT : 0 < T) (hq : 0 < q)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    0 < α.val q := by
  by_contra hn
  have hz : α.val q = 0 := le_antisymm (le_of_not_gt hn) (α.property.1 q).1
  apply scalarMinimizer_no_zero_plateau hT hq α hα _ hmin
  intro r hr
  apply le_antisymm _ (α.property.1 r).1
  exact (α.property.2 hr.2.le).trans_eq hz

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_origin_accumulates {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β) {q : ℝ} (hq : 0 < q) :
    0 < (profileStieltjes α).measure (Ioo 0 q) := by
  by_contra hn
  have hz : (profileStieltjes α).measure (Ioo 0 q) = 0 := le_zero_iff.mp (le_of_not_gt hn)
  let β := rightMassProfile α
  have hβ : β ∈ scalarProfiles := rightMassProfile_mem hα
  have hf : ∀ r ∈ Ico (0:ℝ) q, β.val r = β.val 0 := by
    intro r hr
    have hi : Ioc (0:ℝ) r ⊆ Ioo 0 q := fun s hs => ⟨hs.1,hs.2.trans_lt hr.2⟩
    have hz' : (profileStieltjes α).measure (Ioc 0 r) = 0 :=
      le_zero_iff.mp ((measure_mono hi).trans_eq hz)
    rw [(profileStieltjes α).measure_Ioc] at hz'
    have hl : β.val r-β.val 0 ≤ 0 := ENNReal.ofReal_eq_zero.mp hz'
    exact le_antisymm (by linarith) (β.property.2 hr.1)
  have hminβ : ∀ γ ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) β ≤
      scalarParisiValue (by linarith : 0 < T) γ := by
    intro γ hγ
    rw [scalarParisiValue_congr_ae (by linarith) (rightMassProfile_ae α)]
    exact hmin γ hγ
  obtain hm | hm := (β.property.1 0).1.eq_or_lt
  · apply scalarMinimizer_no_zero_plateau (by linarith) hq β hβ _ hminβ
    intro r hr
    exact (hf r hr).trans hm.symm
  · exact scalarMinimizer_no_positive_plateau hT hq β hβ hm hf hminβ

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarHeadVariation_integrable {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (m a b : ℝ) :
    IntervalIntegrable (fun s => (m-α.val s)*s*(scalarHeadObservedRatio hT α s m-1))
      volume a b := by
  exact ((intervalIntegrable_const.sub α.property.2.intervalIntegrable).mul_continuousOn
    continuous_id.continuousOn).mul_continuousOn
      (((scalarHeadObservedRatio_continuous hT α).comp
        (continuous_id.prodMk continuous_const)).sub continuous_const).continuousOn

 

theorem scalarMinimizer_head_variation {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hmq : m ≤ α.val q)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    0 ≤ ∫ s in (0:ℝ)..q, (m-α.val s)*s*(scalarHeadObservedRatio hT α s m-1) := by
  have hh := scalarParisiValue_replace_head_general hT hq α hm hm1 hmq hc
  have hn := sub_nonneg.mpr (hmin _ (replaceHeadProfile_mem hα hq.2 hm.le hm1 hmq))
  rw [hh] at hn
  have he : (∫ s in (0:ℝ)..q, (m-α.val s)*
      ((scalarTailJet hT α s).observedSquare m (T*s) 0-s)) =
      ∫ s in (0:ℝ)..q, (m-α.val s)*s*(scalarHeadObservedRatio hT α s m-1) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hq.1.le
    intro s hs
    dsimp only
    rw [scalarHeadObservedRatio_eq hT hs.1 α ⟨hm.le,hm1⟩]
    ring
  rw [he] at hn
  exact (nonneg_of_mul_nonneg_right hn (by positivity : 0 < T/2))

theorem scalarMinimizer_strict_origin {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β) {q : ℝ} (hq : 0 < q) :
    α.val 0 < α.val q := by
  by_contra hn
  have he : α.val q = α.val 0 := le_antisymm (le_of_not_gt hn) (α.property.2 hq.le)
  have hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = α.val 0 := by
    intro s hs
    exact le_antisymm ((α.property.2 hs.2.le).trans_eq he) (α.property.2 hs.1)
  obtain hm | hm := (α.property.1 0).1.eq_or_lt
  · exact scalarMinimizer_no_zero_plateau (by linarith) hq α hα
      (fun s hs => (hf s hs).trans hm.symm) hmin
  · exact scalarMinimizer_no_positive_plateau hT hq α hα hm hf hmin

 

theorem integral_pos_of_initial_pos {f : ℝ → ℝ} {q u : ℝ}
    (hu : 0 < u) (huq : u ≤ q) (hi : IntervalIntegrable f volume 0 q)
    (hn : ∀ s ∈ Ioo (0:ℝ) q, 0 ≤ f s)
    (hp : ∀ s ∈ Ioo (0:ℝ) u, 0 < f s) : 0 < ∫ s in (0:ℝ)..q, f s := by
  have hq := hu.trans_le huq
  have h₀ : 0 ≤ᵐ[volume.restrict (uIoc 0 q)] f := by
    rw [EventuallyLE,uIoc_of_le hq.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs using hn s hs
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' h₀ hi]
  refine ⟨hq,((Measure.measure_Ioo_pos volume).mpr hu).trans_le (measure_mono ?_)⟩
  intro s hs
  exact ⟨Function.mem_support.mpr (hp s hs).ne',hs.1,hs.2.le.trans huq⟩

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem profileStieltjes_support_strict (α : boundedMassProfiles) {p q r : ℝ}
    (hq : q ∈ (profileStieltjes α).measure.support) (hpq : p < q) (hqr : q < r) :
    α.val p < α.val r := by
  let u := (p+q)/2
  let v := (q+r)/2
  have hpu : p < u := by dsimp [u]; linarith
  have huq : u < q := by dsimp [u]; linarith
  have hqv : q < v := by dsimp [v]; linarith
  have hvr : v < r := by dsimp [v]; linarith
  have hp := (Measure.mem_support_iff_forall q).mp hq (Ioo u v) (Ioo_mem_nhds huq hqv)
  have hp' := hp.trans_le (measure_mono (Ioo_subset_Ioc_self : Ioo u v ⊆ Ioc u v))
  rw [(profileStieltjes α).measure_Ioc] at hp'
  have hv : α.val.rightLim u < α.val.rightLim v := by
    have hh := ENNReal.ofReal_pos.mp hp'
    exact sub_pos.mp hh
  exact ((α.property.2.le_rightLim hpu.le).trans_lt hv).trans_le (α.property.2.rightLim_le hvr)

 theorem scalarSupport_local_areas (α : boundedMassProfiles) {p q r : ℝ}
    (hq : q ∈ (profileStieltjes α).measure.support) (hpq : p < q) (hqr : q < r) :
    (0 < ∫ s in p..r, α.val s-α.val p) ∧
      (∫ s in p..r, α.val s-α.val r) < 0 := by
  constructor
  · have hqu : q < (q+r)/2 := by linarith
    have hur : (q+r)/2 < r := by linarith
    exact scalarInterval_down_area_pos α (hpq.trans hqu) hur
      (profileStieltjes_support_strict α hq hpq hqu)
  · have hpu : p < (p+q)/2 := by linarith
    have huq : (p+q)/2 < q := by linarith
    exact scalarInterval_up_area_neg α hpu (huq.trans hqr)
      (profileStieltjes_support_strict α hq huq hqr)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology

 theorem HasDerivAt.ge_of_right_error {f : ℝ → ℝ} {b d K : ℝ}
    (hd : HasDerivAt f d b)
    (hh : ∀ᶠ a in 𝓝[>] b, f b ≤ f a+K*(a-b)) : -K ≤ d := by
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  apply ge_of_tendsto ht
  filter_upwards [hh,self_mem_nhdsWithin] with a ha hab
  rw [slope_def_field]
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology

 theorem HasDerivAt.le_of_left_error {f : ℝ → ℝ} {b d K : ℝ}
    (hd : HasDerivAt f d b)
    (hh : ∀ᶠ a in 𝓝[<] b, f b ≤ f a+K*(b-a)) : d ≤ K := by
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto ht
  filter_upwards [hh,self_mem_nhdsWithin] with a ha hab
  rw [slope_def_field]
  apply (div_le_iff_of_neg (sub_neg.mpr hab)).mpr
  linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.massResponseFamily_gapTest (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) (hA : J.A=J.G 0)
    {b : ℝ} (hb : 0 < b) (D s : ℝ) (α : NonnegativeMassProfile)
    (l : ℝ) (t : ℝ≥0) :
    ((J.massResponseFamily hS hb D).J s).nonnegativeProfileTest α l t=
      (J.profileGapSquareJet hS hb hA D s).nonnegativeProfileTest α l t := by
  apply HeatJet.nonnegativeProfileTest_congr
  · rfl
  · rw [J.massResponseFamily_A hS hb,J.profileGapSquareJet_A]
    funext x
    unfold HeatJet.massEnergy HeatJet.filledSquare
    have he : (J.evolve hb (D-s)).potentialEnergy = fun y => ((J.evolve hb (D-s)).A y)^2 := by
      funext y
      change (∑ i : Fin 1, (J.evolve hb (D-s)).G i y ^ 2)=_
      rw [Fin.sum_univ_one]
      change (clockTest b J.F (J.G 0) (D-s) y)^2=(clockTest b J.F J.A (D-s) y)^2
      rw [hA]
    rw [he]
    rfl

 theorem scalarMassResponse_physical {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    ((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0=
      ∫ s in (0:ℝ)..T*(r-p), scalarPlantedEnergy hT α (p+s/T) := by
  let J := scalarTailJet hT α r
  have hD : 0 ≤ T*(r-p) := mul_nonneg hT.le (sub_nonneg.mpr hpr)
  rw [J.massResponseJet_profileTest (scalarTailJet_G_smooth hT α r) hm _ _
    (fun s => (α.property.1 (s/T)).2)]
  rw [← intervalIntegral.integral_of_le hD]
  apply intervalIntegral.integral_congr_Ioo_of_le hD
  intro s hs
  dsimp only
  rw [J.massResponseFamily_gapTest (scalarTailJet_G_smooth hT α r)
    (scalarTailJet_gradientTest hT α r).1]
  have hps : p < p+s/T := by linarith [div_pos hs.1 hT]
  have hsr : p+s/T < r := by
    have hh : s/T < r-p := (div_lt_iff₀ hT).mpr (by nlinarith [hs.2])
    linarith
  rw [scalarPlantedEnergy_plateau hT hp hps hsr hr α hm hm1 hf]
  congr 3
  field_simp
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarMinimizer_plateau_left_mass_bound {T q p r m : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hqp : q < p) (hpr : p < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hqm : α.val q < m)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (1/2*((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0-T/2*(∫ u in p..r, u)) ≤ T*(p-q) := by
  apply HasDerivAt.le_of_left_error (scalarIntervalMassValue_hasDerivAt hT hpr.le α hm hm1)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ a : ℝ in 𝓝[<] m, α.val q < a from
      (eventually_gt_nhds hqm).filter_mono nhdsWithin_le_nhds)] with a ham hqa
  have ha : 0 < a := (α.property.1 q).1.trans_lt hqa
  let β := clipLowerProfile α r ha.le
  have hβ : β ∈ scalarProfiles := clipLowerProfile_mem hα hr ha.le
  have herror := scalarIntervalMassValue_spillover hT hq hqp.le hpr hr α β ha
    (fun s hs => clipLowerProfile_before α ha.le hqa.le hs.2.le)
    (d:=m-a) (fun s hs => clipLowerProfile_error α ha.le ham.le (by
      have heu := hf ((p+r)/2) ⟨by linarith,by linarith⟩
      rw [← heu]
      exact α.property.2 (by linarith [hs.2])))
    (fun s hs => clipLowerProfile_flat α ha.le ham.le hf hs)
    (fun s hs => clipLowerProfile_after α ha.le hs.1.le)
  have hmin' := hmin β hβ
  rw [scalarIntervalMassValue_plateau hT (hq.trans hqp.le) hpr hr α hm hf]
  have hh := (abs_le.mp herror).2
  nlinarith

 theorem scalarMinimizer_plateau_left_mass_nonpos {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hpr : p < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hs : p ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (1/2*((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0-T/2*(∫ u in p..r, u)) ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (p/2) (ε/(2*T))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδp : δ ≤ p/2 := min_le_left _ _
  have hδε : δ ≤ ε/(2*T) := min_le_right _ _
  have hq : 0 ≤ p-δ := by linarith
  have hqp : p-δ < p := by linarith
  have hqm : α.val (p-δ) < m := by
    rw [← hf ((p+r)/2) ⟨by linarith,by linarith⟩]
    exact profileStieltjes_support_strict α hs hqp (by linarith)
  have hh := scalarMinimizer_plateau_left_mass_bound hT hq hqp hpr hr α hα hm hm1 hqm hf hmin
  have hd : T*δ ≤ ε/2 := by
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*T)).mp hδε
    nlinarith
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarMassResponse_physical_integral {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    ((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0=
      T*(∫ u in p..r, scalarPlantedEnergy hT α u) := by
  rw [scalarMassResponse_physical hT hp hpr hr α hm hm1 hf,
    intervalIntegral.integral_comp_add_div _ hT.ne']
  simp only [zero_div,add_zero,smul_eq_mul]
  congr 2
  field_simp
  ring

 theorem scalarMinimizer_plateau_left_integral_nonpos {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hpr : p < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hs : p ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (∫ u in p..r, scalarPlantedEnergy hT α u-u) ≤ 0 := by
  have hh := scalarMinimizer_plateau_left_mass_nonpos hT hp hpr hr α hα hm hm1 hf hs hmin
  rw [scalarMassResponse_physical_integral hT hp.le hpr.le hr α hm hm1.le hf] at hh
  have hi : IntervalIntegrable (fun u : ℝ => u) volume p r := continuous_id.intervalIntegrable p r
  rw [intervalIntegral.integral_sub ((scalarPlantedEnergy_continuous hT α).intervalIntegrable p r) hi]
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarMinimizer_plateau_right_mass_bound {T p r z m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hrz : r < z) (hz : z ≤ 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hmz : m < α.val z)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    -(T*(z-r)) ≤
    (1/2*((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0-T/2*(∫ u in p..r, u)) := by
  apply HasDerivAt.ge_of_right_error (scalarIntervalMassValue_hasDerivAt hT hpr.le α hm hm1)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ a : ℝ in 𝓝[>] m, a < α.val z from
      (eventually_lt_nhds hmz).filter_mono nhdsWithin_le_nhds)] with a hma haz
  have ha : 0 < a := hm.trans hma
  have ha1 : a ≤ 1 := haz.le.trans (α.property.1 z).2
  let β := clipUpperProfile α p ha1
  have hβ : β ∈ scalarProfiles := clipUpperProfile_mem hα hp ha1
  have herror := scalarIntervalMassValue_tail_spillover hT hp hpr hrz.le hz α β ha
    (fun s hs => clipUpperProfile_before α ha1 hs.2)
    (fun s hs => clipUpperProfile_flat α ha1 hma.le hf hs)
    (d:=a-m) (fun s hs => clipUpperProfile_error α ha1 hma.le (by
      have heu := hf ((p+r)/2) ⟨by linarith,by linarith⟩
      rw [← heu]
      exact α.property.2 (by linarith [hs.1])))
    (fun s hs => clipUpperProfile_after α ha1 haz.le hs.1.le)
  have hmin' := hmin β hβ
  rw [scalarIntervalMassValue_plateau hT hp hpr (hrz.le.trans hz) α hm hf]
  have hh := (abs_le.mp herror).2
  nlinarith

 theorem scalarMinimizer_plateau_right_mass_nonneg {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r < 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hs : r ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    0 ≤ (1/2*((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0-T/2*(∫ u in p..r, u)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min ((1-r)/2) (ε/(2*T))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ ≤ (1-r)/2 := min_le_left _ _
  have hδε : δ ≤ ε/(2*T) := min_le_right _ _
  have hz : r+δ ≤ 1 := by linarith
  have hrz : r < r+δ := by linarith
  have hmz : m < α.val (r+δ) := by
    rw [← hf ((p+r)/2) ⟨by linarith,by linarith⟩]
    exact profileStieltjes_support_strict α hs (by linarith) hrz
  have hh := scalarMinimizer_plateau_right_mass_bound hT hp hpr hrz hz α hα hm hm1 hmz hf hmin
  have hd : T*δ ≤ ε/2 := by
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*T)).mp hδε
    nlinarith
  nlinarith

 theorem scalarMinimizer_plateau_right_integral_nonneg {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r < 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hs : r ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    0 ≤ ∫ u in p..r, scalarPlantedEnergy hT α u-u := by
  have hh := scalarMinimizer_plateau_right_mass_nonneg hT hp hpr hr α hα hm hm1 hf hs hmin
  rw [scalarMassResponse_physical_integral hT hp hpr.le hr.le α hm hm1.le hf] at hh
  have hi : IntervalIntegrable (fun u : ℝ => u) volume p r := continuous_id.intervalIntegrable p r
  rw [intervalIntegral.integral_sub ((scalarPlantedEnergy_continuous hT α).intervalIntegrable p r) hi]
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.clockTestDerivative_unit_bound {n : ℕ} (J : HeatJet n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m ∈ Icc (0:ℝ) 1, ∀ t x,
      |clockTestDerivative m J.F J.G J.H J.A J.A₁ J.A₂ t x| ≤ B := by
  let m : ℝ × (Fin (n+1) → ℝ) → ℝ := fun p => unitMassClip p.1
  have hm : AbsBounded m := ⟨1,zero_le_one,fun p => by
    rw [abs_of_nonneg (unitMassClip_bounds p.1).1]; exact (unitMassClip_bounds p.1).2⟩
  have hA := AbsBounded.comp J.smoothA.bound (Prod.snd : ℝ × (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
  have hG (i) := AbsBounded.comp (J.smoothG i).bound (Prod.snd : ℝ × (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
  have hH (i) := AbsBounded.comp (J.smoothH i).bound (Prod.snd : ℝ × (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
  have hA₁ (i) := AbsBounded.comp (J.smoothA₁ i).bound (Prod.snd : ℝ × (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
  have hA₂ (i) := AbsBounded.comp (J.smoothA₂ i).bound (Prod.snd : ℝ × (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
  have hp : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => potentialHeatTrace (m p) J.G J.H p.2) := by
    apply AbsBounded.sum
    intro i
    simpa only [pow_two] using (hm.mul (hH i)).add ((hm.mul hm).mul ((hG i).mul (hG i)))
  have hw : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => testedHeatTrace (m p) J.G J.H J.A J.A₁ J.A₂ p.2) := by
    apply AbsBounded.sum
    intro i
    simpa only [pow_two] using ((hA₂ i).add (((hm.const_mul 2).mul (hA₁ i)).mul (hG i))).add
      (hA.mul ((hm.mul (hH i)).add ((hm.mul hm).mul ((hG i).mul (hG i)))))
  obtain ⟨A,hA0,ha⟩ := J.smoothA.bound
  obtain ⟨P,hP0,hp⟩ := hp
  obtain ⟨W,hW0,hw⟩ := hw
  refine ⟨(W+A*P)/2,by positivity,fun a ha' t x => ?_⟩
  have hp' (y) : |potentialHeatTrace a J.G J.H y| ≤ P := by
    simpa only [m,unitMassClip_eq ha'] using hp (a,y)
  have hw' (y) : |testedHeatTrace a J.G J.H J.A J.A₁ J.A₂ y| ≤ W := by
    simpa only [m,unitMassClip_eq ha'] using hw (a,y)
  have hbP := clockTest_abs_le J.lipschitz (potentialHeatTrace_bddSmooth J.smoothG J.smoothH a) hp' a t x
  have hbW := clockTest_abs_le J.lipschitz
    (testedHeatTrace_bddSmooth J.smoothG J.smoothH J.smoothA J.smoothA₁ J.smoothA₂ a) hw' a t x
  have hbA := clockTest_abs_le J.lipschitz J.smoothA ha a t x
  unfold clockTestDerivative
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := abs_sub (clockTest a J.F (testedHeatTrace a J.G J.H J.A J.A₁ J.A₂) t x)
    (clockTest a J.F J.A t x*clockTest a J.F (potentialHeatTrace a J.G J.H) t x)
  rw [abs_mul] at hh
  have hh' := mul_le_mul hbA hbP (abs_nonneg _) hA0
  linarith

 theorem HeatJet.clockDerivative_unit_bound {n : ℕ} (J : HeatJet n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m ∈ Icc (0:ℝ) 1, ∀ t x,
      |clockDerivative m J.F J.G J.H t x| ≤ B := by
  choose G hG0 hG using fun i => (J.smoothG i).bound
  choose H hH0 hH using fun i => (J.smoothH i).bound
  refine ⟨(∑ i, (H i+G i^2))/2, div_nonneg (Finset.sum_nonneg (fun i _ => add_nonneg (hH0 i) (sq_nonneg _))) (by norm_num),fun m hm t x => ?_⟩
  have hbH (i) := clockTest_abs_le J.lipschitz (J.smoothH i) (hH i) m t x
  have hbG (i) := clockTest_abs_le J.lipschitz ((J.smoothG i).mul (J.smoothG i))
    (fun y => by simpa only [← pow_two,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hG i y) 2) m t x
  unfold clockDerivative
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hsH : |∑ i, clockTest m J.F (J.H i) t x| ≤ ∑ i, H i := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hbH i))
  have hsG : |∑ i, clockTest m J.F (fun y => J.G i y*J.G i y) t x| ≤ ∑ i, G i^2 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hbG i))
  have hh := abs_add_le (∑ i, clockTest m J.F (J.H i) t x)
    (m*∑ i, clockTest m J.F (fun y => (J.G i y)^2) t x)
  rw [abs_mul,abs_of_nonneg hm.1] at hh
  have hh' := mul_le_mul hm.2 (by simpa only [← pow_two] using hsG) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  simp only [one_mul] at hh'
  rw [Finset.sum_add_distrib]
  linarith

 theorem HeatJet.clockTest_unit_time_bound {n : ℕ} (J : HeatJet n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ∈ Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → ∀ x,
      |clockTest m J.F J.A t x-J.A x| ≤ C*t := by
  obtain ⟨C,hC,hb⟩ := J.clockTestDerivative_unit_bound
  refine ⟨C,hC,fun m hm t ht x => ?_⟩
  have hc : ContinuousOn (fun t : ℝ => clockTest m J.F J.A t x) (Ici 0) :=
    ((clockTest_continuous J.lipschitz J.smoothA m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  have hd (r : ℝ) (hr : 0 < r) := (hasDerivWithinAt_clockTest J.lipschitz J.smoothA
    J.smoothG J.smoothH J.smoothA₁ J.smoothA₂ J.derivF J.derivG J.derivA J.derivA₁
    m x hr.le).hasDerivAt (Ici_mem_nhds hr)
  have hh := abs_sub_le_mul_of_deriv_interior hc hd (fun r _ => hb m hm r x) ht (le_refl (0:ℝ))
  simpa only [clockTest_zero,zero_sub,abs_neg,abs_of_nonneg ht,abs_sub_comm] using hh

 theorem HeatJet.clockValue_unit_time_bound {n : ℕ} (J : HeatJet n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℝ, 0 < m → m ≤ 1 → ∀ t : ℝ, 0 ≤ t → ∀ x,
      |clockContinuation m J.F t x-J.F x| ≤ C*t := by
  obtain ⟨C,hC,hb⟩ := J.clockDerivative_unit_bound
  refine ⟨C,hC,fun m hm hm1 t ht x => ?_⟩
  have hc : ContinuousOn (fun t : ℝ => clockContinuation m J.F t x) (Ici 0) :=
    ((clockContinuation_continuous J.lipschitz m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  have hd (r : ℝ) (hr : 0 < r) := hasDerivAt_clockContinuation J.lipschitz J.smoothG
    J.smoothH J.derivF J.derivG hm hr x
  have hh := abs_sub_le_mul_of_deriv_interior hc hd (fun r _ => hb m ⟨hm.le,hm1⟩ r x) ht (le_refl (0:ℝ))
  simpa only [clockContinuation_zero hm.ne',zero_sub,abs_neg,abs_of_nonneg ht,abs_sub_comm] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.evolve_varying_mass_terminal_tendsto {n : ℕ} (J : ℕ → HeatJet n) (L : HeatJet n)
    (hF : TendstoUniformly (fun k => (J k).F) L.F atTop)
    (hA : TendstoUniformly (fun k => (J k).A) L.A atTop)
    (m : ℕ → ℝ) (hm : ∀ k, 0 < m k) (hm1 : ∀ k, m k ≤ 1) (t : ℕ → ℝ)
    (ht : ∀ k, 0 ≤ t k) (ht0 : Tendsto t atTop (𝓝 0)) :
    TendstoUniformly (fun k => ((J k).evolve (hm k) (t k)).F) L.F atTop ∧
      TendstoUniformly (fun k => ((J k).evolve (hm k) (t k)).A) L.A atTop := by
  obtain ⟨C,hC,hCv⟩ := L.clockValue_unit_time_bound
  obtain ⟨B,hB,hBt⟩ := L.clockTest_unit_time_bound
  obtain ⟨K,hK,hKA⟩ := L.smoothA.bound
  have hc : Tendsto (fun k => C*t k) atTop (𝓝 0) := by simpa only [mul_zero] using ht0.const_mul C
  have hb : Tendsto (fun k => B*t k) atTop (𝓝 0) := by simpa only [mul_zero] using ht0.const_mul B
  constructor
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hF (ε/2) (by positivity),
      hc.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with k hk he x
    have hf (y) : |(J k).F y-L.F y| ≤ ε/2 := by simpa only [Real.dist_eq,abs_sub_comm] using (hk y).le
    have hh := clockContinuation_abs_sub_le (J k).lipschitz L.lipschitz (hm k) hf (t k) x
    rw [Real.dist_eq,abs_sub_comm]
    exact (abs_sub_le _ (clockContinuation (m k) L.F (t k) x) _).trans_lt
      ((add_le_add hh (hCv _ (hm k) (hm1 k) _ (ht k) x)).trans_lt (by linarith))
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    let δ := ε/(2*(1+4*(K+1)))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    filter_upwards [Metric.tendstoUniformly_iff.mp hF δ hδ,
      Metric.tendstoUniformly_iff.mp hA δ hδ,
      hb.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with k hkF hkA he x
    have hf (y) : |(J k).F y-L.F y| ≤ δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hkF y).le
    have ha (y) : |(J k).A y-L.A y| ≤ δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hkA y).le
    have hh := L.clockTest_terminal_stability (J k) (hm k) (hm1 k) hδ.le hf (by linarith : 0 < K+1)
      (fun y => (hKA y).trans (by linarith)) ha (t k) x
    have hd : δ+4*δ*(K+1)=ε/2 := by dsimp [δ]; field_simp
    rw [hd] at hh
    rw [Real.dist_eq,abs_sub_comm]
    exact (abs_sub_le _ (clockTest (m k) L.F L.A (t k) x) _).trans_lt
      ((add_le_add hh (hBt _ ⟨(hm k).le,hm1 k⟩ _ (ht k) x)).trans_lt (by linarith))

end SKFluctuations.Hierarchy

end

end OAI
