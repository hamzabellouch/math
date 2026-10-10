import Mathlib
import OAI.Probability.SKFluctuations.ScalarJetPowerTests

namespace OAI

/-! Scalar Interval Penalty. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarPenalty_replace_interval {p r m : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hpm : α.val p ≤ m) (hmr : m ≤ α.val r) :
    scalarPenalty α-scalarPenalty (replaceIntervalProfile α hm0 hm1 hpm hmr) =
      ∫ s in p..r, s*(α.val s-m) := by
  let β := replaceIntervalProfile α hm0 hm1 hpm hmr
  let f := fun s => weightedProfile α s-weightedProfile β s
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    (weightedProfile_monotone α).intervalIntegrable.sub (weightedProfile_monotone β).intervalIntegrable
  have hz : (∫ s in (0:ℝ)..p, f s) = 0 := by
    trans ∫ _s in (0:ℝ)..p, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hp
      intro s hs
      dsimp only [f,weightedProfile]
      rw [replaceIntervalProfile_before α hm0 hm1 hpm hmr hs.2,sub_self]
    · simp
  have ht : (∫ s in r..1, f s) = 0 := by
    trans ∫ _s in r..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hr
      intro s hs
      dsimp only [f,weightedProfile]
      rw [replaceIntervalProfile_after α hm0 hm1 hpm hmr hs.1.le,sub_self]
    · simp
  unfold scalarPenalty
  rw [← intervalIntegral.integral_sub (weightedProfile_monotone α).intervalIntegrable
    (weightedProfile_monotone β).intervalIntegrable]
  change (∫ s in (0:ℝ)..1, f s) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 p) (hfi p 1),hz,zero_add,
    ← intervalIntegral.integral_add_adjacent_intervals (hfi p r) (hfi r 1),ht,add_zero]
  apply intervalIntegral.integral_congr_Ioo_of_le hpr
  intro s hs
  dsimp only [f,weightedProfile]
  rw [replaceIntervalProfile_inside α hm0 hm1 hpm hmr ⟨hs.1.le,hs.2⟩,
    max_eq_left (hp.trans hs.1.le)]
  ring

 theorem scalarPenalty_interval_upper {p r m c : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hpm : α.val p ≤ m) (hmr : m ≤ α.val r)
    (h : ∀ s ∈ Ioo p r, s*(α.val s-m) ≤ c*(α.val s-m)) :
    scalarPenalty α-scalarPenalty (replaceIntervalProfile α hm0 hm1 hpm hmr) ≤
      c*(∫ s in p..r, α.val s-m) := by
  rw [scalarPenalty_replace_interval hp hpr hr,← intervalIntegral.integral_const_mul]
  have hi : IntervalIntegrable (fun s => α.val s-m) volume p r :=
    α.property.2.intervalIntegrable.sub intervalIntegrable_const
  exact intervalIntegral.integral_mono_on_of_le_Ioo hpr
    (hi.continuousOn_mul continuous_id.continuousOn) (hi.const_mul c) h

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def scalarIntervalMassValue {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (p r a : ℝ) : ℝ :=
  (scalarTailJet hT α r).massClockProfileValue (T*(r-p)) (rescaledMassProfile α hT)
    0 (Real.toNNReal (T*p)) 0 a-
    T/2*(scalarPenalty α-∫ u in p..r, u*(α.val u-a))-T/4

 theorem scalarIntervalMassValue_eq {T p r a : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (ha : 0 < a) (ha1 : a ≤ 1) (hpa : α.val p ≤ a) (har : a ≤ α.val r) :
    scalarIntervalMassValue hT α p r a =
      scalarParisiValue hT (replaceIntervalProfile α ha.le ha1 hpa har) := by
  let β := replaceIntervalProfile α ha.le ha1 hpa har
  rw [scalarParisiValue_prefix hT ⟨hp,hpr.le.trans hr⟩ β]
  have he := scalarPrefix_congr (scalarTailJet hT β p) hT hp
    (α:=β) (β:=α) (fun s hs => replaceIntervalProfile_before α ha.le ha1 hpa har hs.2) 0
  rw [he]
  have hf := HeatJet.nonnegativeProfileValue_congr_potential (scalarTailJet hT β p)
    ((scalarTailJet hT α r).evolve ha (T*(r-p)))
    (scalarTailJet_interval_flat hT hpr hr α ha ha1 hpa har)
    (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p))
  rw [hf]
  have hpen := scalarPenalty_replace_interval hp hpr.le hr α ha.le ha1 hpa har
  change scalarPenalty α-scalarPenalty β=_ at hpen
  simp only [scalarIntervalMassValue,HeatJet.massClockProfileValue,dite_eq_left ha]
  rw [← hpen]
  ring

 theorem scalarIntervalMassValue_hasDerivAt {T p r b : ℝ} (hT : 0 < T)
    (hpr : p ≤ r) (α : boundedMassProfiles) (hb : 0 < b) (hb1 : b < 1) :
    HasDerivAt (scalarIntervalMassValue hT α p r)
      (1/2*((scalarTailJet hT α r).massResponseJet (scalarTailJet_G_smooth hT α r)
        hb (T*(r-p))).nonnegativeProfileTest (rescaledMassProfile α hT)
          0 (Real.toNNReal (T*p)) 0 -T/2*(∫ u in p..r, u)) b := by
  have hd := (scalarTailJet hT α r).hasDerivAt_massClockProfileValue
    (scalarTailJet_G_smooth hT α r) (scalarTailJet_G_bound hT α r 0)
    hb hb1 (mul_nonneg hT.le (sub_nonneg.mpr hpr))
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
    0 (Real.toNNReal (T*p)) 0
  have hi : IntervalIntegrable (fun u => u*α.val u) volume p r :=
    α.property.2.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  have he (a : ℝ) : (∫ u in p..r, u*(α.val u-a)) =
      (∫ u in p..r, u*α.val u)-a*(∫ u in p..r, u) := by
    simp only [mul_sub]
    have hia : IntervalIntegrable (fun u : ℝ => u*a) volume p r :=
      (continuous_id.mul_const a).intervalIntegrable p r
    rw [intervalIntegral.integral_sub hi hia, intervalIntegral.integral_mul_const]
    ring
  have hpen : HasDerivAt (fun a : ℝ => T/2*(scalarPenalty α-(∫ u in p..r, u*(α.val u-a))))
      (T/2*(∫ u in p..r, u)) b := by
    simp only [he]
    convert (((hasDerivAt_const b (∫ u in p..r, u*α.val u)).sub
      ((hasDerivAt_id b).mul_const (∫ u in p..r, u))).const_sub (scalarPenalty α)).const_mul (T/2) using 1 <;>
      first | rfl | ring
  exact (hd.sub hpen).sub_const (T/4)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarIntervalMassValue_spillover {T q p r a d : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpr : p < r) (hr : r ≤ 1)
    (α β : boundedMassProfiles) (ha : 0 < a)
    (hz : ∀ s ∈ Ioo (0:ℝ) q, β.val s=α.val s)
    (hb : ∀ s ∈ Ioo q p, |β.val s-α.val s| ≤ d)
    (hf : ∀ s ∈ Ioo p r, β.val s=a)
    (he : ∀ s ∈ Ioo r 1, β.val s=α.val s) :
    |scalarParisiValue hT β-scalarIntervalMassValue hT α p r a| ≤ T*d*(p-q) := by
  let J := (scalarTailJet hT α r).evolve ha (T*(r-p))
  have ht : (scalarTailJet hT β p).F=J.F := by
    rw [scalarTailJet_plateau_evolve hT hpr hr β ha hf]
    change clockContinuation a (scalarTailJet hT β r).F (T*(r-p))=
      clockContinuation a (scalarTailJet hT α r).F (T*(r-p))
    have heF : (scalarTailJet hT β r).F=(scalarTailJet hT α r).F := by
      funext x
      have hh := scalarTailJet_error hT (le_refl r) hr α β (d:=0)
        (fun s hs => by linarith [hs.1,hs.2]) he x
      simpa only [sub_self,mul_zero,abs_nonpos_iff,sub_eq_zero] using hh
    rw [heF]
  have hgrad : ∀ i x, |J.G i x| ≤ 1 := by
    intro i x
    exact clockTest_abs_le (scalarTailJet hT α r).lipschitz
      ((scalarTailJet hT α r).smoothG i) (scalarTailJet_G_bound hT α r i) a (T*(r-p)) x
  have hv := scalarPrefix_error J hgrad hT hq hqp α β hz hb (0:Fin 1 → ℝ)
  have hp := scalarPenalty_prefix_error hq hqp hpr.le hr α β hz hb hf he
  rw [scalarParisiValue_prefix hT ⟨hq.trans hqp,hpr.le.trans hr⟩ β,
    HeatJet.nonnegativeProfileValue_congr_potential (scalarTailJet hT β p) J ht]
  simp only [scalarIntervalMassValue,HeatJet.massClockProfileValue,dite_eq_left ha]
  change |(J.nonnegativeProfileValue (rescaledMassProfile β hT) 0
      (Real.toNNReal (T*p)) 0-T/2*scalarPenalty β-T/4)-
    (J.nonnegativeProfileValue (rescaledMassProfile α hT) 0
      (Real.toNNReal (T*p)) 0-T/2*(scalarPenalty α-∫ u in p..r, u*(α.val u-a))-T/4)| ≤ _
  rw [show (J.nonnegativeProfileValue (rescaledMassProfile β hT) 0
      (Real.toNNReal (T*p)) 0-T/2*scalarPenalty β-T/4)-
    (J.nonnegativeProfileValue (rescaledMassProfile α hT) 0
      (Real.toNNReal (T*p)) 0-T/2*(scalarPenalty α-∫ u in p..r, u*(α.val u-a))-T/4)=
    (J.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) 0-
      J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0)-
      T/2*(scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a))) by ring]
  calc
    |_ - _| ≤ |J.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) 0-
      J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0|+
      |T/2*(scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a)))| := abs_sub _ _
    _ ≤ T/2*d*(p-q)+T/2*(d*(p-q)) := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ T/2)]
      exact add_le_add hv (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by ring

 theorem scalarIntervalMassValue_plateau {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    scalarIntervalMassValue hT α p r m=scalarParisiValue hT α := by
  have hh := scalarIntervalMassValue_spillover hT hp (le_refl p) hpr hr α α hm
    (fun _ _ => rfl) (d:=0) (fun s _ => by simp) hf (fun _ _ => rfl)
  simp only [sub_self,mul_zero] at hh
  exact (sub_eq_zero.mp (abs_nonpos_iff.mp hh)).symm

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarPenalty_interval_tail_error {p r z a d : ℝ} (hp : 0 ≤ p)
    (hpr : p ≤ r) (hrz : r ≤ z) (hz : z ≤ 1) (α β : boundedMassProfiles)
    (hpre : ∀ s ∈ Ioo (0:ℝ) p, β.val s=α.val s)
    (hf : ∀ s ∈ Ioo p r, β.val s=a)
    (hb : ∀ s ∈ Ioo r z, |β.val s-α.val s| ≤ d)
    (he : ∀ s ∈ Ioo z 1, β.val s=α.val s) :
    |scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a))| ≤ d*(z-r) := by
  let f := fun s => weightedProfile β s-weightedProfile α s
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    (weightedProfile_monotone β).intervalIntegrable.sub (weightedProfile_monotone α).intervalIntegrable
  have hzero : (∫ s in (0:ℝ)..p, f s)=0 := by
    trans ∫ _s in (0:ℝ)..p, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hp
      intro s hs
      dsimp only [f,weightedProfile]
      rw [hpre s hs,sub_self]
    · simp
  have hlast : (∫ s in z..1, f s)=0 := by
    trans ∫ _s in z..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hz
      intro s hs
      dsimp only [f,weightedProfile]
      rw [he s hs,sub_self]
    · simp
  have hflat : (∫ s in p..r, f s)= -(∫ s in p..r, s*(α.val s-a)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le hpr
    intro s hs
    dsimp only [f,weightedProfile]
    rw [hf s hs,max_eq_left (hp.trans hs.1.le)]
    ring
  have hmid : |∫ s in r..z, f s| ≤ d*(z-r) := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) hrz (hfi _ _).abs
      (intervalIntegrable_const (c:=d)) (by
        intro s hs
        change |max s 0*β.val s-max s 0*α.val s| ≤ d
        have hs0 : 0 ≤ s := hp.trans (hpr.trans hs.1.le)
        rw [← mul_sub,max_eq_left hs0,abs_mul,abs_of_nonneg hs0]
        have hd : 0 ≤ d := (abs_nonneg _).trans (hb s hs)
        calc
          s*|β.val s-α.val s| ≤ s*d := mul_le_mul_of_nonneg_left (hb s hs) hs0
          _ ≤ d := by nlinarith [hs.2.le.trans hz])
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hh
    exact (intervalIntegral.abs_integral_le_integral_abs hrz).trans (by nlinarith)
  have heq : scalarPenalty β-scalarPenalty α=
      -(∫ s in p..r, s*(α.val s-a))+(∫ s in r..z, f s) := by
    unfold scalarPenalty
    rw [← intervalIntegral.integral_sub (weightedProfile_monotone β).intervalIntegrable
      (weightedProfile_monotone α).intervalIntegrable]
    change (∫ s in (0:ℝ)..1, f s)=_
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 p) (hfi p 1),hzero,zero_add,
      ← intervalIntegral.integral_add_adjacent_intervals (hfi p r) (hfi r 1),hflat,
      ← intervalIntegral.integral_add_adjacent_intervals (hfi r z) (hfi z 1),hlast,add_zero]
  have hh : scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a))=
      ∫ s in r..z, f s := by linarith
  rw [hh]
  exact hmid

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarIntervalMassValue_tail_spillover {T p r z a d : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hrz : r ≤ z) (hz : z ≤ 1)
    (α β : boundedMassProfiles) (ha : 0 < a)
    (hpre : ∀ s ∈ Ioo (0:ℝ) p, β.val s=α.val s)
    (hf : ∀ s ∈ Ioo p r, β.val s=a)
    (hb : ∀ s ∈ Ioo r z, |β.val s-α.val s| ≤ d)
    (he : ∀ s ∈ Ioo z 1, β.val s=α.val s) :
    |scalarParisiValue hT β-scalarIntervalMassValue hT α p r a| ≤ T*d*(z-r) := by
  let J := (scalarTailJet hT α r).evolve ha (T*(r-p))
  let K := scalarTailJet hT β p
  have ht : ∀ y, |K.F y-J.F y| ≤ T/2*d*(z-r) := by
    intro y
    have hh := clockContinuation_abs_sub_le (scalarTailJet hT β r).lipschitz
      (scalarTailJet hT α r).lipschitz ha (scalarTailJet_error hT hrz hz α β hb he) (T*(r-p)) y
    dsimp only [K,J]
    rw [scalarTailJet_plateau_evolve hT hpr (hrz.trans hz) β ha hf]
    exact hh
  have hv := K.nonnegativeProfile_nonexpansive J ht (rescaledMassProfile α hT)
    0 (Real.toNNReal (T*p)) (0:Fin 1 → ℝ)
  have hpen := scalarPenalty_interval_tail_error hp hpr.le hrz hz α β hpre hf hb he
  rw [scalarParisiValue_prefix hT ⟨hp,hpr.le.trans (hrz.trans hz)⟩ β,
    scalarPrefix_congr K hT hp hpre]
  simp only [scalarIntervalMassValue,HeatJet.massClockProfileValue,dite_eq_left ha]
  change |(K.nonnegativeProfileValue (rescaledMassProfile α hT) 0
      (Real.toNNReal (T*p)) 0-T/2*scalarPenalty β-T/4)-
    (J.nonnegativeProfileValue (rescaledMassProfile α hT) 0
      (Real.toNNReal (T*p)) 0-T/2*(scalarPenalty α-∫ u in p..r, u*(α.val u-a))-T/4)| ≤ _
  rw [show (K.nonnegativeProfileValue (rescaledMassProfile α hT) 0
      (Real.toNNReal (T*p)) 0-T/2*scalarPenalty β-T/4)-
    (J.nonnegativeProfileValue (rescaledMassProfile α hT) 0
      (Real.toNNReal (T*p)) 0-T/2*(scalarPenalty α-∫ u in p..r, u*(α.val u-a))-T/4)=
    (K.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0-
      J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0)-
      T/2*(scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a))) by ring]
  calc
    |_ - _| ≤ |K.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0-
      J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0|+
      |T/2*(scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a)))| := abs_sub _ _
    _ ≤ T/2*d*(z-r)+T/2*(d*(z-r)) := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ T/2)]
      exact add_le_add hv (mul_le_mul_of_nonneg_left hpen (by positivity))
    _ = _ := by ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def clipLowerProfile (α : boundedMassProfiles) (r : ℝ)
    {a : ℝ} (ha : 0 ≤ a) : boundedMassProfiles :=
  ⟨fun s => if s < r then min (α.val s) a else α.val s, by
    constructor
    · intro s
      dsimp only
      split_ifs
      · exact ⟨le_min (α.property.1 s).1 ha,(min_le_left _ _).trans (α.property.1 s).2⟩
      · exact α.property.1 s
    · intro s t hst
      dsimp only
      by_cases ht : t < r
      · rw [ite_eq_left ht,ite_eq_left (hst.trans_lt ht)]
        exact min_le_min_right _ (α.property.2 hst)
      · rw [ite_eq_right ht]
        split_ifs
        · exact (min_le_left _ _).trans (α.property.2 hst)
        · exact α.property.2 hst⟩

 theorem clipLowerProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {r a : ℝ} (hr : r ≤ 1) (ha : 0 ≤ a) : clipLowerProfile α r ha ∈ scalarProfiles := by
  constructor
  · intro s hs
    change (if s < r then min (α.val s) a else α.val s)=0
    rw [hα.1 s hs]
    simp [min_eq_left ha]
  · intro s hs
    change (if s < r then min (α.val s) a else α.val s)=1
    rw [ite_eq_right (not_lt.mpr (hr.trans hs.le)),hα.2 s hs]

 theorem clipLowerProfile_before (α : boundedMassProfiles) {p r a s : ℝ}
    (ha : 0 ≤ a) (hpa : α.val p ≤ a) (hs : s ≤ p) :
    (clipLowerProfile α r ha).val s=α.val s := by
  change (if s < r then min (α.val s) a else α.val s)=α.val s
  simp only [min_eq_left ((α.property.2 hs).trans hpa),ite_self]

 theorem clipLowerProfile_after (α : boundedMassProfiles) {r a s : ℝ}
    (ha : 0 ≤ a) (hs : r ≤ s) : (clipLowerProfile α r ha).val s=α.val s := by
  exact ite_eq_right (not_lt.mpr hs)

 theorem clipLowerProfile_flat (α : boundedMassProfiles) {p r m a s : ℝ}
    (ha : 0 ≤ a) (ham : a ≤ m) (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hs : s ∈ Ioo p r) : (clipLowerProfile α r ha).val s=a := by
  change (if s < r then min (α.val s) a else α.val s)=a
  rw [ite_eq_left hs.2,hf s hs,min_eq_right ham]

 theorem clipLowerProfile_error (α : boundedMassProfiles) {r m a s : ℝ}
    (ha : 0 ≤ a) (ham : a ≤ m) (hsm : α.val s ≤ m) :
    |(clipLowerProfile α r ha).val s-α.val s| ≤ m-a := by
  change |(if s < r then min (α.val s) a else α.val s)-α.val s| ≤ m-a
  split_ifs
  · by_cases hs : α.val s ≤ a
    · rw [min_eq_left hs,sub_self,abs_zero]; linarith
    · rw [min_eq_right (le_of_not_ge hs),abs_of_nonpos (by linarith)]
      linarith
  · rw [sub_self,abs_zero]; linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def clipUpperProfile (α : boundedMassProfiles) (p : ℝ)
    {a : ℝ} (ha : a ≤ 1) : boundedMassProfiles :=
  ⟨fun s => if s < p then α.val s else max (α.val s) a, by
    constructor
    · intro s
      dsimp only
      split_ifs
      · exact α.property.1 s
      · exact ⟨(α.property.1 s).1.trans (le_max_left _ _),max_le (α.property.1 s).2 ha⟩
    · intro s t hst
      dsimp only
      by_cases hs : s < p
      · rw [ite_eq_left hs]
        split_ifs
        · exact α.property.2 hst
        · exact (α.property.2 hst).trans (le_max_left _ _)
      · rw [ite_eq_right hs,ite_eq_right (not_lt.mpr ((le_of_not_gt hs).trans hst))]
        exact max_le_max_right _ (α.property.2 hst)⟩

 theorem clipUpperProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {p a : ℝ} (hp : 0 ≤ p) (ha : a ≤ 1) : clipUpperProfile α p ha ∈ scalarProfiles := by
  constructor
  · intro s hs
    change (if s < p then α.val s else max (α.val s) a)=0
    rw [ite_eq_left (hs.trans_le hp),hα.1 s hs]
  · intro s hs
    change (if s < p then α.val s else max (α.val s) a)=1
    rw [hα.2 s hs]
    simp [max_eq_left ha]

 theorem clipUpperProfile_before (α : boundedMassProfiles) {p a s : ℝ}
    (ha : a ≤ 1) (hs : s < p) : (clipUpperProfile α p ha).val s=α.val s := by
  exact ite_eq_left hs

 theorem clipUpperProfile_after (α : boundedMassProfiles) {p r a s : ℝ}
    (ha : a ≤ 1) (har : a ≤ α.val r) (hs : r ≤ s) :
    (clipUpperProfile α p ha).val s=α.val s := by
  change (if s < p then α.val s else max (α.val s) a)=α.val s
  simp only [max_eq_left (har.trans (α.property.2 hs)),ite_self]

 theorem clipUpperProfile_flat (α : boundedMassProfiles) {p r m a s : ℝ}
    (ha : a ≤ 1) (hma : m ≤ a) (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hs : s ∈ Ioo p r) : (clipUpperProfile α p ha).val s=a := by
  change (if s < p then α.val s else max (α.val s) a)=a
  rw [ite_eq_right (not_lt.mpr hs.1.le),hf s hs,max_eq_right hma]

 theorem clipUpperProfile_error (α : boundedMassProfiles) {p m a s : ℝ}
    (ha : a ≤ 1) (hma : m ≤ a) (hms : m ≤ α.val s) :
    |(clipUpperProfile α p ha).val s-α.val s| ≤ a-m := by
  change |(if s < p then α.val s else max (α.val s) a)-α.val s| ≤ a-m
  split_ifs
  · rw [sub_self,abs_zero]; linarith
  · by_cases hs : a ≤ α.val s
    · rw [max_eq_left hs,sub_self,abs_zero]; linarith
    · rw [max_eq_right (le_of_not_ge hs),abs_of_nonneg (by linarith)]
      linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.flatten_profile_reverse_error {J K : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {a A l : ℝ} (t : ℝ≥0) (ha : 0 < a) (ha1 : a ≤ 1) (hal : α.mass (l+t) ≤ a)
    (hA0 : 0 ≤ A) (hK : K.F = J.nonnegativeProfileValue α l t) (x : Fin 1 → ℝ) :
    |clockContinuation a K.F A x-clockContinuation a J.F (A+t) x-
      ((∫ s in l..l+t, α.mass s-a)/2)*J.observedSquare a (A+t) x| ≤
      -(2*(t:ℝ)*(∫ s in l..l+t, α.mass s-a)) := by
  have hg (k : ℕ) (y : Fin 1 → ℝ) :
      |(J.schedule ((α.cappedApprox k).grid l t k)).F y-K.F y| ≤ (t:ℝ)*(1/2:ℝ)^k := by
    rw [hK,(α.cappedApprox k).grid_eq_linear]
    have he : ((2^k:ℕ):ℝ≥0)*(t/(2^k:ℝ≥0)) = t := by simp only [Nat.cast_pow,Nat.cast_ofNat]; field_simp
    have hh := J.capped_linear_error (fun _ => 1) (fun i y => by rw [Fin.eq_zero i]; exact hJ.gradient y) α hα k l (t/(2^k:ℝ≥0)) (2^k) y
    rw [he] at hh
    apply hh.trans_eq
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.reduceAdd,
      nsmul_eq_mul,Nat.cast_one,one_pow,one_mul,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,
      Nat.cast_pow,Nat.cast_ofNat,div_pow,one_div]
    field_simp
    ring
  have ht : Tendsto (fun k => clockContinuation a (J.schedule ((α.cappedApprox k).grid l t k)).F A x)
      atTop (𝓝 (clockContinuation a K.F A x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hdist (k : ℕ) : dist (clockContinuation a (J.schedule ((α.cappedApprox k).grid l t k)).F A x)
        (clockContinuation a K.F A x) ≤ (t:ℝ)*(1/2:ℝ)^k := by
      rw [Real.dist_eq]
      exact clockContinuation_abs_sub_le (J.schedule _).lipschitz K.lipschitz ha (hg k) A x
    exact squeeze_zero (fun _ => dist_nonneg) hdist
      (by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (t:ℝ))
  have hw := capped_grid_excess_tendsto α a l t
  have hε : ∀ᶠ k : ℕ in atTop, (1/2:ℝ)^k ≤ a :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).eventually (gt_mem_nhds ha)).mono (fun _ h => h.le)
  apply le_of_tendsto_of_tendsto ((ht.sub_const _).sub ((hw.div_const 2).mul_const _)).abs
    ((hw.const_mul (2*(t:ℝ))).neg)
  filter_upwards [hε] with k hk
  have hh := HeatJet.flatten_schedule_reverse_error hJ hA ((α.cappedApprox k).grid l t k) ha ha1
    (fun c hc => ((α.cappedApprox k).grid_mass_bounds l t k hc).2.trans
      (max_le hal hk)) hA0 x
  simpa only [clockLength,PositiveMassProfile.grid_total_time] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarLocalResponse_upper {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hmr : α.val r=m) :
    let β := replaceIntervalProfile α hm.le hm1 (α.property.2 hpr.le |>.trans_eq hmr) hmr.ge
    let W := ∫ s in p..r, α.val s-m
    |scalarParisiValue hT α-scalarParisiValue hT β+
      T/2*(scalarPenalty α-scalarPenalty β)-T/2*W*scalarFlattenedEnergy hT α p r hm| ≤
      -(2*T^2*(r-p)*W)+T^2*W^2 := by
  dsimp only
  let β := replaceIntervalProfile α hm.le hm1 (α.property.2 hpr.le |>.trans_eq hmr) hmr.ge
  let W := ∫ s in p..r, α.val s-m
  let J := (scalarTailJet hT α r).square.evolve hm (T*(r-p))
  let K := scalarTailJet hT α p
  have hd : 0 ≤ T*(r-p) := mul_nonneg hT.le (sub_nonneg.mpr hpr.le)
  have hi : (∫ s in T*p..T*r, (rescaledMassProfile α hT).mass s-m) = T*W := by
    change (∫ s in T*p..T*r, (fun z => α.val z-m) (s/T)) = _
    rw [intervalIntegral.integral_comp_div (fun z => α.val z-m) hT.ne']
    simp only [mul_div_cancel_left₀ _ hT.ne',smul_eq_mul,W]
  have he (x : Fin 1 → ℝ) : |K.F x-(J.F x+(T/2*W)*J.A x)| ≤ -(2*T^2*(r-p)*W) := by
    have hh := HeatJet.flatten_profile_reverse_error (scalarTailJet_admissible hT α r)
      (scalarTailJet_gradientTest hT α r) (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) (A:=0) (l:=T*p)
      (Real.toNNReal (T*(r-p))) hm hm1
      (by
        simp only [Real.coe_toNNReal _ hd,show T*p+T*(r-p)=T*r by ring,
          rescaledMassProfile,mul_div_cancel_left₀ _ hT.ne']
        exact hmr.le)
      le_rfl (scalarTailJet_restart hT hpr.le hr α) x
    rw [clockContinuation_zero hm.ne'] at hh
    simp only [zero_add,Real.coe_toNNReal _ hd,show T*p+T*(r-p)=T*r by ring,hi] at hh
    change |K.F x-J.F x-(T*W/2)*J.A x| ≤ -(2*(T*(r-p))*(T*W)) at hh
    convert hh using 1
    · congr 1
      ring
    · ring
  have hbound (x : Fin 1 → ℝ) : |J.A x| ≤ 1 := by
    exact clockTest_abs_le (scalarTailJet hT α r).lipschitz
      (scalarTailJet hT α r).square.smoothA (scalarTailJet_square_bound hT α r) m _ x
  have hb := J.nonnegativeProfile_response_error K (by norm_num : (0:ℝ)<1) hbound he
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal (T*p)) 0
  have hJF : J.F=(scalarTailJet hT β p).F :=
    (scalarTailJet_interval_flat hT hpr hr α hm hm1 (α.property.2 hpr.le |>.trans_eq hmr) hmr.ge).symm
  have hv : J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0 =
      (scalarTailJet hT β p).nonnegativeProfileValue (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) 0 := by
    rw [J.nonnegativeProfileValue_congr_potential (scalarTailJet hT β p) hJF]
    exact scalarPrefix_congr _ hT hp (fun s hs =>
      (replaceIntervalProfile_before α hm.le hm1 (α.property.2 hpr.le |>.trans_eq hmr) hmr.ge hs.2).symm) 0
  rw [hv] at hb
  rw [scalarParisiValue_prefix hT ⟨hp,hpr.le.trans hr⟩ α,
    scalarParisiValue_prefix hT ⟨hp,hpr.le.trans hr⟩ β]
  change |K.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0-
      T/2*scalarPenalty α-T/4- ((scalarTailJet hT β p).nonnegativeProfileValue
      (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) 0-T/2*scalarPenalty β-T/4)+
      T/2*(scalarPenalty α-scalarPenalty β)-T/2*W*J.nonnegativeProfileTest
      (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0| ≤ _
  convert hb using 1 <;> congr 1 <;> ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarInterval_mass_bound (α : boundedMassProfiles) {m p r : ℝ}
    (hm : m ∈ Icc (0:ℝ) 1) (hpr : p ≤ r) :
    |∫ s in p..r, α.val s-m| ≤ r-p := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=p) (b:=r) (C:=1) (f:=fun s => α.val s-m) (fun s _ => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(α.property.1 s).1,hm.2],by linarith [(α.property.1 s).2,hm.1]⟩)
  simpa only [Real.norm_eq_abs,one_mul,abs_of_nonneg (sub_nonneg.mpr hpr)] using hh

 theorem scalarMinimizer_local_upper {T p r : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β)
    (hm : 0 < α.val p) (hW : 0 < ∫ s in p..r, α.val s-α.val p) :
    scalarFlattenedEnergy hT α p r hm ≤ r+6*T*(r-p) := by
  let m := α.val p
  let W := ∫ s in p..r, α.val s-m
  let E := scalarFlattenedEnergy hT α p r hm
  let β := replaceIntervalProfile α hm.le (α.property.1 p).2 (le_refl m) (α.property.2 hpr.le)
  have hV := hmin β (replaceIntervalProfile_mem hα hp hr hm.le (α.property.1 p).2
    (le_refl m) (α.property.2 hpr.le))
  have hR := (abs_le.mp (scalarLocalResponse_lower hT hp hpr hr α hm (α.property.1 p).2 rfl)).1
  have hP := scalarPenalty_interval_upper hp hpr.le hr α hm.le (α.property.1 p).2
    (le_refl m) (α.property.2 hpr.le) (c:=r) (fun s hs =>
      mul_le_mul_of_nonneg_right hs.2.le (sub_nonneg.mpr (α.property.2 hs.1.le)))
  have hB : W ≤ r-p := (le_abs_self W).trans (scalarInterval_mass_bound α (α.property.1 p) hpr.le)
  change 0 < W at hW
  change scalarParisiValue hT α ≤ scalarParisiValue hT β at hV
  change -(2*T^2*(r-p)*W+T^2*W^2) ≤ scalarParisiValue hT α-scalarParisiValue hT β+
    T/2*(scalarPenalty α-scalarPenalty β)-T/2*W*E at hR
  change scalarPenalty α-scalarPenalty β ≤ r*W at hP
  have hP' := mul_le_mul_of_nonneg_left hP (show 0 ≤ T/2 by positivity)
  have hB' := mul_le_mul_of_nonneg_left hB (show 0 ≤ T^2*W by positivity)
  change E ≤ r+6*T*(r-p)
  apply (mul_le_mul_iff_right₀ (show 0 < T*W/2 by positivity)).mp
  nlinarith

 theorem scalarMinimizer_local_lower {T p r : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β)
    (hm : 0 < α.val r) (hW : (∫ s in p..r, α.val s-α.val r) < 0) :
    p-6*T*(r-p) ≤ scalarFlattenedEnergy hT α p r hm := by
  let m := α.val r
  let W := ∫ s in p..r, α.val s-m
  let E := scalarFlattenedEnergy hT α p r hm
  let β := replaceIntervalProfile α hm.le (α.property.1 r).2 (α.property.2 hpr.le) (le_refl m)
  have hV := hmin β (replaceIntervalProfile_mem hα hp hr hm.le (α.property.1 r).2
    (α.property.2 hpr.le) (le_refl m))
  have hR := (abs_le.mp (scalarLocalResponse_upper hT hp hpr hr α hm (α.property.1 r).2 rfl)).1
  have hP := scalarPenalty_interval_upper hp hpr.le hr α hm.le (α.property.1 r).2
    (α.property.2 hpr.le) (le_refl m) (c:=p) (fun s hs =>
      mul_le_mul_of_nonpos_right hs.1.le (sub_nonpos.mpr (α.property.2 hs.2.le)))
  have hB : -W ≤ r-p := by
    have hh := scalarInterval_mass_bound α (α.property.1 r) hpr.le
    change |W| ≤ r-p at hh
    rwa [abs_of_neg hW] at hh
  change W < 0 at hW
  change scalarParisiValue hT α ≤ scalarParisiValue hT β at hV
  change -(-(2*T^2*(r-p)*W)+T^2*W^2) ≤ scalarParisiValue hT α-scalarParisiValue hT β+
    T/2*(scalarPenalty α-scalarPenalty β)-T/2*W*E at hR
  change scalarPenalty α-scalarPenalty β ≤ p*W at hP
  have hP' := mul_le_mul_of_nonneg_left hP (show 0 ≤ T/2 by positivity)
  have hB' := mul_le_mul_of_nonneg_left hB (show 0 ≤ -(T^2*W) by nlinarith [sq_nonneg T])
  change p-6*T*(r-p) ≤ E
  apply (mul_le_mul_iff_right₀ (show 0 < -(T*W/2) by nlinarith [mul_neg_of_pos_of_neg hT hW])).mp
  nlinarith

end SKFluctuations.Hierarchy

end

end OAI
