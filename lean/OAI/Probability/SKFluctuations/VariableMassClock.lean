import Mathlib
import OAI.Probability.SKFluctuations.ResidualGradientBound

namespace OAI

/-! Variable Mass Clock. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem AbsBounded.comp {X Y : Type*} {f : X → ℝ} (h : AbsBounded f) (g : Y → X) :
    AbsBounded (fun y => f (g y)) := by
  obtain ⟨K,hK,hb⟩ := h
  exact ⟨K,hK,fun y => hb (g y)⟩

 theorem parametric_clockTest_continuous_mass {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] [FirstCountableTopology X]
    {F A : X → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ} {m : X → ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : X × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : X × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (hm : Continuous m) (hmb : AbsBounded m) (x : ι → ℝ) :
    Continuous (fun p : ℝ × X => clockTest (m p.2) (F p.2) (A p.2) p.1 x) := by
  obtain ⟨M,hM,hbound⟩ := hmb
  have hL (r : X) : LipschitzWith (⟨M,hM⟩*C) (fun y => m r*F r y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [Real.dist_eq,← mul_sub,abs_mul]
    calc
      _ ≤ M*((C:ℝ)*dist y z) := mul_le_mul (hbound r) ((hF r).dist_le_mul y z)
        (abs_nonneg _) hM
      _ = _ := by change M*((C:ℝ)*dist y z) = (M*(C:ℝ))*dist y z; ring
  have hh := parametric_clockTest_continuous hL
    ((hm.comp continuous_fst).mul hcF) hcA hb 1 x
  apply hh.congr
  intro p
  unfold clockTest shiftedMean tiltedMean
  simp only [one_mul]

noncomputable def unitMassClip (m : ℝ) : ℝ := max 0 (min m 1)

theorem unitMassClip_continuous : Continuous unitMassClip := by unfold unitMassClip; fun_prop

theorem unitMassClip_bounds (m : ℝ) : unitMassClip m ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_right _ _)

theorem unitMassClip_eq {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) : unitMassClip m = m := by
  unfold unitMassClip
  rw [min_eq_left hm.2,max_eq_right hm.1]

 theorem HeatJetFamily.clockDerivative_continuous_mass {n : ℕ} (V : HeatJetFamily n)
    (x : Fin (n+1) → ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => clockTestDerivative (unitMassClip p.2.2)
      (V.J p.2.1).F (V.J p.2.1).G (V.J p.2.1).H
      (V.J p.2.1).A (V.J p.2.1).A₁ (V.J p.2.1).A₂ p.1 x) := by
  let m : ℝ × ℝ → ℝ := fun p => unitMassClip p.2
  have hm : Continuous m := unitMassClip_continuous.comp continuous_snd
  have hmb : AbsBounded m := ⟨1,zero_le_one,fun p => by
    rw [abs_of_nonneg (unitMassClip_bounds p.2).1]; exact (unitMassClip_bounds p.2).2⟩
  let z : ((ℝ × ℝ) × (Fin (n+1) → ℝ)) → ℝ × (Fin (n+1) → ℝ) := fun p => (p.1.1,p.2)
  have hz : Continuous z := (continuous_fst.fst).prodMk continuous_snd
  have hm' : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) => m p.1) := hm.comp continuous_fst
  have hmb' : AbsBounded (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) => m p.1) := hmb.comp Prod.fst
  have hp : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) =>
      potentialHeatTrace (m p.1) (V.J p.1.1).G (V.J p.1.1).H p.2) := by
    apply continuous_finsetSum
    intro i _
    exact (hm'.mul ((V.continuousH i).comp hz)).add
      ((hm'.pow 2).mul (((V.continuousG i).comp hz).pow 2))
  have hpb : AbsBounded (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) =>
      potentialHeatTrace (m p.1) (V.J p.1.1).G (V.J p.1.1).H p.2) := by
    apply AbsBounded.sum
    intro i
    simpa only [pow_two] using (hmb'.mul ((V.boundedH i).comp z)).add
      ((hmb'.mul hmb').mul (((V.boundedG i).comp z).mul ((V.boundedG i).comp z)))
  have hw : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) =>
      testedHeatTrace (m p.1) (V.J p.1.1).G (V.J p.1.1).H
        (V.J p.1.1).A (V.J p.1.1).A₁ (V.J p.1.1).A₂ p.2) := by
    apply continuous_finsetSum
    intro i _
    exact (((V.continuousA₂ i).comp hz).add
      (((hm'.const_mul 2).mul ((V.continuousA₁ i).comp hz)).mul ((V.continuousG i).comp hz))).add
      ((V.continuousA.comp hz).mul ((hm'.mul ((V.continuousH i).comp hz)).add
        ((hm'.pow 2).mul (((V.continuousG i).comp hz).pow 2))))
  have hwb : AbsBounded (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) =>
      testedHeatTrace (m p.1) (V.J p.1.1).G (V.J p.1.1).H
        (V.J p.1.1).A (V.J p.1.1).A₁ (V.J p.1.1).A₂ p.2) := by
    apply AbsBounded.sum
    intro i
    simpa only [pow_two] using (((V.boundedA₂ i).comp z).add
      (((hmb'.const_mul 2).mul ((V.boundedA₁ i).comp z)).mul ((V.boundedG i).comp z))).add
      ((V.boundedA.comp z).mul ((hmb'.mul ((V.boundedH i).comp z)).add
        ((hmb'.mul hmb').mul (((V.boundedG i).comp z).mul ((V.boundedG i).comp z)))))
  obtain ⟨KA,_,hA⟩ := V.boundedA.comp z
  obtain ⟨KP,_,hP⟩ := hpb
  obtain ⟨KW,_,hW⟩ := hwb
  exact ((parametric_clockTest_continuous_mass (fun p => V.lipschitz p.1)
    (V.continuousF.comp hz) hw (fun p y => hW (p,y)) hm hmb x).sub
    ((parametric_clockTest_continuous_mass (fun p => V.lipschitz p.1)
      (V.continuousF.comp hz) (V.continuousA.comp hz) (fun p y => hA (p,y)) hm hmb x).mul
      (parametric_clockTest_continuous_mass (fun p => V.lipschitz p.1)
        (V.continuousF.comp hz) hp (fun p y => hP (p,y)) hm hmb x))).const_mul (1/2:ℝ)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def scalarTailJetFamily {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) : HeatJetFamily 0 where
  J := scalarTailJet hT α
  C := 1
  lipschitz := scalarTailJet_lipschitz hT α
  continuousF := scalarTailJet_F_continuous hT α
  continuousA := scalarTailJet_spatial_continuous hT α 1
  continuousG _ := scalarTailJet_spatial_continuous hT α 1
  continuousH _ := scalarTailJet_spatial_continuous hT α 2
  continuousA₁ _ := scalarTailJet_spatial_continuous hT α 2
  continuousA₂ _ := scalarTailJet_spatial_continuous hT α 3
  boundedA := ⟨(ReplicaTree.attachmentCount 1 0:ℝ),by positivity,fun p =>
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ 0 (p.2 0)⟩
  boundedG _ := ⟨(ReplicaTree.attachmentCount 1 0:ℝ),by positivity,fun p =>
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ 0 (p.2 0)⟩
  boundedH _ := ⟨(ReplicaTree.attachmentCount 1 1:ℝ),by positivity,fun p =>
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ 1 (p.2 0)⟩
  boundedA₁ _ := ⟨(ReplicaTree.attachmentCount 1 1:ℝ),by positivity,fun p =>
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ 1 (p.2 0)⟩
  boundedA₂ _ := ⟨(ReplicaTree.attachmentCount 1 2:ℝ),by positivity,fun p =>
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ 2 (p.2 0)⟩

theorem scalarTailJet_A_zero {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    (scalarTailJet hT α q).A 0 = 0 :=
  scalarProfileJet_gradient_zero _ (fun s => (α.property.1 (s/T)).2) _ _

noncomputable def HeatJet.observedRate {n : ℕ} (J : HeatJet n) (m t : ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  clockTestDerivative m J.square.F J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ t x

theorem HeatJet.observedRate_zero {J : HeatJet 0} {x : Fin 1 → ℝ} (hA : J.A x = 0)
    (m : ℝ) : J.observedRate m 0 x = (J.A₁ 0 x)^2 := by
  simp only [HeatJet.observedRate,clockTestDerivative,clockTest_zero,
    testedHeatTrace,potentialHeatTrace,HeatJet.square,hA]
  simp only [Nat.reduceAdd, Fin.sum_univ_one]
  ring

 

noncomputable def scalarHeadObservedRatio {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m : ℝ) : ℝ :=
  T*(∫ u in (0:ℝ)..1, (scalarTailJet hT α q).observedRate (unitMassClip m) (T*q*u) 0)

theorem scalarHeadObservedRatio_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × ℝ => scalarHeadObservedRatio hT α p.1 p.2) := by
  have hh := (scalarTailJetFamily hT α).square.clockDerivative_continuous_mass (0:Fin 1 → ℝ)
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (scalarTailJet hT α p.1.1).observedRate (unitMassClip p.1.2) (T*p.1.1*p.2) 0) :=
    hh.comp (((continuous_const.mul continuous_fst.fst).mul continuous_snd).prodMk continuous_fst)
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1).const_mul T

theorem scalarHeadObservedRatio_zero {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (m : ℝ) :
    scalarHeadObservedRatio hT α 0 m = T*((scalarTailJet hT α 0).A₁ 0 0)^2 := by
  unfold scalarHeadObservedRatio
  simp only [mul_zero,zero_mul,HeatJet.observedRate_zero (scalarTailJet_A_zero hT α 0),
    intervalIntegral.integral_const,sub_zero,one_smul]

theorem scalarHeadObservedRatio_eq {T q m : ℝ} (hT : 0 < T) (hq : 0 < q)
    (α : boundedMassProfiles) (hm : m ∈ Icc (0:ℝ) 1) :
    (scalarTailJet hT α q).observedSquare m (T*q) 0 = q*scalarHeadObservedRatio hT α q m := by
  let J := (scalarTailJet hT α q).square
  have ht : 0 < T*q := mul_pos hT hq
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.le
    ((clockTest_continuous J.lipschitz J.smoothA m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
    (f':=fun t => (scalarTailJet hT α q).observedRate m t 0)
    (fun t h => ((hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH
      J.smoothA₁ J.smoothA₂ J.derivF J.derivG J.derivA J.derivA₁ m 0 h.1.le).hasDerivAt
        (Ici_mem_nhds h.1)).hasDerivWithinAt)
    (by
      exact ((clockTestDerivative_continuous J.lipschitz J.smoothA J.smoothG J.smoothH
        J.smoothA₁ J.smoothA₂ m).comp (continuous_id.prodMk continuous_const)).intervalIntegrable (μ := volume) 0 (T*q))
  have hz : clockTest m J.F J.A 0 0 = 0 := by
    rw [clockTest_zero]
    change ((scalarTailJet hT α q).A 0)^2 = 0
    rw [scalarTailJet_A_zero,pow_two,mul_zero]
  simp only [Function.comp_apply, id_eq] at hh
  rw [hz,sub_zero] at hh
  unfold scalarHeadObservedRatio
  rw [unitMassClip_eq hm]
  have hi := intervalIntegral.integral_comp_mul_left
    (fun t => (scalarTailJet hT α q).observedRate m t 0) ht.ne'
    (a:=0) (b:=1)
  simp only [mul_zero,mul_one,smul_eq_mul] at hi
  rw [hi,hh]
  change _ = q*(T*((T*q)⁻¹*(scalarTailJet hT α q).observedSquare m (T*q) 0))
  field_simp

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.testAverageRate {n : ℕ} (J : HeatJet n) (m t : ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, clockTestDerivative m J.F J.G J.H J.A J.A₁ J.A₂ (t*u) x

theorem HeatJet.testAverageRate_zero {n : ℕ} (J : HeatJet n) (m : ℝ)
    (x : Fin (n+1) → ℝ) :
    J.testAverageRate m 0 x = clockTestDerivative m J.F J.G J.H J.A J.A₁ J.A₂ 0 x := by
  simp only [HeatJet.testAverageRate,zero_mul,intervalIntegral.integral_const,sub_zero,one_smul]

theorem HeatJet.testAverageRate_eq {n : ℕ} (J : HeatJet n) (m : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (x : Fin (n+1) → ℝ) :
    clockTest m J.F J.A t x = J.A x+t*J.testAverageRate m t x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [clockTest_zero,zero_mul,add_zero]
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.le
    ((clockTest_continuous J.lipschitz J.smoothA m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
    (f':=fun s => clockTestDerivative m J.F J.G J.H J.A J.A₁ J.A₂ s x)
    (fun s h => ((hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH
      J.smoothA₁ J.smoothA₂ J.derivF J.derivG J.derivA J.derivA₁ m x h.1.le).hasDerivAt
        (Ici_mem_nhds h.1)).hasDerivWithinAt)
    (((clockTestDerivative_continuous J.lipschitz J.smoothA J.smoothG J.smoothH
      J.smoothA₁ J.smoothA₂ m).comp (continuous_id.prodMk continuous_const)).intervalIntegrable
        (μ:=volume) 0 t)
  simp only [Function.comp_apply,id_eq,clockTest_zero] at hh
  have hi := intervalIntegral.integral_comp_mul_left
    (fun s => clockTestDerivative m J.F J.G J.H J.A J.A₁ J.A₂ s x) ht.ne'
    (a:=0) (b:=1)
  simp only [mul_zero,mul_one,smul_eq_mul] at hi
  unfold HeatJet.testAverageRate
  rw [hi,hh]
  field_simp
  ring

theorem HeatJetFamily.testAverageRate_continuous_mass {n : ℕ} (V : HeatJetFamily n)
    (x : Fin (n+1) → ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) =>
      (V.J p.2.1).testAverageRate (unitMassClip p.2.2) p.1 x) := by
  have hh := V.clockDerivative_continuous_mass x
  have hc : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
      clockTestDerivative (unitMassClip p.1.2.2) (V.J p.1.2.1).F
        (V.J p.1.2.1).G (V.J p.1.2.1).H (V.J p.1.2.1).A
        (V.J p.1.2.1).A₁ (V.J p.1.2.1).A₂ (p.1.1*p.2) x) :=
    hh.comp ((continuous_fst.fst.mul continuous_snd).prodMk continuous_fst.snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

noncomputable def replaceIntervalProfile (α : boundedMassProfiles) {p r m : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hpm : α.val p ≤ m) (hmr : m ≤ α.val r) :
    boundedMassProfiles :=
  ⟨(fun s => if s < p then α.val s else if s < r then m else α.val s), by
    constructor
    · intro s
      dsimp only
      split_ifs <;> first | exact α.property.1 s | exact ⟨hm0,hm1⟩
    · intro s t hst
      dsimp only
      by_cases hs : s < p
      · rw [ite_eq_left hs]
        by_cases ht : t < p
        · rw [ite_eq_left ht]; exact α.property.2 hst
        · rw [ite_eq_right ht]
          split_ifs
          · exact (α.property.2 hs.le).trans hpm
          · exact α.property.2 hst
      · rw [ite_eq_right hs,ite_eq_right (not_lt.mpr ((le_of_not_gt hs).trans hst))]
        by_cases hsr : s < r
        · rw [ite_eq_left hsr]
          by_cases htr : t < r
          · rw [ite_eq_left htr]
          · rw [ite_eq_right htr]
            exact hmr.trans (α.property.2 (le_of_not_gt htr))
        · rw [ite_eq_right hsr,ite_eq_right (not_lt.mpr ((le_of_not_gt hsr).trans hst))]
          exact α.property.2 hst⟩

 theorem replaceIntervalProfile_before (α : boundedMassProfiles) {p r m s : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hpm : α.val p ≤ m) (hmr : m ≤ α.val r)
    (hs : s < p) : (replaceIntervalProfile α hm0 hm1 hpm hmr).val s = α.val s := by
  simp only [replaceIntervalProfile,hs,ite_true]

 theorem replaceIntervalProfile_inside (α : boundedMassProfiles) {p r m s : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hpm : α.val p ≤ m) (hmr : m ≤ α.val r)
    (hs : s ∈ Ico p r) : (replaceIntervalProfile α hm0 hm1 hpm hmr).val s = m := by
  simp only [replaceIntervalProfile,not_lt.mpr hs.1,hs.2,ite_false,ite_true]

 theorem replaceIntervalProfile_after (α : boundedMassProfiles) {p r m s : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hpm : α.val p ≤ m) (hmr : m ≤ α.val r)
    (hs : r ≤ s) : (replaceIntervalProfile α hm0 hm1 hpm hmr).val s = α.val s := by
  simp only [replaceIntervalProfile,not_lt.mpr hs,ite_false,ite_self]

 theorem replaceIntervalProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {p r m : ℝ} (hp : 0 ≤ p) (hr : r ≤ 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hpm : α.val p ≤ m) (hmr : m ≤ α.val r) :
    replaceIntervalProfile α hm0 hm1 hpm hmr ∈ scalarProfiles := by
  constructor
  · intro s hs
    rw [replaceIntervalProfile_before α hm0 hm1 hpm hmr (hs.trans_le hp)]
    exact hα.1 s hs
  · intro s hs
    rw [replaceIntervalProfile_after α hm0 hm1 hpm hmr (hr.trans hs.le)]
    exact hα.2 s hs

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarParisiValue_prefix {T p : ℝ} (hT : 0 < T) (hp : p ∈ Icc (0:ℝ) 1)
    (α : boundedMassProfiles) :
    scalarParisiValue hT α = (scalarTailJet hT α p).nonnegativeProfileValue
      (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0-T/2*scalarPenalty α-T/4 := by
  have hh := congrFun (scalarTailJet_restart hT hp.1 hp.2 α) (0:Fin 1 → ℝ)
  rw [scalarTailJet_F] at hh
  simp only [mul_zero,sub_zero,mul_one] at hh
  have he : Real.toNNReal T = (⟨T,hT.le⟩:ℝ≥0) := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ hT.le
  rw [he] at hh
  exact congrArg (fun z => z-T/2*scalarPenalty α-T/4) hh

 theorem scalarPrefix_congr {n : ℕ} (J : HeatJet n) {T : ℝ} (hT : 0 < T)
    {p : ℝ} (hp : 0 ≤ p) {α β : boundedMassProfiles}
    (he : ∀ s ∈ Ioo (0:ℝ) p, α.val s=β.val s) (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) x =
      J.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) x := by
  apply J.nonnegativeProfileValue_congr_ae
  refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  change α.val (s/T)=β.val (s/T)
  apply he
  simp only [zero_add,Real.coe_toNNReal _ (mul_nonneg hT.le hp)] at hs
  exact ⟨div_pos hs.1 hT,(div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩

 theorem scalarTailJet_interval_flat {T p r m : ℝ} (hT : 0 < T)
    (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hpm : α.val p ≤ m) (hmr : m ≤ α.val r) :
    (scalarTailJet hT (replaceIntervalProfile α hm.le hm1 hpm hmr) p).F =
      clockContinuation m (scalarTailJet hT α r).F (T*(r-p)) := by
  let β := replaceIntervalProfile α hm.le hm1 hpm hmr
  have ht : (scalarTailJet hT β r).F=(scalarTailJet hT α r).F :=
    scalarTailJet_congr hT hr (fun s hs => replaceIntervalProfile_after α hm.le hm1 hpm hmr hs.1.le)
  have hd : 0 < T*(r-p) := mul_pos hT (sub_pos.mpr hpr)
  funext x
  rw [scalarTailJet_restart hT hpr.le hr]
  have hh := HeatJet.nonnegativeProfileValue_constant (scalarTailJet hT β r)
    (rescaledMassProfile β hT) hm (T*p) (Real.toNNReal (T*(r-p)))
    (by rwa [Real.coe_toNNReal _ hd.le]) (by
      intro s hs
      change β.val (s/T)=m
      apply replaceIntervalProfile_inside
      simp only [Real.coe_toNNReal _ hd.le] at hs
      exact ⟨(le_div_iff₀ hT).mpr (by nlinarith [hs.1]),
        (div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩) x
  simpa only [ht,Real.coe_toNNReal _ hd.le] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def scalarFlattenedEnergy {T m : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (p r : ℝ) (hm : 0 < m) : ℝ :=
  ((scalarTailJet hT α r).square.evolve hm (T*(r-p))).nonnegativeProfileTest
    (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0

 theorem scalarLocalResponse_lower {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hpm : α.val p=m) :
    let β := replaceIntervalProfile α hm.le hm1 hpm.le
      (hpm.symm ▸ α.property.2 hpr.le)
    let W := ∫ s in p..r, α.val s-m
    |scalarParisiValue hT α-scalarParisiValue hT β+
      T/2*(scalarPenalty α-scalarPenalty β)-T/2*W*scalarFlattenedEnergy hT α p r hm| ≤
      2*T^2*(r-p)*W+T^2*W^2 := by
  dsimp only
  let β := replaceIntervalProfile α hm.le hm1 hpm.le (hpm.symm ▸ α.property.2 hpr.le)
  let W := ∫ s in p..r, α.val s-m
  let J := (scalarTailJet hT α r).square.evolve hm (T*(r-p))
  let K := scalarTailJet hT α p
  have hd : 0 ≤ T*(r-p) := mul_nonneg hT.le (sub_nonneg.mpr hpr.le)
  have hi : (∫ s in T*p..T*r, (rescaledMassProfile α hT).mass s-m) = T*W := by
    change (∫ s in T*p..T*r, (fun z => α.val z-m) (s/T)) = _
    rw [intervalIntegral.integral_comp_div (fun z => α.val z-m) hT.ne']
    simp only [mul_div_cancel_left₀ _ hT.ne',smul_eq_mul,W]
  have he (x : Fin 1 → ℝ) : |K.F x-(J.F x+(T/2*W)*J.A x)| ≤ 2*T^2*(r-p)*W := by
    have hh := HeatJet.flatten_profile_error (scalarTailJet_admissible hT α r)
      (scalarTailJet_gradientTest hT α r) (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) (A:=0) (l:=T*p)
      (Real.toNNReal (T*(r-p))) hm hm1
      (by simpa only [rescaledMassProfile,mul_div_cancel_left₀ _ hT.ne'] using hpm.ge)
      le_rfl (scalarTailJet_restart hT hpr.le hr α) x
    rw [clockContinuation_zero hm.ne'] at hh
    simp only [zero_add,Real.coe_toNNReal _ hd,show T*p+T*(r-p)=T*r by ring,hi] at hh
    change |K.F x-J.F x-(T*W/2)*J.A x| ≤ 2*(T*(r-p))*(T*W) at hh
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
    (scalarTailJet_interval_flat hT hpr hr α hm hm1 hpm.le (hpm.symm ▸ α.property.2 hpr.le)).symm
  have hv : J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0 =
      (scalarTailJet hT β p).nonnegativeProfileValue (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) 0 := by
    rw [J.nonnegativeProfileValue_congr_potential (scalarTailJet hT β p) hJF]
    exact scalarPrefix_congr _ hT hp (fun s hs =>
      (replaceIntervalProfile_before α hm.le hm1 hpm.le (hpm.symm ▸ α.property.2 hpr.le) hs.2).symm) 0
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

 theorem HeatJet.clockTest_time_bound {n : ℕ} (J : HeatJet n) (m : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, |clockTest m J.F J.A t x-J.A x| ≤ C*t := by
  obtain ⟨C,hC,hb⟩ := clockTestDerivative_absBounded J.lipschitz J.smoothA
    J.smoothG J.smoothH J.smoothA₁ J.smoothA₂ m
  refine ⟨C,hC,fun t ht x => ?_⟩
  have hc : ContinuousOn (fun t : ℝ => clockTest m J.F J.A t x) (Ici 0) := ((clockTest_continuous J.lipschitz J.smoothA m).comp
    (continuous_id.prodMk continuous_const)).continuousOn (s:=Ici 0)
  have hd (r : ℝ) (hr : 0 < r) := (hasDerivWithinAt_clockTest J.lipschitz J.smoothA
    J.smoothG J.smoothH J.smoothA₁ J.smoothA₂ J.derivF J.derivG J.derivA J.derivA₁
    m x hr.le).hasDerivAt (Ici_mem_nhds hr)
  have hh := abs_sub_le_mul_of_deriv_interior hc hd (fun r _ => hb (r,x)) ht (le_refl (0:ℝ))
  simpa only [clockTest_zero,sub_zero,zero_sub,abs_neg,abs_of_nonneg ht,abs_sub_comm] using hh

 theorem HeatJet.clockValue_time_bound {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, |clockContinuation m J.F t x-J.F x| ≤ C*t := by
  obtain ⟨C,hC,hb⟩ := clockDerivative_absBounded J.lipschitz J.smoothG J.smoothH m
  refine ⟨C,hC,fun t ht x => ?_⟩
  have hc : ContinuousOn (fun t : ℝ => clockContinuation m J.F t x) (Ici 0) := ((clockContinuation_continuous J.lipschitz m).comp
    (continuous_id.prodMk continuous_const)).continuousOn (s:=Ici 0)
  have hd (r : ℝ) (hr : 0 < r) := hasDerivAt_clockContinuation J.lipschitz J.smoothG
    J.smoothH J.derivF J.derivG hm hr x
  have hh := abs_sub_le_mul_of_deriv_interior hc hd (fun r _ => hb (r,x)) ht (le_refl (0:ℝ))
  simpa only [clockContinuation_zero hm.ne',sub_zero,zero_sub,abs_neg,abs_of_nonneg ht,abs_sub_comm] using hh

 theorem HeatJet.clockTest_terminal_stability {n : ℕ} (J K : HeatJet n) {m E L D : ℝ}
    (hm : 0 < m) (hm1 : m ≤ 1) (hE : 0 ≤ E) (hF : ∀ x, |K.F x-J.F x| ≤ E)
    (hL : 0 < L) (hA : ∀ x, |J.A x| ≤ L) (hD : ∀ x, |K.A x-J.A x| ≤ D)
    (t : ℝ) (x : Fin (n+1) → ℝ) :
    |clockTest m K.F K.A t x-clockTest m J.F J.A t x| ≤ D+4*E*L := by
  let cs : List (GaussianStep (Fin (n+1))) := [(m,fun _ => Real.toNNReal t)]
  have ho : PrefixOrdered 0 1 cs := ⟨le_rfl,hm.le,hm,hm.le,hm1⟩
  have he := prefixTest_potential_stability J.lipschitz K.lipschitz hE hF
    J.smoothA.continuous hL hA cs ho x
  have hd := clockTest_abs_le K.lipschitz (K.smoothA.sub J.smoothA) hD m t x
  rw [clockTest_sub_test K.lipschitz K.smoothA J.smoothA] at hd
  change |clockTest m K.F J.A t x-clockTest m J.F J.A t x| ≤ 4*1*E*L at he
  exact (abs_sub_le _ (clockTest m K.F J.A t x) _).trans
    (by simpa only [mul_one] using add_le_add hd he)

 theorem HeatJet.evolve_small_terminal_tendsto {n : ℕ} (J : ℕ → HeatJet n) (L : HeatJet n)
    (hF : TendstoUniformly (fun k => (J k).F) L.F atTop)
    (hA : TendstoUniformly (fun k => (J k).A) L.A atTop)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (t : ℕ → ℝ)
    (ht : ∀ k, 0 ≤ t k) (ht0 : Tendsto t atTop (𝓝 0)) :
    TendstoUniformly (fun k => ((J k).evolve hm (t k)).F) L.F atTop ∧
      TendstoUniformly (fun k => ((J k).evolve hm (t k)).A) L.A atTop := by
  obtain ⟨C,hC,hCv⟩ := L.clockValue_time_bound hm
  obtain ⟨B,hB,hBt⟩ := L.clockTest_time_bound m
  obtain ⟨K,hK,hKA⟩ := L.smoothA.bound
  have hc : Tendsto (fun k => C*t k) atTop (𝓝 0) := by simpa only [mul_zero] using ht0.const_mul C
  have hb : Tendsto (fun k => B*t k) atTop (𝓝 0) := by simpa only [mul_zero] using ht0.const_mul B
  constructor
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hF (ε/2) (by positivity),
      hc.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with k hk he x
    have hf (y) : |(J k).F y-L.F y| ≤ ε/2 := by simpa only [Real.dist_eq,abs_sub_comm] using (hk y).le
    have hh := clockContinuation_abs_sub_le (J k).lipschitz L.lipschitz hm hf (t k) x
    rw [Real.dist_eq,abs_sub_comm]
    exact (abs_sub_le _ (clockContinuation m L.F (t k) x) _).trans_lt
      ((add_le_add hh (hCv _ (ht k) x)).trans_lt (by linarith))
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    let δ := ε/(2*(1+4*(K+1)))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    filter_upwards [Metric.tendstoUniformly_iff.mp hF δ hδ,
      Metric.tendstoUniformly_iff.mp hA δ hδ,
      hb.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with k hkF hkA he x
    have hf (y) : |(J k).F y-L.F y| ≤ δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hkF y).le
    have ha (y) : |(J k).A y-L.A y| ≤ δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hkA y).le
    have hh := L.clockTest_terminal_stability (J k) hm hm1 hδ.le hf (by linarith : 0 < K+1)
      (fun y => (hKA y).trans (by linarith)) ha (t k) x
    have hd : δ+4*δ*(K+1)=ε/2 := by dsimp [δ]; field_simp
    rw [hd] at hh
    rw [Real.dist_eq,abs_sub_comm]
    exact (abs_sub_le _ (clockTest m L.F L.A (t k) x) _).trans_lt
      ((add_le_add hh (hBt _ (ht k) x)).trans_lt (by linarith))

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open Set

theorem closedSet_gap_endpoints {S : Set ℝ} (hS : IsClosed S) {a x b : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hax : a < x) (hxb : x < b) (hx : x ∉ S) :
    ∃ p r, p ∈ S ∧ r ∈ S ∧ a ≤ p ∧ p < x ∧ x < r ∧ r ≤ b ∧
      ∀ u ∈ Ioo p r, u ∉ S := by
  obtain ⟨p,hp⟩ := (isCompact_Icc.inter_left hS).exists_isGreatest
    (show (S ∩ Icc a x).Nonempty from ⟨a,ha,le_rfl,hax.le⟩)
  obtain ⟨r,hr⟩ := (isCompact_Icc.inter_left hS).exists_isLeast
    (show (S ∩ Icc x b).Nonempty from ⟨b,hb,hxb.le,le_rfl⟩)
  have hpx : p < x := hp.1.2.2.lt_of_ne (by intro he; exact hx (he ▸ hp.1.1))
  have hxr : x < r := hr.1.2.1.lt_of_ne (by intro he; exact hx (he.symm ▸ hr.1.1))
  refine ⟨p,r,hp.1.1,hr.1.1,hp.1.2.1,hpx,hxr,hr.1.2.2,?_⟩
  intro u hu hus
  obtain hux | hxu := le_total u x
  · exact not_lt_of_ge (hp.2 ⟨hus,hp.1.2.1.trans hu.1.le,hux⟩) hu.1
  · exact not_lt_of_ge (hr.2 ⟨hus,hxu,hu.2.le.trans hr.1.2.2⟩) hu.2

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.nonnegativeProfileTest_lipschitzOnWith {n : ℕ} (J : ℝ → HeatJet n)
    {K : ℝ≥0} {s : Set ℝ} (hF : ∀ u v, (J u).F=(J v).F)
    (hA : ∀ y, LipschitzOnWith K (fun u => (J u).A y) s)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    LipschitzOnWith K (fun u => (J u).nonnegativeProfileTest α l t x) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  rw [Real.dist_eq]
  have hh := (J v).nonnegativeProfileTest_remainder_bound (J u) (J v) (hF u v) rfl
    (c:=0) (E:=K*dist u v) (fun y => by
      simpa only [zero_mul,sub_zero,Real.dist_eq] using (hA y).dist_le_mul u hu v hv) α hα l t x
  simpa only [zero_mul,sub_zero] using hh

 theorem lipschitzOnWith_closed_interval_of_derivative_bound {f g : ℝ → ℝ}
    {a b : ℝ} (hab : a < b) {K : ℝ≥0} (hc : Continuous f)
    (hd : ∀ u ∈ Ioo a b, HasDerivAt f (g u) u)
    (hb : ∀ u ∈ Ioo a b, |g u| ≤ K) : LipschitzOnWith K f (Icc a b) := by
  have hh := (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u hu => (hd u hu).hasDerivWithinAt) (C:=K) (fun u hu => by
      change ‖g u‖ ≤ (K:ℝ)
      simpa only [Real.norm_eq_abs] using hb u hu)
  have he := LipschitzOnWith.closure hc.continuousOn hh
  rwa [closure_Ioo hab.ne] at he

 theorem HeatJet.profileGapEnergy_continuousOn (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m T : ℝ} (hm : 0 < m) (hT : 0 < T)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    ContinuousOn (fun u => (J.profileGapEnergyJet hG hm T u).nonnegativeProfileTest α l t x)
      (Icc 0 T) := by
  obtain ⟨K,hK,hb⟩ := J.scalarGapCurvature_bound hG hm T
  apply (HeatJet.nonnegativeProfileTest_lipschitzOnWith
    (J.profileGapEnergyJet hG hm T) (K:=⟨K,hK⟩)
    (fun u v => (J.profileGapEnergyJet_F hG hm T u).trans (J.profileGapEnergyJet_F hG hm T v).symm)
    ?_ α hα l t x).continuousOn
  intro y
  simp only [HeatJet.profileGapEnergyJet_A]
  apply lipschitzOnWith_closed_interval_of_derivative_bound hT (K:=⟨K,hK⟩)
    (J.continuous_scalarGapEnergy hG hm T y)
    (fun u hu => J.hasDerivAt_scalarGapEnergy hG hH hm hu y)
  intro u _
  change |J.scalarGapCurvature m T u y| ≤ K
  have hy : (fun _ : Fin 1 => y 0)=y := by ext i; rw [Fin.eq_zero i]
  simpa only [hy, NNReal.coe_mk] using hb (u,y 0)

 theorem HeatJet.profileGapCurvature_continuousOn (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m T : ℝ} (hm : 0 < m) (hT : 0 < T)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    ContinuousOn (fun u => (J.profileGapCurvatureJet hG hm T u).nonnegativeProfileTest α l t x)
      (Icc 0 T) := by
  obtain ⟨K,hK,hb⟩ := J.scalarGapThird_bound hG hm T
  apply (HeatJet.nonnegativeProfileTest_lipschitzOnWith
    (J.profileGapCurvatureJet hG hm T) (K:=⟨K,hK⟩)
    (fun u v => (J.profileGapCurvatureJet_F hG hm T u).trans (J.profileGapCurvatureJet_F hG hm T v).symm)
    ?_ α hα l t x).continuousOn
  intro y
  simp only [HeatJet.profileGapCurvatureJet_A]
  apply lipschitzOnWith_closed_interval_of_derivative_bound hT (K:=⟨K,hK⟩)
    (J.continuous_scalarGapCurvature hG hm T y)
    (fun u hu => J.hasDerivAt_scalarGapCurvature hG hm hH hu y)
  intro u _
  change |J.scalarGapThird m T u y| ≤ K
  have hy : (fun _ : Fin 1 => y 0)=y := by ext i; rw [Fin.eq_zero i]
  simpa only [hy, NNReal.coe_mk] using hb (u,y 0)

end SKFluctuations.Hierarchy

end

end OAI
