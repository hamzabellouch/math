import Mathlib
import OAI.Probability.SKFluctuations.ScalarGapWeighted

namespace OAI

/-! Clock Flatten Schedule. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

def clockLength (cs : List HeatClock) : ℝ := (cs.map (fun c => (c.time:ℝ))).sum
def clockExcess (a : ℝ) (cs : List HeatClock) : ℝ :=
  (cs.map (fun c => (c.mass-a)*(c.time:ℝ))).sum

@[simp] theorem clockLength_nil : clockLength [] = 0 := rfl
@[simp] theorem clockLength_cons (c : HeatClock) (cs : List HeatClock) :
    clockLength (c::cs) = c.time+clockLength cs := rfl
@[simp] theorem clockExcess_nil (a : ℝ) : clockExcess a [] = 0 := rfl
@[simp] theorem clockExcess_cons (a : ℝ) (c : HeatClock) (cs : List HeatClock) :
    clockExcess a (c::cs) = (c.mass-a)*c.time+clockExcess a cs := rfl

theorem clockLength_nonneg (cs : List HeatClock) : 0 ≤ clockLength cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih => exact add_nonneg c.time.coe_nonneg ih

theorem clockExcess_nonneg (a : ℝ) (cs : List HeatClock)
    (hc : ∀ c ∈ cs, a ≤ c.mass) : 0 ≤ clockExcess a cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hc c (List.mem_cons_self ..))) c.time.coe_nonneg)
      (ih (fun d hd => hc d (List.mem_cons_of_mem _ hd)))

theorem HeatJet.flatten_schedule_energy {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (cs : List HeatClock) (hc : ∀ c ∈ cs, c.mass ≤ 1)
    {a A : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hA0 : 0 ≤ A) (x : Fin 1 → ℝ) :
    |(J.schedule cs).observedSquare a A x-J.observedSquare a (A+clockLength cs) x| ≤
      4*clockLength cs := by
  induction cs generalizing A with
  | nil => simp only [HeatJet.schedule,clockLength_nil,add_zero,sub_self,abs_zero,mul_zero,le_refl]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, d.mass ≤ 1 := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    have hh := HeatJet.flatten_one_energy (hJ.schedule cs hcs) (hA.schedule cs) ha
      c.positive (hc c (List.mem_cons_self ..)) hA0 c.time.coe_nonneg x
    have hi := ih hcs (A:=A+c.time) (by positivity)
    have ht := (abs_sub_le ((J.schedule (c::cs)).observedSquare a A x)
      ((J.schedule cs).observedSquare a (A+c.time) x)
      (J.observedSquare a (A+c.time+clockLength cs) x)).trans (add_le_add hh hi)
    simpa only [clockLength_cons,add_assoc,mul_add] using ht

 

theorem HeatJet.flatten_schedule_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (cs : List HeatClock) {a A : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hc : ∀ c ∈ cs, a ≤ c.mass ∧ c.mass ≤ 1)
    (hA0 : 0 ≤ A) (x : Fin 1 → ℝ) :
    |clockContinuation a (J.schedule cs).F A x-clockContinuation a J.F (A+clockLength cs) x-
      (clockExcess a cs/2)*J.observedSquare a (A+clockLength cs) x| ≤
      2*clockLength cs*clockExcess a cs := by
  induction cs generalizing A with
  | nil => simp only [HeatJet.schedule,clockLength_nil,clockExcess_nil,add_zero,sub_self,
      zero_div,zero_mul,abs_zero,mul_zero,le_refl]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, a ≤ d.mass ∧ d.mass ≤ 1 := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    have hcc := hc c (List.mem_cons_self ..)
    have hh := HeatJet.flatten_one_error (hJ.schedule cs (fun d hd => (hcs d hd).2))
      (hA.schedule cs) ha ha1 c.positive hcc.2 hcc.1 hA0 c.time.coe_nonneg x
    have hi := ih hcs (A:=A+c.time) (by positivity)
    have he := HeatJet.flatten_schedule_energy hJ hA cs (fun d hd => (hcs d hd).2)
      ⟨ha.le,ha1⟩ (A:=A+c.time) (by positivity) x
    let F₀ := clockContinuation a (J.schedule (c::cs)).F A x
    let F₁ := clockContinuation a (J.schedule cs).F (A+c.time) x
    let F₂ := clockContinuation a J.F (A+c.time+clockLength cs) x
    let E₁ := (J.schedule cs).observedSquare a (A+c.time) x
    let E₂ := J.observedSquare a (A+c.time+clockLength cs) x
    let w := (c.mass-a)*(c.time:ℝ)
    have hw : 0 ≤ w := mul_nonneg (sub_nonneg.mpr hcc.1) c.time.coe_nonneg
    have hW : 0 ≤ clockExcess a cs := clockExcess_nonneg a cs (fun d hd => (hcs d hd).1)
    change |F₀-F₁-w/2*E₁| ≤ 2*(c.mass-a)*(c.time:ℝ)^2 at hh
    change |F₁-F₂-clockExcess a cs/2*E₂| ≤ _ at hi
    change |E₁-E₂| ≤ _ at he
    have h3 : |w/2*(E₁-E₂)| ≤ 2*w*clockLength cs := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ w/2)]
      calc
        _ ≤ w/2*(4*clockLength cs) := mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by ring
    have ht : |F₀-F₂-(w+clockExcess a cs)/2*E₂| ≤
        2*(c.mass-a)*(c.time:ℝ)^2+2*clockLength cs*clockExcess a cs+2*w*clockLength cs := by
      calc
        _ = |(F₀-F₁-w/2*E₁)+(F₁-F₂-clockExcess a cs/2*E₂)+w/2*(E₁-E₂)| := by congr 1; ring
        _ ≤ |F₀-F₁-w/2*E₁|+|F₁-F₂-clockExcess a cs/2*E₂|+|w/2*(E₁-E₂)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := add_le_add (add_le_add hh hi) h3
    have hb : 2*(c.mass-a)*(c.time:ℝ)^2+2*clockLength cs*clockExcess a cs+2*w*clockLength cs ≤
        2*((c.time:ℝ)+clockLength cs)*(w+clockExcess a cs) := by
      dsimp only [w]
      nlinarith [mul_nonneg c.time.coe_nonneg hW]
    simpa only [clockLength_cons,clockExcess_cons,add_assoc,F₀,F₂,E₂,w]
      using ht.trans hb

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

@[simp] theorem clockExcess_append (a : ℝ) (cs ds : List HeatClock) :
    clockExcess a (cs++ds) = clockExcess a cs+clockExcess a ds := by
  simp only [clockExcess,List.map_append,List.sum_append]

theorem PositiveMassProfile.grid_excess (α : PositiveMassProfile) (a l : ℝ) (t : ℝ≥0) (k : ℕ) :
    clockExcess a (α.grid l t k) = dyadicLowerSum (fun s => α.mass s-a) l t k := by
  induction k generalizing l t with
  | zero => simp [PositiveMassProfile.grid,clockExcess,dyadicLowerSum,mul_comm]
  | succ k ih => simp only [PositiveMassProfile.grid,clockExcess_append,ih,dyadicLowerSum]

theorem dyadicLowerSum_abs_sub {f g : ℝ → ℝ} {C : ℝ} (h : ∀ s, |f s-g s| ≤ C)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    |dyadicLowerSum f l t k-dyadicLowerSum g l t k| ≤ (t:ℝ)*C := by
  induction k generalizing l t with
  | zero =>
    simp only [dyadicLowerSum,← mul_sub,abs_mul,abs_of_nonneg t.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (h l) t.coe_nonneg
  | succ k ih =>
    simp only [dyadicLowerSum]
    have he : dyadicLowerSum f l (t/2) k+dyadicLowerSum f (l+t/2) (t/2) k-
        (dyadicLowerSum g l (t/2) k+dyadicLowerSum g (l+t/2) (t/2) k) =
        (dyadicLowerSum f l (t/2) k-dyadicLowerSum g l (t/2) k)+
        (dyadicLowerSum f (l+t/2) (t/2) k-dyadicLowerSum g (l+t/2) (t/2) k) := by ring
    rw [he]
    apply (abs_add_le _ _).trans ((add_le_add (ih l (t/2)) (ih (l+t/2) (t/2))).trans_eq _)
    simp only [NNReal.coe_div,NNReal.coe_ofNat]
    ring

theorem capped_grid_excess_tendsto (α : NonnegativeMassProfile) (a l : ℝ) (t : ℝ≥0) :
    Tendsto (fun k => clockExcess a ((α.cappedApprox k).grid l t k)) atTop
      (𝓝 (∫ s in l..l+t, α.mass s-a)) := by
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb (k : ℕ) :
      dist (clockExcess a ((α.cappedApprox k).grid l t k)) (∫ s in l..l+t, α.mass s-a) ≤
        (t:ℝ)*(1+α.mass (l+t)-α.mass l)*(1/2:ℝ)^k := by
    rw [PositiveMassProfile.grid_excess,Real.dist_eq]
    have h1 := dyadicLowerSum_abs_sub (f:=fun s => (α.cappedApprox k).mass s-a)
      (g:=fun s => α.mass s-a) (C:=(1/2:ℝ)^k) (fun s => by
        dsimp only [NonnegativeMassProfile.cappedApprox]
        rw [sub_sub_sub_cancel_right,abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
        exact sub_le_iff_le_add.mpr (max_le (by linarith [show 0 ≤ (1/2:ℝ)^k by positivity]) (by linarith [α.nonneg s]))) l t k
    have h2 := dyadicLowerSum_integral_error (show Monotone (fun s => α.mass s-a) from fun _ _ h => sub_le_sub_right (α.monotone h) a) l t k
    have ht := (abs_sub_le (dyadicLowerSum (fun s => (α.cappedApprox k).mass s-a) l t k)
      (dyadicLowerSum (fun s => α.mass s-a) l t k) (∫ s in l..l+t, α.mass s-a)).trans
      (add_le_add h1 (by simpa only [abs_sub_comm] using h2))
    apply ht.trans_eq
    ring
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) hb (by simpa only [mul_zero] using
    (hp.const_mul ((t:ℝ)*(1+α.mass (l+t)-α.mass l))))

 

theorem HeatJet.flatten_profile_error {J K : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {a A l : ℝ} (t : ℝ≥0) (ha : 0 < a) (ha1 : a ≤ 1) (hal : a ≤ α.mass l)
    (hA0 : 0 ≤ A) (hK : K.F = J.nonnegativeProfileValue α l t) (x : Fin 1 → ℝ) :
    |clockContinuation a K.F A x-clockContinuation a J.F (A+t) x-
      ((∫ s in l..l+t, α.mass s-a)/2)*J.observedSquare a (A+t) x| ≤
      2*(t:ℝ)*(∫ s in l..l+t, α.mass s-a) := by
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
  apply le_of_tendsto_of_tendsto ((ht.sub_const _).sub ((hw.div_const 2).mul_const _)).abs
    (hw.const_mul (2*(t:ℝ)))
  apply Eventually.of_forall
  intro k
  have hh := HeatJet.flatten_schedule_error hJ hA ((α.cappedApprox k).grid l t k) ha ha1
    (fun c hc => ⟨hal.trans ((le_max_left _ _).trans ((α.cappedApprox k).grid_mass_bounds l t k hc).1),
      ((α.cappedApprox k).grid_mass_bounds l t k hc).2.trans (α.cappedApprox_le_one hα k _)⟩) hA0 x
  simpa only [clockLength,PositiveMassProfile.grid_total_time] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarProfile_constant_head (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) {s : ℝ≥0} (hs : 0 < (s:ℝ)) (t : ℝ≥0) {m : ℝ} (hm : 0 < m)
    (hf : ∀ r ∈ Ico l (l+s), α.mass r = m) (x : Fin 1 → ℝ) :
    scalarTerminal.nonnegativeProfileValue α l (s+t) x =
      clockContinuation m (scalarProfileHeatJet α hα (l+s) t).F s x := by
  rw [scalarProfile_concat α hα]
  exact HeatJet.nonnegativeProfileValue_constant _ α hm l s hs hf x

noncomputable def scalarTailJet {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) : HeatJet 0 :=
  scalarProfileHeatJet (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
    (T*q) (Real.toNNReal (T*(1-q)))

theorem scalarTailJet_G_bound {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    ∀ i x, |(scalarTailJet hT α q).G i x| ≤ 1 :=
  scalarProfileHeatJet_G_bound _ _ _ _

theorem scalarTailJet_G_smooth {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    ∀ k i, BddSmooth k ((scalarTailJet hT α q).G i) := by
  intro k i
  exact scalarProfileJet_bddSmooth_all (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) k 0

theorem scalarParisiValue_constant_head {T q m : ℝ} (hT : 0 < T) (hq : q ∈ Ioc (0:ℝ) 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m) :
    scalarParisiValue hT α = clockContinuation m (scalarTailJet hT α q).F (T*q) 0-
      T/2*scalarPenalty α-T/4 := by
  have hs : 0 < T*q := mul_pos hT hq.1
  have ht : 0 ≤ T*(1-q) := mul_nonneg hT.le (sub_nonneg.mpr hq.2)
  have he : Real.toNNReal (T*q)+Real.toNNReal (T*(1-q)) = (⟨T,hT.le⟩:ℝ≥0) := by
    apply NNReal.eq
    change ((Real.toNNReal (T*q):ℝ)+(Real.toNNReal (T*(1-q)):ℝ)) = T
    rw [Real.coe_toNNReal _ hs.le,Real.coe_toNNReal _ ht]
    ring
  have hh := scalarProfile_constant_head (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) 0
    (s:=Real.toNNReal (T*q)) (by rwa [Real.coe_toNNReal _ hs.le])
    (Real.toNNReal (T*(1-q))) hm (by
      intro r hr
      change α.val (r/T) = m
      apply hf
      simp only [zero_add,Real.coe_toNNReal _ hs.le] at hr
      exact ⟨div_nonneg hr.1 hT.le,(div_lt_iff₀ hT).mpr (by nlinarith [hr.2])⟩) 0
  rw [he] at hh
  simp only [zero_add,Real.coe_toNNReal _ hs.le] at hh
  unfold scalarParisiValue
  rw [hh]
  rfl

 
theorem scalarHead_hasDerivAt {T q m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m < 1) :
    HasDerivAt (fun b => clockContinuation b (scalarTailJet hT α q).F (T*q) 0-
      T*b*q^2/4)
      ((1/2:ℝ)*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0)-T*q^2/4) m := by
  have hh := (scalarTailJet hT α q).hasDerivAt_mass_clockContinuation
    (scalarTailJet_G_smooth hT α q) (scalarTailJet_G_bound hT α q 0) hm hm1 (mul_nonneg hT.le hq) 0
  have he (s : ℝ) : (scalarTailJet hT α q).massEnergy m hm (T*q) s 0 =
      (scalarTailJet hT α q).filledSquare hm (T*q) s 0 := by
    unfold HeatJet.massEnergy HeatJet.filledSquare HeatJet.potentialEnergy
    congr 1
    funext y
    rw [Fin.sum_univ_one]
    rfl
  simp_rw [he] at hh
  convert hh.fun_sub ((hasDerivAt_id m).const_mul T |>.mul_const (q^2) |>.div_const 4) using 1 <;>
    first | rfl | simp only [mul_one]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def replaceHeadProfile (α : boundedMassProfiles) {q b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbq : b ≤ α.val q) : boundedMassProfiles :=
  ⟨fun s => if s < 0 then 0 else if s < q then b else α.val s, by
    constructor
    · intro s
      change (if s < 0 then 0 else if s < q then b else α.val s) ∈ Icc 0 1
      split_ifs <;> first | exact ⟨hb0,hb1⟩ | exact α.property.1 s | constructor <;> norm_num
    · intro s t hst
      change (if s < 0 then 0 else if s < q then b else α.val s) ≤
        (if t < 0 then 0 else if t < q then b else α.val t)
      by_cases hs : s < 0
      · rw [ite_eq_left hs]
        split_ifs <;> first | exact hb0 | exact (α.property.1 t).1 | exact le_rfl
      · rw [ite_eq_right hs]
        have ht : ¬ t < 0 := fun ht => hs (lt_of_le_of_lt hst ht)
        rw [ite_eq_right ht]
        by_cases hsq : s < q
        · rw [ite_eq_left hsq]
          split_ifs with htq
          · exact le_rfl
          · exact hbq.trans (α.property.2 (le_of_not_gt htq))
        · rw [ite_eq_right hsq, ite_eq_right (not_lt.mpr ((le_of_not_gt hsq).trans hst))]
          exact α.property.2 hst⟩

theorem replaceHeadProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {q b : ℝ} (hq : q ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbq : b ≤ α.val q) :
    replaceHeadProfile α hb0 hb1 hbq ∈ scalarProfiles := by
  constructor
  · intro s hs
    exact ite_eq_left hs
  · intro s hs
    change (if s < 0 then 0 else if s < q then b else α.val s) = 1
    rw [ite_eq_right (by linarith),ite_eq_right (by linarith)]
    exact hα.2 s hs

theorem replaceHeadProfile_head (α : boundedMassProfiles) {q b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbq : b ≤ α.val q) {s : ℝ} (hs : s ∈ Ico (0:ℝ) q) :
    (replaceHeadProfile α hb0 hb1 hbq).val s = b := by
  change (if s < 0 then 0 else if s < q then b else α.val s) = b
  rw [ite_eq_right (not_lt.mpr hs.1),ite_eq_left hs.2]

theorem replaceHeadProfile_tail (α : boundedMassProfiles) {q b : ℝ} (hq : 0 ≤ q)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbq : b ≤ α.val q) {s : ℝ} (hs : q ≤ s) :
    (replaceHeadProfile α hb0 hb1 hbq).val s = α.val s := by
  change (if s < 0 then 0 else if s < q then b else α.val s) = α.val s
  rw [ite_eq_right (not_lt.mpr (hq.trans hs)),ite_eq_right (not_lt.mpr hs)]

theorem scalarPenalty_head_difference (α : boundedMassProfiles) {q b m : ℝ}
    (hq : q ∈ Icc (0:ℝ) 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbq : b ≤ α.val q)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m) :
    scalarPenalty (replaceHeadProfile α hb0 hb1 hbq)-scalarPenalty α = (b-m)*q^2/2 := by
  let β := replaceHeadProfile α hb0 hb1 hbq
  have hαi := weightedProfile_monotone α
  have hβi := weightedProfile_monotone β
  have hh : (∫ s in (0:ℝ)..q, weightedProfile β s-weightedProfile α s) = (b-m)*q^2/2 := by
    trans ∫ s in (0:ℝ)..q, s*(b-m)
    · apply intervalIntegral.integral_congr_Ioo_of_le hq.1
      intro s hs
      change max s 0*β.val s-max s 0*α.val s = s*(b-m)
      rw [max_eq_left hs.1.le,hf s ⟨hs.1.le,hs.2⟩,
        replaceHeadProfile_head α hb0 hb1 hbq ⟨hs.1.le,hs.2⟩]
      ring
    · rw [intervalIntegral.integral_mul_const,integral_id]
      ring
  have ht : (∫ s in q..1, weightedProfile β s-weightedProfile α s) = 0 := by
    trans ∫ _s in q..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hq.2
      intro s hs
      change max s 0*β.val s-max s 0*α.val s = 0
      rw [replaceHeadProfile_tail α hq.1 hb0 hb1 hbq hs.1.le,sub_self]
    · simp
  unfold scalarPenalty
  rw [← intervalIntegral.integral_sub hβi.intervalIntegrable hαi.intervalIntegrable,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hβi.intervalIntegrable.sub hαi.intervalIntegrable)
      (hβi.intervalIntegrable.sub hαi.intervalIntegrable),hh,ht,add_zero]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_F {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) (x : Fin 1 → ℝ) :
    (scalarTailJet hT α q).F x = scalarTerminal.nonnegativeProfileValue
      (rescaledMassProfile α hT) (T*q) (Real.toNNReal (T*(1-q))) x :=
  scalarProfileHeatJet_F _ _ _ _ _

theorem scalarTailJet_congr {T q : ℝ} (hT : 0 < T) (hq : q ≤ 1)
    {α β : boundedMassProfiles} (he : ∀ r ∈ Ioc q 1, α.val r = β.val r) :
    (scalarTailJet hT α q).F = (scalarTailJet hT β q).F := by
  funext x
  rw [scalarTailJet_F,scalarTailJet_F]
  apply scalarTerminal.nonnegativeProfileValue_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  change α.val (s/T) = β.val (s/T)
  apply he
  simp only [Real.coe_toNNReal _ (mul_nonneg hT.le (sub_nonneg.mpr hq))] at hs
  constructor
  · exact (lt_div_iff₀ hT).mpr (by nlinarith [hs.1])
  · exact (div_le_iff₀ hT).mpr (by nlinarith [hs.2])

noncomputable def scalarHeadValue {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q b : ℝ) : ℝ := clockContinuation b (scalarTailJet hT α q).F (T*q) 0-T*b*q^2/4

theorem scalarHeadValue_hasDerivAt {T q m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m < 1) :
    HasDerivAt (scalarHeadValue hT α q)
      ((1/2:ℝ)*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0)-T*q^2/4) m :=
  scalarHead_hasDerivAt hT hq α hm hm1

theorem scalarParisiValue_replace_head {T q m b : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hm : 0 < m) (hb : 0 < b)
    (hb1 : b ≤ 1) (hbq : b ≤ α.val q) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m) :
    scalarParisiValue hT (replaceHeadProfile α hb.le hb1 hbq)-scalarParisiValue hT α =
      scalarHeadValue hT α q b-scalarHeadValue hT α q m := by
  have he : (scalarTailJet hT (replaceHeadProfile α hb.le hb1 hbq) q).F =
      (scalarTailJet hT α q).F := scalarTailJet_congr hT hq.2 (fun r hr =>
        replaceHeadProfile_tail α hq.1.le hb.le hb1 hbq hr.1.le)
  rw [scalarParisiValue_constant_head hT hq α hm hf,
    scalarParisiValue_constant_head hT hq _ hb (fun r hr =>
      replaceHeadProfile_head α hb.le hb1 hbq hr),he]
  have hp := scalarPenalty_head_difference α ⟨hq.1.le,hq.2⟩ hb.le hb1 hbq hf
  unfold scalarHeadValue
  nlinarith

 
theorem scalarMinimizer_head_derivative_nonpos {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (1/2:ℝ)*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0)-T*q^2/4 ≤ 0 := by
  have hmq : m ≤ α.val q := by
    rw [← hf 0 ⟨le_rfl,hq.1⟩]
    exact α.property.2 hq.1.le
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (scalarHeadValue_hasDerivAt hT hq.1.le α hm hm1)).1
  apply le_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ b : ℝ in 𝓝[<] m, 0 < b from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hm))] with b hbm hb
  have hb1 : b ≤ 1 := hbm.le.trans hm1.le
  have hbq : b ≤ α.val q := hbm.le.trans hmq
  have hh := hmin _ (replaceHeadProfile_mem hα hq.2 hb.le hb1 hbq)
  have he := scalarParisiValue_replace_head hT hq α hm hb hb1 hbq hf
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hbm.le)

 

theorem scalarMinimizer_atomic_head_balance {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hmq : m < α.val q)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    2*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0) = T*q^2 := by
  have hm1 : m < 1 := hmq.trans_le (α.property.1 q).2
  have hl : IsLocalMin (scalarHeadValue hT α q) m := by
    filter_upwards [Ioo_mem_nhds hm hmq] with b hb
    have hb1 : b ≤ 1 := hb.2.le.trans (α.property.1 q).2
    have hh := hmin _ (replaceHeadProfile_mem hα hq.2 hb.1.le hb1 hb.2.le)
    have he := scalarParisiValue_replace_head hT hq α hm hb.1 hb1 hb.2.le hf
    linarith
  have hz := hl.hasDerivAt_eq_zero (scalarHeadValue_hasDerivAt hT hq.1.le α hm hm1)
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
theorem scalarTailJet_error {T q r d : ℝ} (hT : 0 < T)
    (hq : q ≤ r) (hr : r ≤ 1) (α β : boundedMassProfiles)
    (hb : ∀ s ∈ Ioo q r, |β.val s-α.val s| ≤ d)
    (he : ∀ s ∈ Ioo r 1, β.val s = α.val s) (x : Fin 1 → ℝ) :
    |(scalarTailJet hT β q).F x-(scalarTailJet hT α q).F x| ≤ T/2*d*(r-q) := by
  have hq1 : q ≤ 1 := hq.trans hr
  have hqt : 0 ≤ T*(1-q) := mul_nonneg hT.le (sub_nonneg.mpr hq1)
  have hqr : T*q ≤ T*r := mul_le_mul_of_nonneg_left hq hT.le
  have hr1 : T*r ≤ T := by nlinarith
  let f := fun s => |β.val (s/T)-α.val (s/T)|
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    (((rescaledMassProfile β hT).monotone.intervalIntegrable).sub
      ((rescaledMassProfile α hT).monotone.intervalIntegrable)).abs
  have hfirst : (∫ s in T*q..T*r, f s) ≤ T*d*(r-q) := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) hqr (hfi _ _)
      (intervalIntegrable_const (c:=d)) (by
        intro s hs
        exact hb (s/T) ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hs.1]),
          (div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hh
    nlinarith
  have hlast : (∫ s in T*r..T, f s) = 0 := by
    trans ∫ _s in T*r..T, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hr1
      intro s hs
      dsimp [f]
      rw [he (s/T) ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hs.1]),
        (div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩,sub_self,abs_zero]
    · simp
  have hi : (∫ s in T*q..T, f s) ≤ T*d*(r-q) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi (T*q) (T*r)) (hfi (T*r) T),
      hlast,add_zero]
    exact hfirst
  have hh := scalarTerminal.nonnegativeProfileValue_L1_comparison (fun _ => 1)
    scalarTerminal_G_bound (rescaledMassProfile β hT) (rescaledMassProfile α hT)
    (T*q) (Real.toNNReal (T*(1-q))) x
  norm_num only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Nat.reduceAdd,nsmul_eq_mul,Nat.cast_one,one_mul,Real.coe_toNNReal _ hqt] at hh
  have heq : T*q+T*(1-q) = T := by ring
  rw [heq] at hh
  rw [scalarTailJet_F,scalarTailJet_F]
  change |_ - _| ≤ _
  change |_ - _| ≤ (1:ℝ)/2*(∫ s in T*q..T, f s) at hh
  linarith

theorem scalarPenalty_tail_error {q r m b d : ℝ}
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1) (α β : boundedMassProfiles)
    (hα : ∀ s ∈ Ico (0:ℝ) q, α.val s = m)
    (hβ : ∀ s ∈ Ico (0:ℝ) q, β.val s = b)
    (hb : ∀ s ∈ Ioo q r, |β.val s-α.val s| ≤ d)
    (he : ∀ s ∈ Ioo r 1, β.val s = α.val s) :
    |scalarPenalty β-scalarPenalty α-(b-m)*q^2/2| ≤ d*(r-q) := by
  let f := fun s => weightedProfile β s-weightedProfile α s
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    (weightedProfile_monotone β).intervalIntegrable.sub (weightedProfile_monotone α).intervalIntegrable
  have hh : (∫ s in (0:ℝ)..q, f s) = (b-m)*q^2/2 := by
    trans ∫ s in (0:ℝ)..q, s*(b-m)
    · apply intervalIntegral.integral_congr_Ioo_of_le hq
      intro s hs
      change max s 0*β.val s-max s 0*α.val s = s*(b-m)
      rw [max_eq_left hs.1.le,hα s ⟨hs.1.le,hs.2⟩,hβ s ⟨hs.1.le,hs.2⟩]
      ring
    · rw [intervalIntegral.integral_mul_const,integral_id]
      ring
  have ht : (∫ s in r..1, f s) = 0 := by
    trans ∫ _s in r..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hr
      intro s hs
      change max s 0*β.val s-max s 0*α.val s = 0
      rw [he s hs,sub_self]
    · simp
  have hm : |∫ s in q..r, f s| ≤ d*(r-q) := by
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) hqr (hfi q r).abs
      (intervalIntegrable_const (c:=d)) (fun s hs => by
        change |max s 0*β.val s-max s 0*α.val s| ≤ d
        have hs0 : 0 ≤ s := hq.trans hs.1.le
        rw [← mul_sub,max_eq_left hs0,abs_mul,abs_of_nonneg hs0]
        have hd : 0 ≤ d := (abs_nonneg _).trans (hb s hs)
        calc
          s*|β.val s-α.val s| ≤ s*d := mul_le_mul_of_nonneg_left (hb s hs) hs0
          _ ≤ d := by nlinarith [hs.2.le.trans hr])
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hm
    exact (intervalIntegral.abs_integral_le_integral_abs hqr).trans (by nlinarith)
  have heq : scalarPenalty β-scalarPenalty α =
      (b-m)*q^2/2+(∫ s in q..r, f s) := by
    unfold scalarPenalty
    rw [← intervalIntegral.integral_sub (weightedProfile_monotone β).intervalIntegrable
      (weightedProfile_monotone α).intervalIntegrable]
    change (∫ s in (0:ℝ)..1, f s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 q) (hfi q 1),hh,
      ← intervalIntegral.integral_add_adjacent_intervals (hfi q r) (hfi r 1),ht,add_zero]
  rw [heq,add_sub_cancel_left]
  exact hm

theorem scalarParisiValue_head_error {T q r m b d : ℝ} (hT : 0 < T)
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1) (α β : boundedMassProfiles)
    (hm : 0 < m) (hb0 : 0 < b)
    (hα : ∀ s ∈ Ico (0:ℝ) q, α.val s = m)
    (hβ : ∀ s ∈ Ico (0:ℝ) q, β.val s = b)
    (hb : ∀ s ∈ Ioo q r, |β.val s-α.val s| ≤ d)
    (he : ∀ s ∈ Ioo r 1, β.val s = α.val s) :
    |scalarParisiValue hT β-scalarParisiValue hT α-
      (scalarHeadValue hT α q b-scalarHeadValue hT α q m)| ≤ T*d*(r-q) := by
  have hp := clockContinuation_abs_sub_le (scalarTailJet hT β q).lipschitz
    (scalarTailJet hT α q).lipschitz hb0 (scalarTailJet_error hT hqr hr α β hb he) (T*q) 0
  have hpen := scalarPenalty_tail_error hq.le hqr hr α β hα hβ hb he
  rw [scalarParisiValue_constant_head hT ⟨hq,hqr.trans hr⟩ β hb0 hβ,
    scalarParisiValue_constant_head hT ⟨hq,hqr.trans hr⟩ α hm hα]
  unfold scalarHeadValue
  have heq : (clockContinuation b (scalarTailJet hT β q).F (T*q) 0-T/2*scalarPenalty β-T/4)-
      (clockContinuation m (scalarTailJet hT α q).F (T*q) 0-T/2*scalarPenalty α-T/4)-
      ((clockContinuation b (scalarTailJet hT α q).F (T*q) 0-T*b*q^2/4)-
      (clockContinuation m (scalarTailJet hT α q).F (T*q) 0-T*m*q^2/4)) =
      (clockContinuation b (scalarTailJet hT β q).F (T*q) 0-
      clockContinuation b (scalarTailJet hT α q).F (T*q) 0)-
      T/2*(scalarPenalty β-scalarPenalty α-(b-m)*q^2/2) := by ring
  rw [heq]
  calc
    |_ - _| ≤ |clockContinuation b (scalarTailJet hT β q).F (T*q) 0-
        clockContinuation b (scalarTailJet hT α q).F (T*q) 0|+
        |T/2*(scalarPenalty β-scalarPenalty α-(b-m)*q^2/2)| := abs_sub _ _
    _ ≤ T/2*d*(r-q)+(T/2)*(d*(r-q)) := by
      rw [abs_mul,abs_of_nonneg (div_nonneg hT.le (by norm_num))]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hpen (by positivity))
    _ = _ := by ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def floorMassProfile (α : boundedMassProfiles) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : boundedMassProfiles :=
  ⟨fun s => if s < 0 then 0 else max b (α.val s), by
    constructor
    · intro s
      change (if s < 0 then 0 else max b (α.val s)) ∈ Icc (0:ℝ) 1
      split_ifs
      · exact ⟨le_rfl,zero_le_one⟩
      · exact ⟨hb0.trans (le_max_left _ _),max_le hb1 (α.property.1 s).2⟩
    · intro s t hst
      change (if s < 0 then 0 else max b (α.val s)) ≤ (if t < 0 then 0 else max b (α.val t))
      by_cases hs : s < 0
      · rw [ite_eq_left hs]
        split_ifs
        · exact le_rfl
        · exact hb0.trans (le_max_left _ _)
      · rw [ite_eq_right hs,ite_eq_right (fun ht => hs (lt_of_le_of_lt hst ht))]
        exact max_le_max_left b (α.property.2 hst)⟩

theorem floorMassProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : floorMassProfile α hb0 hb1 ∈ scalarProfiles := by
  constructor
  · intro s hs; exact ite_eq_left hs
  · intro s hs
    change (if s < 0 then 0 else max b (α.val s)) = 1
    rw [ite_eq_right (by linarith),hα.2 s hs,max_eq_right hb1]

theorem floorMassProfile_head (α : boundedMassProfiles) {q m b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hmb : m ≤ b)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m) {s : ℝ} (hs : s ∈ Ico (0:ℝ) q) :
    (floorMassProfile α hb0 hb1).val s = b := by
  change (if s < 0 then 0 else max b (α.val s)) = b
  rw [ite_eq_right (not_lt.mpr hs.1),hf s hs,max_eq_left hmb]

theorem floorMassProfile_tail (α : boundedMassProfiles) {r b : ℝ}
    (hr : 0 ≤ r) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbr : b ≤ α.val r)
    {s : ℝ} (hs : r ≤ s) : (floorMassProfile α hb0 hb1).val s = α.val s := by
  change (if s < 0 then 0 else max b (α.val s)) = α.val s
  rw [ite_eq_right (not_lt.mpr (hr.trans hs)),max_eq_right (hbr.trans (α.property.2 hs))]

theorem floorMassProfile_bound (α : boundedMassProfiles) {m b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hmb : m ≤ b) {s : ℝ} (hs : 0 ≤ s) (hms : m ≤ α.val s) :
    |(floorMassProfile α hb0 hb1).val s-α.val s| ≤ b-m := by
  change |(if s < 0 then 0 else max b (α.val s))-α.val s| ≤ b-m
  rw [ite_eq_right (not_lt.mpr hs),abs_of_nonneg (sub_nonneg.mpr (le_max_right _ _))]
  exact sub_le_iff_le_add.mpr (max_le (by linarith) (by linarith))

end SKFluctuations.Hierarchy

end

end OAI
