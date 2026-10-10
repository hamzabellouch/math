import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SignedRemainder
import OAI.Analysis.VlasovMaxwell.Geometry.ArrivalDomain
import OAI.Analysis.VlasovMaxwell.Geometry.BallCutoff

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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def phaseAcceleration (E B : Field) (α : Phase → ℝ → Phase) (z : Phase) (t : ℝ) : Vec :=
  fderiv ℝ velocity (α z t).2 (E (t,(α z t).1)+cross (velocity (α z t).2) (B (t,(α z t).1)))

lemma PhaseFlowOn.velocity_hasDerivAt {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) (ht : t∈Ioo 0 T) :
    HasDerivAt (fun r => velocity (F.flow z r).2) (phaseAcceleration E B F.flow z t) t := by
  have hd := ((F.ode z t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).snd
  exact ((contDiff_velocity (k:=1)).differentiable one_ne_zero (F.flow z t).2).hasFDerivAt.comp_hasDerivAt t hd

lemma PhaseFlowOn.branchDirection_hasDerivAt {E B : Field} {T s : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hs : s∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1≠(F.flow zY s).1) :
    HasDerivAt (branchDirection F.flow zX zY T)
      ((branchTime F.flow zX zY T s-s)⁻¹ •
        coneMotion (velocity (F.flow zX (branchTime F.flow zX zY T s)).2)
          (velocity (F.flow zY s).2) (branchDirection F.flow zX zY T s)) s := by
  let t := branchTime F.flow zX zY T s
  have ht := F.branch_time_mem zX zY hs hne
  have hti : t∈Ioo 0 T := ⟨hs.1.1.trans ht.1,ht.2⟩
  have hg : (F.flow zX t).1-(F.flow zY s).1=(t-s) • branchDirection F.flow zX zY T s := by
    unfold branchDirection
    rw [smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr ht.1.ne'),one_smul]
  exact hasDerivAt_cone_direction rfl ht.1 hg
    (((F.ode zX t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).fst)
    (((F.ode zY s (Ioo_subset_Icc_self hs.1)).hasDerivAt (Icc_mem_nhds hs.1.1 hs.1.2)).fst)
    (F.branch_differential zX zY hs hne).2

lemma PhaseFlowOn.actual_signed_identity {E B : Field} {T s : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hs : s∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1≠(F.flow zY s).1) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ => τ σ-σ
    let a := fun σ => velocity (F.flow zX (τ σ)).2
    let u := fun σ => velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    signedForceKernel (r s) (a s) (u s) (n s) (phaseAcceleration E B F.flow zY s) =
      -deriv (fun σ => retardedPrimitive (r σ) (a σ) (u σ) (n σ)) s+
        signedRemainder (r s) (a s) (u s) (n s) (phaseAcceleration E B F.flow zX (τ s)) := by
  let τ := branchTime F.flow zX zY T
  let r := fun σ => τ σ-σ
  let a := fun σ => velocity (F.flow zX (τ σ)).2
  let u := fun σ => velocity (F.flow zY σ).2
  let n := branchDirection F.flow zX zY T
  have ht := F.branch_time_mem zX zY hs hne
  have hτ := (F.branch_differential zX zY hs hne).2
  have hr : HasDerivAt r ((1-dot (n s) (u s))/(1-dot (n s) (a s))-1) s :=
    hτ.sub (hasDerivAt_id s)
  have ha : HasDerivAt a
      (((1-dot (n s) (u s))/(1-dot (n s) (a s))) • phaseAcceleration E B F.flow zX (τ s)) s :=
    (F.velocity_hasDerivAt zX ⟨hs.1.1.trans ht.1,ht.2⟩).scomp s hτ
  have hu := F.velocity_hasDerivAt zY hs.1
  have hn := F.branchDirection_hasDerivAt zX zY hs hne
  have hnorm := F.branchDirection_norm zX zY hs hne
  have hd := (cone_denom_pos (F.flow zY s).2 (n s) hnorm).ne'
  have hD := (cone_denom_pos (F.flow zX (τ s)).2 (n s) hnorm).ne'
  have hh := signed_force_identity_along_branch hr ha hu hn
    (sub_ne_zero.mpr ht.1.ne') hd hD
  simpa only [signedRemainder,add_assoc] using hh

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace RVM

def DyadicWindow (k n : ℕ) (x : ℝ) : Prop :=
  1/(2:ℝ)^k ≤ (2:ℝ)^n*x ∧ (2:ℝ)^n*x ≤ (2:ℝ)^k

lemma dyadicWindow_index_le {k n m : ℕ} {x : ℝ}
    (hn : DyadicWindow k n x) (hm : DyadicWindow k m x) : m≤n+2*k := by
  have hpk : 0<(2:ℝ)^k := by positivity
  have hx : 0≤x := by
    by_contra hh
    have he := mul_neg_of_pos_of_neg (by positivity : 0<(2:ℝ)^n) (lt_of_not_ge hh)
    have hp : 0<1/(2:ℝ)^k := by positivity
    linarith [hn.1]
  by_contra hnm
  have hi : n+(2*k+1) ≤ m := by omega
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hi) hx
  have hlo : 2*(2:ℝ)^k ≤ (2:ℝ)^(n+(2*k+1))*x := by
    calc
      _ = (1/(2:ℝ)^k)*(2:ℝ)^(2*k+1) := by
        rw [pow_add,show 2*k=k*2 from Nat.mul_comm _ _,pow_mul]; norm_num; field_simp
      _ ≤ ((2:ℝ)^n*x)*(2:ℝ)^(2*k+1) :=
        mul_le_mul_of_nonneg_right hn.1 (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hh := hlo.trans (he.trans hm.2)
  linarith

lemma dyadicWindow_card_le (k : ℕ) (S : Finset ℕ) {x : ℝ}
    (hS : ∀ n∈S, DyadicWindow k n x) : S.card≤4*k+1 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨n,hn⟩ := hs
    have hsub : S⊆Finset.Icc (n-2*k) (n+2*k) := by
      intro m hm
      have hlo := dyadicWindow_index_le (hS m hm) (hS n hn)
      have hhi := dyadicWindow_index_le (hS n hn) (hS m hm)
      exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hh
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

lemma dyadicWindow_pair_card_le (k : ℕ) (S : Finset (ℕ × ℕ)) {x y : ℝ}
    (hS : ∀ n∈S, DyadicWindow k n.1 x ∧ DyadicWindow k n.2 y) :
    S.card≤(4*k+1)^2 := by
  classical
  let A := S.image Prod.fst
  let B := S.image Prod.snd
  have hA : A.card≤4*k+1 := by
    apply dyadicWindow_card_le
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (hS m hm).1
  have hB : B.card≤4*k+1 := by
    apply dyadicWindow_card_le
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (hS m hm).2
  have hsub : S⊆A×ˢ B := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,
      Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  calc
    _ ≤ (A×ˢ B).card := Finset.card_le_card hsub
    _ = A.card*B.card := Finset.card_product _ _
    _ ≤ (4*k+1)*(4*k+1) := Nat.mul_le_mul hA hB
    _ = _ := (pow_two _).symm

lemma measurableSet_dyadicWindow (k n : ℕ) : MeasurableSet {x : ℝ | DyadicWindow k n x} :=
  ((isClosed_le continuous_const (continuous_const.mul continuous_id)).inter
    (isClosed_le (continuous_const.mul continuous_id) continuous_const)).measurableSet

def sameTimeBudgetSet (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (n : ℕ × ℕ) : Set (ℝ × Phase) :=
  {p | p.1∈Ioo 0 T ∧ DyadicWindow k n.1 (q p.2.2)⁻¹ ∧
    DyadicWindow k n.2 ‖velocity p.2.2-velocity (α zX p.1).2‖}

def arrivalFinalDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Vec) :=
  {p | p.1∈Ioo 0 T ∧ p.1+‖(α zX T).1-p.2‖=T}

def arrivalBudgetSet (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (n : ℕ × ℕ) : Set (ℝ × Phase) :=
  {p | DyadicWindow k n.1 (q p.2.2)⁻¹ ∧
    (( (p.1,p.2.1)∈arrivalDomain α zX T ∧
      DyadicWindow k n.2 (Real.sqrt ((1-dot (arrivalDirection α zX T (p.1,p.2.1))
        (arrivalVelocity α zX T (p.1,p.2.1)))/2))) ∨
    ((p.1,p.2.1)∈arrivalFinalDomain α zX T ∧
      DyadicWindow k n.2 (Real.sqrt ((1-dot ((T-p.1)⁻¹ • ((α zX T).1-p.2.1))
        (velocity (α zX T).2))/2))))}

lemma PhaseFlowOn.measurable_sameTimeBudgetSet {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : ℕ) (n : ℕ × ℕ) :
    MeasurableSet (sameTimeBudgetSet F.flow zX T k n) := by
  classical
  let U : Set (ℝ × Phase) := {p | p.1∈Ioo 0 T}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  have hc : ContinuousOn (fun p : ℝ × Phase => ‖velocity p.2.2-velocity (F.flow zX p.1).2‖) U := by
    intro p hp
    have hX := ((F.continuousOn_time zX).snd.continuousAt (Icc_mem_nhds hp.1 hp.2)).comp continuousAt_fst
    exact (((contDiff_velocity (k:=1)).continuous.continuousAt.comp (continuousAt_snd.snd)).sub
      ((contDiff_velocity (k:=1)).continuous.continuousAt.comp hX)).norm.continuousWithinAt
  have hm : Measurable (U.piecewise
      (fun p : ℝ × Phase => ‖velocity p.2.2-velocity (F.flow zX p.1).2‖) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hU.measurableSet
  have hq : Measurable (fun p : ℝ × Phase => (q p.2.2)⁻¹) :=
    ((contDiff_q (k:=1)).continuous.measurable.comp (measurable_snd.snd)).inv
  have hh := hU.measurableSet.inter ((measurableSet_dyadicWindow k n.1).preimage hq |>.inter
    ((measurableSet_dyadicWindow k n.2).preimage hm))
  convert hh using 1
  ext p
  constructor
  · rintro ⟨hp,hq,hb⟩
    refine ⟨hp,hq,?_⟩
    change DyadicWindow k n.2 (U.piecewise
      (fun p : ℝ × Phase => ‖velocity p.2.2-velocity (F.flow zX p.1).2‖) (fun _ => (0:ℝ)) p)
    rw [piecewise_eq_of_mem U _ _ (show p∈U from hp)]
    exact hb
  · rintro ⟨hp,hq,hb⟩
    change DyadicWindow k n.2 (U.piecewise
      (fun p : ℝ × Phase => ‖velocity p.2.2-velocity (F.flow zX p.1).2‖) (fun _ => (0:ℝ)) p) at hb
    rw [piecewise_eq_of_mem U _ _ hp] at hb
    exact ⟨hp,hq,hb⟩

lemma PhaseFlowOn.measurable_arrivalBudgetSet {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : ℕ) (n : ℕ × ℕ) :
    MeasurableSet (arrivalBudgetSet F.flow zX T k n) := by
  classical
  let U := arrivalDomain F.flow zX T
  let b : ℝ × Vec → ℝ := fun p => Real.sqrt ((1-dot
    (arrivalDirection F.flow zX T p) (arrivalVelocity F.flow zX T p))/2)
  have hb : ContinuousOn b U := by
    intro p hp
    exact (((continuousAt_const.sub (continuous_dot.continuousAt.comp ((F.arrivalDirection_continuousAt zX hp).prodMk
      (F.arrivalVelocity_continuousAt zX hp)))).div_const 2).sqrt).continuousWithinAt
  have hm : Measurable (U.indicator b) := hb.measurable_piecewise continuousOn_const
    (F.isOpen_arrivalDomain zX).measurableSet
  have hopen : MeasurableSet {p | p∈U ∧ DyadicWindow k n.2 (b p)} := by
    convert (F.isOpen_arrivalDomain zX).measurableSet.inter
      ((measurableSet_dyadicWindow k n.2).preimage hm) using 1
    ext p
    change (p∈U ∧ DyadicWindow k n.2 (b p)) ↔
      (p∈U ∧ DyadicWindow k n.2 (U.indicator b p))
    by_cases hp : p∈U <;> simp [hp]
  have hfinal : MeasurableSet (arrivalFinalDomain F.flow zX T) :=
    (measurable_fst (measurableSet_Ioo)).inter
      (measurableSet_eq_fun (measurable_fst.add (measurable_const.sub measurable_snd).norm) measurable_const)
  have hbfinal : Measurable (fun p : ℝ × Vec => Real.sqrt ((1-dot
      ((T-p.1)⁻¹ • ((F.flow zX T).1-p.2)) (velocity (F.flow zX T).2))/2)) := by
    unfold dot
    fun_prop
  have hq : Measurable (fun p : ℝ × Phase => (q p.2.2)⁻¹) :=
    ((contDiff_q (k:=1)).continuous.measurable.comp (measurable_snd.snd)).inv
  exact (measurableSet_dyadicWindow k n.1).preimage hq |>.inter
    ((hopen.union (hfinal.inter ((measurableSet_dyadicWindow k n.2).preimage hbfinal))).preimage
      (measurable_fst.prodMk measurable_snd.fst))

lemma dyadicWindow_sum_indicator {α : Type*} (k : ℕ) (S : Finset (ℕ × ℕ))
    (G : ℕ × ℕ → Set α) (p : α) (e : ℝ≥0∞) {x y : ℝ}
    (hG : ∀ n∈S, p∈G n → DyadicWindow k n.1 x ∧ DyadicWindow k n.2 y) :
    (∑ n∈S, (G n).indicator (fun _ => e) p) ≤ ((4*k+1)^2 : ℕ)*e := by
  classical
  have hc : (S.filter (fun n => p∈G n)).card≤(4*k+1)^2 := by
    apply dyadicWindow_pair_card_le
    intro n hn
    exact hG n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  have heq : (∑ n∈S, (G n).indicator (fun _ => e) p)=
      (S.filter (fun n => p∈G n)).card*e := by
    simp only [Set.indicator]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [heq]
  exact mul_le_mul' (by exact_mod_cast hc) le_rfl

lemma jointBudget_pointwise (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (S : Finset (ℕ × ℕ)) (p : ℝ × Phase) (e : ℝ≥0∞) :
    (∑ n∈S, ((sameTimeBudgetSet α zX T k n).indicator (fun _ => e) p+
      (arrivalBudgetSet α zX T k n).indicator (fun _ => e) p)) ≤
      (3*(4*k+1)^2 : ℕ)*e := by
  classical
  let G₁ := sameTimeBudgetSet α zX T k
  let G₂ : ℕ × ℕ → Set (ℝ × Phase) := fun n =>
    {r | DyadicWindow k n.1 (q r.2.2)⁻¹ ∧
      (r.1,r.2.1)∈arrivalDomain α zX T ∧
      DyadicWindow k n.2 (Real.sqrt ((1-dot (arrivalDirection α zX T (r.1,r.2.1))
        (arrivalVelocity α zX T (r.1,r.2.1)))/2))}
  let G₃ : ℕ × ℕ → Set (ℝ × Phase) := fun n =>
    {r | DyadicWindow k n.1 (q r.2.2)⁻¹ ∧
      (r.1,r.2.1)∈arrivalFinalDomain α zX T ∧
      DyadicWindow k n.2 (Real.sqrt ((1-dot ((T-r.1)⁻¹ • ((α zX T).1-r.2.1))
        (velocity (α zX T).2))/2))}
  have h₁ := dyadicWindow_sum_indicator k S G₁ p e
    (fun n _ hn => hn.2)
  have h₂ := dyadicWindow_sum_indicator k S G₂ p e
    (fun n _ hn => ⟨hn.1,hn.2.2⟩)
  have h₃ := dyadicWindow_sum_indicator k S G₃ p e
    (fun n _ hn => ⟨hn.1,hn.2.2⟩)
  have hpart (n : ℕ × ℕ) : (arrivalBudgetSet α zX T k n).indicator (fun _ => e) p ≤
      (G₂ n).indicator (fun _ => e) p+(G₃ n).indicator (fun _ => e) p := by
    by_cases hp : p∈arrivalBudgetSet α zX T k n
    · rw [indicator_of_mem hp]
      rcases hp.2 with h|h
      · have hh : p∈G₂ n := ⟨hp.1,h⟩
        rw [indicator_of_mem hh]
        exact le_add_right le_rfl
      · have hh : p∈G₃ n := ⟨hp.1,h⟩
        rw [indicator_of_mem hh]
        exact le_add_left le_rfl
    · rw [indicator_of_notMem hp]; exact zero_le
  calc
    _ ≤ ∑ n∈S, ((G₁ n).indicator (fun _ => e) p+
        ((G₂ n).indicator (fun _ => e) p+(G₃ n).indicator (fun _ => e) p)) :=
      Finset.sum_le_sum (fun n _ => add_le_add le_rfl (hpart n))
    _ = (∑ n∈S, (G₁ n).indicator (fun _ => e) p)+
        ((∑ n∈S, (G₂ n).indicator (fun _ => e) p)+(∑ n∈S, (G₃ n).indicator (fun _ => e) p)) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ ((4*k+1)^2:ℕ)*e+(((4*k+1)^2:ℕ)*e+((4*k+1)^2:ℕ)*e) := add_le_add h₁ (add_le_add h₂ h₃)
    _ = _ := by push_cast; ring

def prefixPhaseEnergy (s : Solution) (T : ℝ) : ℝ × Phase → ℝ≥0∞ :=
  (Icc 0 T ×ˢ (univ : Set Phase)).indicator (fun p => ENNReal.ofReal (q p.2.2*s.f p))

lemma EnergyPrefix.measurable_prefixPhaseEnergy {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) : Measurable (prefixPhaseEnergy s T) := by
  classical
  have hc : ContinuousOn (fun p : ℝ × Phase => ENNReal.ofReal (q p.2.2*s.f p))
      (Icc 0 T ×ˢ (univ : Set Phase)) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((((contDiff_q (k:=1)).continuous.comp (continuous_snd.snd)).continuousOn).mul hs.f_smooth.continuousOn)
  unfold prefixPhaseEnergy
  convert hc.measurable_piecewise (continuousOn_const (c:=(0:ℝ≥0∞)))
    (measurableSet_Icc.prod MeasurableSet.univ) using 1
  ext p
  by_cases hp : p∈Icc 0 T ×ˢ (univ : Set Phase)
  · rw [indicator_of_mem hp,piecewise_eq_of_mem _ _ _ hp]
  · rw [indicator_of_notMem hp,piecewise_eq_of_notMem _ _ _ hp]

def jointEnergyBudget (s : Solution) (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (a b I : ℝ) (n : ℕ × ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
    (sameTimeBudgetSet α zX T k n).indicator (prefixPhaseEnergy s T) (t,z)+
    (arrivalBudgetSet α zX T k n).indicator (prefixPhaseEnergy s T) (t,z)

lemma jointEnergyBudget_eq {s : Solution} {α : Phase → ℝ → Phase} {zX : Phase} {T : ℝ}
    (k : ℕ) {a b I : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T) (n : ℕ × ℕ) :
    jointEnergyBudget s α zX T k a b I n =
      (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
        (sameTimeBudgetSet α zX T k n).indicator (fun p => ENNReal.ofReal (q p.2.2*s.f p)) (t,z)+
        (arrivalBudgetSet α zX T k n).indicator (fun p => ENNReal.ofReal (q p.2.2*s.f p)) (t,z) := by
  unfold jointEnergyBudget
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply lintegral_congr
  intro z
  have he : prefixPhaseEnergy s T (t,z)=ENNReal.ofReal (q z.2*s.f (t,z)) :=
    by simp only [prefixPhaseEnergy,indicator_of_mem (show (t,z)∈Icc 0 T ×ˢ (univ : Set Phase) from ⟨hJ ht,mem_univ _⟩)]
  by_cases h₁ : (t,z)∈sameTimeBudgetSet α zX T k n <;>
    by_cases h₂ : (t,z)∈arrivalBudgetSet α zX T k n <;> simp [h₁,h₂,he]

lemma PhaseFlowOn.jointEnergyBudget_sum_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (k : ℕ) {a b I : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T) (S : Finset (ℕ × ℕ)) :
    ∑ n∈S, jointEnergyBudget s F.flow zX T k a b I n ≤
      (ENNReal.ofReal I)⁻¹ * (3*(4*k+1)^2:ℕ) * ENNReal.ofReal (b-a) *
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  classical
  let g : ℕ × ℕ → ℝ × Phase → ℝ≥0∞ := fun n p =>
    (sameTimeBudgetSet F.flow zX T k n).indicator (prefixPhaseEnergy s T) p+
    (arrivalBudgetSet F.flow zX T k n).indicator (prefixPhaseEnergy s T) p
  have hg (n : ℕ × ℕ) : Measurable (g n) :=
    ((hs.measurable_prefixPhaseEnergy).indicator (F.measurable_sameTimeBudgetSet zX k n)).add
      ((hs.measurable_prefixPhaseEnergy).indicator (F.measurable_arrivalBudgetSet zX k n))
  have hint (t : ℝ) (ht : t∈Icc a b) :
      (∫⁻ z : Phase, ∑ n∈S, g n (t,z)) ≤ (3*(4*k+1)^2:ℕ)*
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
    calc
      _ ≤ ∫⁻ z : Phase, (3*(4*k+1)^2:ℕ)*prefixPhaseEnergy s T (t,z) :=
        lintegral_mono (fun z => jointBudget_pointwise F.flow zX T k S (t,z) (prefixPhaseEnergy s T (t,z)))
      _ = (3*(4*k+1)^2:ℕ)*(∫⁻ z : Phase, ENNReal.ofReal (q z.2*s.f (t,z))) := by
        rw [lintegral_const_mul' _ _ (by finiteness)]
        congr 1
        apply lintegral_congr
        intro z
        simp only [prefixPhaseEnergy,indicator_of_mem
          (show (t,z)∈Icc 0 T ×ˢ (univ : Set Phase) from ⟨hJ ht,mem_univ _⟩)]
      _ ≤ _ := mul_le_mul' le_rfl (hs.phase_energy_bound (hJ ht))
  have heq : (∑ n∈S, jointEnergyBudget s F.flow zX T k a b I n)=
      (ENNReal.ofReal I)⁻¹*(∫⁻ t in Icc a b, ∫⁻ z : Phase, ∑ n∈S, g n (t,z)) := by
    change (∑ n∈S, (ENNReal.ofReal I)⁻¹*(∫⁻ t in Icc a b, ∫⁻ z : Phase, g n (t,z))) = _
    rw [← Finset.mul_sum]
    congr 1
    rw [← lintegral_finsetSum S (fun n _ => (hg n).lintegral_prod_right')]
    apply lintegral_congr
    intro t
    exact (lintegral_finsetSum S (fun n _ => (hg n).comp (measurable_const.prodMk measurable_id))).symm
  rw [heq]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * (∫⁻ t in Icc a b,
        (3*(4*k+1)^2:ℕ)*ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x))) :=
      mul_le_mul' le_rfl (lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hint))
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      ac_rfl

lemma PhaseFlowOn.jointEnergyBudget_tsum_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (k : ℕ) {a b I : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T) :
    ∑' n : ℕ × ℕ, jointEnergyBudget s F.flow zX T k a b I n ≤
      (ENNReal.ofReal I)⁻¹ * (3*(4*k+1)^2:ℕ) * ENNReal.ofReal (b-a) *
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (F.jointEnergyBudget_sum_bound hs zX k hJ)

lemma PhaseFlowOn.jointEnergyBudget_uniform {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (k : ℕ) {a b I C : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T)
    (hI : 0<I) (hC : 0≤C) (hlen : b-a≤C*I) :
    ∑' n : ℕ × ℕ, jointEnergyBudget s F.flow zX T k a b I n ≤
      (3*(4*k+1)^2:ℕ) * ENNReal.ofReal C *
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  have hnorm : (ENNReal.ofReal I)⁻¹ * ENNReal.ofReal (b-a)≤ENNReal.ofReal C := by
    calc
      _ ≤ (ENNReal.ofReal I)⁻¹ * ENNReal.ofReal (C*I) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlen)
      _ = ENNReal.ofReal C := by
        rw [ENNReal.ofReal_mul hC,mul_left_comm,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top,mul_one]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * (3*(4*k+1)^2:ℕ) * ENNReal.ofReal (b-a) *
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) :=
      F.jointEnergyBudget_tsum_bound hs zX k hJ
    _ = (3*(4*k+1)^2:ℕ) * ((ENNReal.ofReal I)⁻¹ * ENNReal.ofReal (b-a)) *
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hnorm) le_rfl

lemma PhaseFlowOn.jointEnergyBudget_finite {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (k : ℕ) {a b I : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T) (hI : 0<I) :
    (∑' n : ℕ × ℕ, jointEnergyBudget s F.flow zX T k a b I n)≠⊤ := by
  apply ne_top_of_le_ne_top _ (F.jointEnergyBudget_tsum_bound hs zX k hJ)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hI).ne')
      (ENNReal.natCast_ne_top _)) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

end RVM

end

end OAI
