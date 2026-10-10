import OAI.NumberTheory.Jacobsthal.Probability.ActualCouplingError

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PersistentFailureFlag

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open ActualCouplingFinite

variable {α : Type*} [MeasurableSpace α]

abbrev FlagState (α : Type*) := α × Bool

noncomputable def badBit (Bad : α → Prop) (x : α) : Bool := by
  classical
  exact if Bad x then true else false

theorem badBit_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (badBit Bad) := by
  classical
  exact Measurable.ite hBad measurable_const measurable_const

noncomputable def update (Bad : α → Prop) (z : FlagState α × α) : FlagState α :=
  (z.2,z.1.2 || badBit Bad z.2)

theorem update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (update Bad) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_snd.prodMk (hor.comp ((measurable_snd.comp measurable_fst).prodMk
    ((badBit_measurable hBad).comp measurable_snd)))

noncomputable def marked (K : Kernel α α) {Bad : α → Prop} (_hBad : MeasurableSet {x | Bad x}) :
    Kernel (FlagState α) (FlagState α) :=
  (Kernel.id ×ₖ (K.comap Prod.fst measurable_fst)).map (update Bad)

instance marked_isMarkov (K : Kernel α α) [IsMarkovKernel K]
    {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : IsMarkovKernel (marked K hBad) := by
  unfold marked
  exact Kernel.IsMarkovKernel.map _ (update_measurable hBad)

theorem marked_apply (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) {B : Set (FlagState α)} (hB : MeasurableSet B) :
    marked K hBad z B = K z.1 {y | (y,z.2 || badBit Bad y) ∈ B} := by
  rw [marked,Kernel.map_apply' _ (update_measurable hBad) _ hB,
    Kernel.prod_apply' _ _ _ ((update_measurable hBad) hB),Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left ((update_measurable hBad) hB)

theorem row_update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) (b : Bool) :
    Measurable (fun y : α => (y,b || badBit Bad y)) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_id.prodMk (hor.comp (measurable_const.prodMk (badBit_measurable hBad)))

theorem marked_eq_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    marked K hBad z = (K z.1).map (fun y => (y,z.2 || badBit Bad y)) := by
  apply Measure.ext
  intro B hB
  rw [marked_apply K hBad z hB,Measure.map_apply (row_update_measurable hBad z.2) hB]
  rfl

theorem marked_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) : (marked K hBad z).map Prod.fst = K z.1 := by
  rw [marked_eq_map K hBad z,Measure.map_map (f:=fun y => (y,z.2 || badBit Bad y))
    (g:=Prod.fst) measurable_fst (row_update_measurable hBad z.2)]
  exact Measure.map_id

def failed : Set (FlagState α) := {z | z.2 = true}

theorem failed_measurable : MeasurableSet (failed (α:=α)) :=
  measurable_snd (measurableSet_singleton true)

theorem marked_failed_true (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) : marked K hBad (x,true) failed = 1 := by
  rw [marked_apply K hBad (x,true) failed_measurable]
  simp [failed]

theorem marked_failed_false (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) : marked K hBad (x,false) failed = K x {y | Bad y} := by
  classical
  rw [marked_apply K hBad (x,false) failed_measurable]
  congr 1
  ext y
  simp [failed,badBit]

instance marked_pow_markov (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) : IsMarkovKernel ((marked K hBad)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (FlagState α) (FlagState α)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    rw [hp]
    infer_instance

theorem marked_power_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (z : FlagState α) :
    (((marked K hBad)^n) z).map Prod.fst = (K^n) z.1 :=
  map_power_of_step (marked K hBad) K measurable_fst (marked_map K hBad) n z

noncomputable def law (K : Kernel α α) {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x})
    (x : α) (n : ℕ) : Measure (FlagState α) := ((marked K hBad)^n) (x,false)

instance law_probability (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) : IsProbabilityMeasure (law K hBad x n) := by
  unfold law
  infer_instance

end NumberTheoryLean.PersistentFailureFlag



namespace NumberTheoryLean.FailureFlagBounds

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

def surviving (Good : α → Prop) (z : FlagState α) : Prop := z.2 = false → Good z.1

theorem surviving_measurable {Good : α → Prop} (hGood : MeasurableSet {x | Good x}) :
    MeasurableSet {z | surviving Good z} :=
  (measurable_snd (measurableSet_singleton false)).imp (measurable_fst hGood)

theorem surviving_step (K : Kernel α α) [IsMarkovKernel K] {Bad P Q : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (hQ : MeasurableSet {x | Q x})
    (hstep : ∀ x,P x → ∀ᵐ y ∂K x, ¬Bad y → Q y) (z : FlagState α) (hz : surviving P z) :
    ∀ᵐ y ∂marked K hBad z, surviving Q y := by
  classical
  rw [marked_eq_map K hBad z]
  apply (ae_map_iff (row_update_measurable hBad z.2).aemeasurable (surviving_measurable hQ)).mpr
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    filter_upwards [hstep x (hz rfl)] with y hy
    intro hf
    apply hy
    simpa [badBit] using hf
  | true =>
    exact Eventually.of_forall (fun y => by
      intro hf
      have hf' : (true || badBit Bad y) = false := hf
      simp at hf')

theorem law_survives (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (Good : ℕ → α → Prop)
    (hGood : ∀ n,MeasurableSet {x | Good n x})
    (hstep : ∀ n x,Good n x → ∀ᵐ y ∂K x, ¬Bad y → Good (n+1) y)
    (x : α) (hx : Good 0 x) (n : ℕ) :
    ∀ᵐ z ∂law K hBad x n, surviving (Good n) z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (x,false), surviving (Good 0) z
    exact (ae_dirac_iff (surviving_measurable (hGood 0))).mpr (fun _ => hx)
  | succ n ih =>
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((marked K hBad)^(n+1)) (x,false), surviving (Good (n+1)) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (surviving_measurable (hGood (n+1)))
    filter_upwards [ih] with z hz
    exact surviving_step K hBad (hGood (n+1)) (hstep n) z hz

theorem marked_failure_row_bound (K : Kernel α α) [IsMarkovKernel K] {Bad Good : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (η : ℝ≥0∞)
    (hrow : ∀ x,Good x → K x {y | Bad y} ≤ η) (z : FlagState α) (hz : surviving Good z) :
    marked K hBad z failed ≤ failed.indicator (fun _ => (1:ℝ≥0∞)) z+η := by
  classical
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    rw [marked_failed_false,indicator_of_notMem (show (x,false) ∉ (failed:Set (FlagState α)) by change ¬(false=true); decide),zero_add]
    exact hrow x (hz rfl)
  | true =>
    rw [marked_failed_true,indicator_of_mem (show (x,true) ∈ (failed:Set (FlagState α)) from rfl)]
    exact le_add_of_nonneg_right zero_le

theorem law_failure_step (K : Kernel α α) [IsMarkovKernel K] {Bad Good : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) (η : ℝ≥0∞)
    (hgood : ∀ᵐ z ∂law K hBad x n, surviving Good z)
    (hrow : ∀ y,Good y → K y {z | Bad z} ≤ η) :
    law K hBad x (n+1) failed ≤ law K hBad x n failed+η := by
  have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
  calc
    _ = ∫⁻ z,marked K hBad z failed ∂law K hBad x n := by
      change ((marked K hBad)^(n+1)) (x,false) failed = _
      rw [hp,Kernel.comp_apply' _ _ _ failed_measurable]
      rfl
    _ ≤ ∫⁻ z,(failed.indicator (fun _ => (1:ℝ≥0∞)) z+η) ∂law K hBad x n := by
      apply lintegral_mono_ae
      filter_upwards [hgood] with z hz
      exact marked_failure_row_bound K hBad η hrow z hz
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator failed_measurable),
        lintegral_indicator failed_measurable,setLIntegral_const,one_mul,lintegral_const,measure_univ,mul_one]

theorem failure_probability_le (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (Good : ℕ → α → Prop)
    (hGood : ∀ n,MeasurableSet {x | Good n x})
    (hstep : ∀ n x,Good n x → ∀ᵐ y ∂K x, ¬Bad y → Good (n+1) y)
    (x : α) (hx : Good 0 x) (η : ℝ≥0∞) (N : ℕ)
    (hrow : ∀ n < N, ∀ y,Good n y → K y {z | Bad z} ≤ η)
    (n : ℕ) (hn : n ≤ N) : law K hBad x n failed ≤ (n:ℝ≥0∞)*η := by
  classical
  induction n with
  | zero =>
    rw [Nat.cast_zero,zero_mul]
    change Measure.dirac (x,false) failed ≤ 0
    rw [Measure.dirac_apply' _ failed_measurable]
    change (if (x,false) ∈ (failed:Set (FlagState α)) then 1 else 0) ≤ 0
    simp [failed]
  | succ n ih =>
    calc
      _ ≤ law K hBad x n failed+η := law_failure_step K hBad x n η
        (law_survives K hBad Good hGood hstep x hx n) (hrow n (by omega))
      _ ≤ (n:ℝ≥0∞)*η+η := add_le_add (ih (by omega)) le_rfl
      _ = _ := by rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

end NumberTheoryLean.FailureFlagBounds



namespace NumberTheoryLean.FullHistoryFailureFlag

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FiniteHistoryTransport PersistentFailureFlag

variable {X : Type*} [MeasurableSpace X]

def noResetPath (n : ℕ) (h : Hist (FlagState X) n) : Prop :=
  ∀ j : Finset.Iic n, (last n h).2 = false → (h j).2 = false

theorem noResetPath_measurable (n : ℕ) : MeasurableSet {h : Hist (FlagState X) n | noResetPath n h} := by
  simp only [noResetPath,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact ((measurable_snd.comp (last_measurable n)) (measurableSet_singleton false)).imp
    ((measurable_snd.comp (measurable_pi_apply j)) (measurableSet_singleton false))

theorem noResetPath_extend (n : ℕ) (h : Hist (FlagState X) n) (y : FlagState X)
    (hh : noResetPath n h) (hy : y.2 = false → (last n h).2 = false) :
    noResetPath (n+1) (extend n h y) := by
  intro ⟨j,hj⟩ hflag
  rw [extend_last] at hflag
  have hj' := Finset.mem_Iic.mp hj
  by_cases hle : j ≤ n
  · rw [extend_previous n h y ⟨j,Finset.mem_Iic.mpr hle⟩]
    exact hh _ (hy hflag)
  · have heq : j = n+1 := by omega
    subst j
    change (last (n+1) (FiniteHistoryTransport.extend n h y)).2 = false
    rw [extend_last]
    exact hflag

theorem marked_no_reset (K : Kernel X X) [IsMarkovKernel K] {Bad : X → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState X) :
    ∀ᵐ y ∂marked K hBad z, y.2 = false → z.2 = false := by
  have hP : MeasurableSet {y : FlagState X | y.2 = false → z.2 = false} :=
    (measurable_snd (measurableSet_singleton false)).imp (by by_cases hz : z.2 = false <;> simp [hz])
  rw [marked_eq_map K hBad z]
  apply (ae_map_iff (row_update_measurable hBad z.2).aemeasurable hP).mpr
  apply Filter.Eventually.of_forall
  intro y
  cases z.2 <;> simp

theorem marked_history_no_reset (K : Kernel X X) [IsMarkovKernel K] {Bad : X → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : X) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (marked K hBad) N (fun _ => (x,false)), noResetPath N h := by
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => (x,false)), noResetPath 0 h
    exact (ae_dirac_iff (noResetPath_measurable 0)).mpr (fun _ _ => rfl)
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (noResetPath_measurable (N+1))
    filter_upwards [ih] with h hh
    filter_upwards [marked_no_reset K hBad (last N h)] with y hy
    exact noResetPath_extend N h y hh hy

end NumberTheoryLean.FullHistoryFailureFlag



namespace NumberTheoryLean.ActualFlagInvariant

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ActualCouplingUpdates ActualCouplingFinite
open PersistentFailureFlag FailureFlagBounds RegeneratingInverseBands ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}

def mismatch (mesh : ℝ) (q : JointState w ell S start) : Prop :=
  primeLabel w ell S mesh start q.1 ≠ continuousLabel S mesh q.2

theorem mismatch_measurable (mesh : ℝ) : MeasurableSet {q : JointState w ell S start | mismatch mesh q} := by
  let D : Set (MeshRatioLabels.Label S mesh × MeshRatioLabels.Label S mesh) := {p | p.1 ≠ p.2}
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  exact (((primeLabel_measurable w ell S mesh start).comp measurable_fst).prodMk
    ((continuousLabel_measurable S mesh).comp measurable_snd)) hD

def liveGood (v mesh : ℝ) (n : ℕ) (h : History w ell S start) (z : CostState) : Prop :=
  stateRatio z.1 ≤ S ∧ h.node.side = stateSide z.1 ∧ |h.node.ratio-stateRatio z.1| ≤ mesh ∧
    |Real.log h.node.gap-Real.log (gapValue v z)| ≤ 4*(n:ℝ)*mesh

def GoodAt (v mesh : ℝ) (n : ℕ) : JointState w ell S start → Prop
  | (none,.inr _) => True
  | (some h,.inl z) => liveGood v mesh n h z
  | _ => False

theorem liveGood_measurable (v mesh : ℝ) (n : ℕ) (h : History w ell S start) :
    MeasurableSet {z | liveGood v mesh n h z} := by
  have hside : MeasurableSet {z : CostState | h.node.side = stateSide z.1} := by
    have heq : {z : CostState | h.node.side = stateSide z.1} = {z : CostState | stateSide z.1 = h.node.side} := by
      ext z
      exact eq_comm
    rw [heq]
    exact measurable_fst (side_set_measurable h.node.side)
  exact (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).inter
    (hside.inter ((measurableSet_le
      (measurable_const.sub (stateRatio_measurable.comp measurable_fst)).abs measurable_const).inter
      (measurableSet_le (measurable_const.sub (Real.measurable_log.comp (gapValue_measurable v))).abs measurable_const)))

theorem GoodAt_measurable (v mesh : ℝ) (n : ℕ) :
    MeasurableSet {q : JointState w ell S start | GoodAt v mesh n q} := by
  apply Measurable.setOf
  apply measurable_from_prod_countable_right
  intro p
  cases p with
  | none => exact measurable_const.sumElim measurable_const
  | some h => exact (measurableSet_setOfPred.mp (liveGood_measurable v mesh n h)).sumElim measurable_const

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_dead_ae (v mesh : ℝ) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead),
      q = (none,CemeteryKernel.dead) := by
  have hL : ∀ᵐ p ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead)).map Prod.fst, p = none := by
    rw [jointKernel_left hw hell hS0 hS hr hs hsS,chain_none]
    exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
  have hdead : MeasurableSet {y : CemeteryKernel.Space CostState | y = CemeteryKernel.dead} := by
    apply measurableSet_sum_iff.mpr
    constructor
    · have hp : (Sum.inl : CostState → CemeteryKernel.Space CostState) ⁻¹' {y | y = CemeteryKernel.dead} = ∅ := by
        ext x
        change ((Sum.inl x : CemeteryKernel.Space CostState) = Sum.inr ()) ↔ False
        simp
      rw [hp]
      exact MeasurableSet.empty
    · simp [CemeteryKernel.dead]
  have hR : ∀ᵐ y ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead)).map Prod.snd,
      y = CemeteryKernel.dead := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    change ∀ᵐ y ∂Measure.dirac (CemeteryKernel.dead : CemeteryKernel.Space CostState), y = CemeteryKernel.dead
    exact (ae_dirac_iff hdead).mpr rfl
  have hl := (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton _)).mp hL
  have hr' := (ae_map_iff measurable_snd.aemeasurable hdead).mp hR
  filter_upwards [hl,hr'] with q hq hq'
  exact Prod.ext hq hq'

theorem actual_good_step (v : ℝ) {mesh : ℝ} (hm : 0 < mesh) (n : ℕ)
    (q : JointState w ell S start) (hq : GoodAt v mesh n q) :
    ∀ᵐ y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh q,
      ¬mismatch mesh y → GoodAt v mesh (n+1) y := by
  rcases q with ⟨p,z⟩
  cases p with
  | none =>
    cases z with
    | inl z => exact False.elim hq
    | inr u =>
      cases u
      filter_upwards [joint_dead_ae hw hell hS0 hS hr hs hsS v mesh] with y hy
      intro _
      rw [hy]
      trivial
  | some h =>
    cases z with
    | inr u => exact False.elim hq
    | inl z =>
      filter_upwards [joint_follows hw hell hS0 hS hr hs hsS v mesh h z,
        joint_matching_control hw hell hS0 hS hr hs hsS v hm (some h) (.inl z),
        joint_continuous_supported hw hell hS0 hS hr hs hsS v mesh (some h) (.inl z)] with y hy hmatch hSup
      intro hnot
      have heq : primeLabel w ell S mesh start y.1 = continuousLabel S mesh y.2 := not_ne_iff.mp hnot
      have hmout := hmatch heq
      rcases y with ⟨p,y⟩
      cases p with
      | none =>
        cases y with
        | inl y => exact False.elim hmout
        | inr u => trivial
      | some k =>
        cases y with
        | inr u => exact False.elim hmout
        | inl y =>
          have hup := matched_live_update hell hr hs h k z y hy.1 hy.2 hq.2.1 hq.2.2.2
            (show |k.node.ratio-stateRatio y.1| ≤ mesh from hmout.le)
          refine ⟨hSup,hup.1,hmout.le,?_⟩
          have he : 4*(n:ℝ)*mesh+4*mesh = 4*((n+1:ℕ):ℝ)*mesh := by push_cast; ring
          exact hup.2.trans_eq he

noncomputable def flaggedKernel (v mesh : ℝ) :
    Kernel (FlagState (JointState w ell S start)) (FlagState (JointState w ell S start)) :=
  marked (jointKernel hw hell hS0 hS hr hs hsS v mesh) (mismatch_measurable mesh)

instance flaggedKernel_markov (v mesh : ℝ) :
    IsMarkovKernel (flaggedKernel hw hell hS0 hS hr hs hsS v mesh) := by
  unfold flaggedKernel
  infer_instance

theorem actual_flagged_invariant (v : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (q : JointState w ell S start) (hq : GoodAt v mesh 0 q) (n : ℕ) :
    ∀ᵐ y ∂law (jointKernel hw hell hS0 hS hr hs hsS v mesh) (mismatch_measurable mesh) q n,
      y.2 = false → GoodAt v mesh n y.1 :=
  law_survives _ (mismatch_measurable mesh) (GoodAt v mesh) (GoodAt_measurable v mesh)
    (actual_good_step hw hell hS0 hS hr hs hsS v hm) q hq n

end NumberTheoryLean.ActualFlagInvariant



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

def typedState : (i : Side) → (s : ℝ) → Valid i s → State
  | .even,s,hs => .inl ⟨s,hs⟩
  | .odd,s,hs => .inr ⟨s,hs⟩

theorem typedState_side (i : Side) (s : ℝ) (hs : Valid i s) : stateSide (typedState i s hs) = i := by
  cases i <;> rfl

theorem typedState_ratio (i : Side) (s : ℝ) (hs : Valid i s) : stateRatio (typedState i s hs) = s := by
  cases i <;> rfl

variable {w ell S : ℝ} {start : Node}

def sourceCostState (hs : Valid start.side start.ratio) : CostState :=
  (typedState start.side start.ratio hs,0)

def sourceJoint (w ell S : ℝ) (start : Node) (hs : Valid start.side start.ratio) : JointState w ell S start :=
  (some History.empty,.inl (sourceCostState hs))

theorem source_gap (hr : 0 < start.gap) (hs : Valid start.side start.ratio) :
    gapValue (Real.log start.gap) (sourceCostState hs) = start.gap := by
  simp [gapValue,sourceCostState,Real.exp_log hr]

theorem source_good {mesh : ℝ} (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (hm : 0 ≤ mesh) :
    GoodAt (Real.log start.gap) mesh 0 (sourceJoint w ell S start hs) := by
  change liveGood (Real.log start.gap) mesh 0 History.empty (sourceCostState hs)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [sourceCostState,typedState_ratio] using hsS
  · change start.side = stateSide (typedState start.side start.ratio hs)
    exact (typedState_side _ _ _).symm
  · change |start.ratio-stateRatio (typedState start.side start.ratio hs)| ≤ mesh
    rw [typedState_ratio,sub_self,abs_zero]
    exact hm
  · rw [Nat.cast_zero,mul_zero,zero_mul]
    change |Real.log start.gap-Real.log (gapValue (Real.log start.gap) (sourceCostState hs))| ≤ 0
    simp [gapValue,sourceCostState]

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def sourceLaw (mesh : ℝ) (n : ℕ) : Measure (FlagState (JointState w ell S start)) :=
  law (jointKernel hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh) (mismatch_measurable mesh)
    (sourceJoint w ell S start hs) n

instance sourceLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceLaw
  infer_instance

theorem sourceLaw_joint (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst =
      jointPathLaw hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh (sourceCostState hs) n :=
  marked_power_map _ (mismatch_measurable mesh) n (sourceJoint w ell S start hs,false)

theorem sourceLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.1) = pathLaw w ell S start n := by
  calc
    _ = ((sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst).map Prod.fst :=
      (Measure.map_map (f:=Prod.fst) (g:=Prod.fst) measurable_fst measurable_fst).symm
    _ = _ := by rw [sourceLaw_joint,jointPathLaw_prime]

theorem sourceLaw_continuous (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.2) =
      ((continuousChain (Real.log start.gap) ell S)^n) (.inl (sourceCostState hs)) := by
  calc
    _ = ((sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst).map Prod.snd :=
      (Measure.map_map (f:=Prod.fst) (g:=Prod.snd) measurable_snd measurable_fst).symm
    _ = _ := by rw [sourceLaw_joint,jointPathLaw_continuous]

theorem sourceLaw_good {mesh : ℝ} (hm : 0 < mesh) (n : ℕ) :
    ∀ᵐ q ∂sourceLaw hw hell hS0 hS hr hs hsS mesh n,
      q.2 = false → GoodAt (Real.log start.gap) mesh n q.1 :=
  actual_flagged_invariant hw hell hS0 hS hr hs hsS (Real.log start.gap) hm
    (sourceJoint w ell S start hs) (source_good hs hsS hm.le) n

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
