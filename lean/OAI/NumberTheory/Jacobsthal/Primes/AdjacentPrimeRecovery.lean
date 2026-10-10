import OAI.NumberTheory.Jacobsthal.Probability.FiniteHistoryPairLaw
import OAI.NumberTheory.Jacobsthal.Probability.SourceThresholdCoupling
import OAI.NumberTheory.Jacobsthal.Probability.SuccessfulMarkedCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistoryPrefixOrder

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualCouplingUpdates
open FiniteHistoryTransport ActualCoupledHistories

variable {w ell S : ℝ} {start : Node}

def prefixRel : ChainState w ell S start → ChainState w ell S start → Prop
  | _,none => True
  | none,some _ => False
  | some a,some b => ∃ tail : List ℕ,b.primes = a.primes++tail

theorem prefixRel_refl (p : ChainState w ell S start) : prefixRel p p := by
  cases p with
  | none => trivial
  | some p => exact ⟨[],by simp⟩

theorem prefixRel_trans {p q r : ChainState w ell S start} (hp : prefixRel p q) (hq : prefixRel q r) :
    prefixRel p r := by
  cases r with
  | none => trivial
  | some r =>
    cases q with
    | none => exact False.elim hq
    | some q =>
      cases p with
      | none => exact False.elim hp
      | some p =>
        obtain ⟨u,hu⟩ := hp
        obtain ⟨v,hv⟩ := hq
        exact ⟨u++v,by rw [hv,hu,List.append_assoc]⟩

theorem actual_row_prefixRel (p : ChainState w ell S start) :
    ∀ᵐ q ∂chain w ell S start p, prefixRel p q := by
  cases p with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (by trivial)).mpr trivial
  | some p =>
    filter_upwards [prime_follows p] with q hq
    cases q with
    | none => trivial
    | some q =>
      obtain ⟨a,ha,rfl⟩ := hq
      exact ⟨[a],rfl⟩

def orderedPast (N : ℕ) (h : Hist (ChainState w ell S start) N) : Prop :=
  ∀ i j : Finset.Iic N, i.1 ≤ j.1 → prefixRel (h i) (h j)

theorem orderedPast_measurable (N : ℕ) :
    MeasurableSet {h : Hist (ChainState w ell S start) N | orderedPast N h} :=
  (Set.to_countable _).measurableSet

theorem orderedPast_extend (N : ℕ) (h : Hist (ChainState w ell S start) N)
    (q : ChainState w ell S start) (hp : orderedPast N h) (hq : prefixRel (last N h) q) :
    orderedPast (N+1) (FiniteHistoryTransport.extend N h q) := by
  intro ⟨i,hi⟩ ⟨j,hj⟩ hij
  have hi' := Finset.mem_Iic.mp hi
  have hj' := Finset.mem_Iic.mp hj
  by_cases hjN : j ≤ N
  · have hiN : i ≤ N := hij.trans hjN
    rw [extend_previous N h q ⟨i,Finset.mem_Iic.mpr hiN⟩,
      extend_previous N h q ⟨j,Finset.mem_Iic.mpr hjN⟩]
    exact hp _ _ hij
  · have hjEq : j = N+1 := by omega
    subst j
    change prefixRel _ (last (N+1) (FiniteHistoryTransport.extend N h q))
    rw [extend_last]
    by_cases hiN : i ≤ N
    · rw [extend_previous N h q ⟨i,Finset.mem_Iic.mpr hiN⟩]
      exact prefixRel_trans (hp ⟨i,Finset.mem_Iic.mpr hiN⟩ ⟨N,by simp⟩ hiN) hq
    · have hiEq : i = N+1 := by omega
      subst i
      change prefixRel (last (N+1) (FiniteHistoryTransport.extend N h q)) q
      rw [extend_last]
      exact prefixRel_refl q

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hs hsS

theorem actual_history_ordered (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty), orderedPast N h := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => some History.empty), orderedPast 0 h
    exact (ae_dirac_iff (orderedPast_measurable 0)).mpr (fun _ _ _ => prefixRel_refl _)
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (orderedPast_measurable (N+1))
    filter_upwards [ih] with h hh
    filter_upwards [actual_row_prefixRel (last N h)] with q hq
    exact orderedPast_extend N h q hh hq

end NumberTheoryLean.PrimeHistoryPrefixOrder

end

section

namespace NumberTheoryLean.PriorPrimeWindow

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open FiniteHistoryTransport ActualCoupledHistories PrimeHistoryPrefixOrder
open ActualProcessCoupling ActualSuccessfulHistories SuccessfulMarkedCoordinates ArrivalKernelGeometry

def hasPrimeWindow (w b₀ b₁ : ℝ) (start : Node) (ps : List ℕ) : Prop :=
  ∃ pre tail : List ℕ, ps = pre++tail ∧ primeWindow b₀ b₁ (terminal w start pre)

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_ordered (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      orderedPast N (mapHist (fun q => q.1.1) N h) := by
  have hm := orderedPast_measurable (w:=w) (ell:=ell) (S:=S) (start:=start) N
  have hp : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (mapHist (fun q => q.1.1) N), orderedPast N h := by
    rw [sourceHistoryLaw_prime]
    exact actual_history_ordered hw hell hS0 hS hr hs hsS N
  exact (ae_map_iff (mapHist_measurable (by exact measurable_fst.comp measurable_fst) N).aemeasurable hm).mp hp

theorem sourceHistory_prior_live (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ i j : Finset.Iic N, i.1 ≤ j.1 → ∀ p : History w ell S start,
      (h j).1.1 = some p → ∃ q : History w ell S start,
        (h i).1.1 = some q ∧ ∃ tail : List ℕ,p.primes = q.primes++tail := by
  filter_upwards [sourceHistory_ordered hw hell hS0 hS hr hs hsS mesh N] with h hh
  intro i j hij p hp
  have hrel := hh i j hij
  change prefixRel (h i).1.1 (h j).1.1 at hrel
  rw [hp] at hrel
  cases hq : (h i).1.1 with
  | none => rw [hq] at hrel; exact False.elim hrel
  | some q =>
    rw [hq] at hrel
    exact ⟨q,rfl,hrel⟩

theorem sourceHistory_prior_mark (hc : Consistent start)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2 = false → ∀ i j : Finset.Iic N, i.1 ≤ j.1 →
      ∀ p : History w ell S start, (h j).1.1 = some p → ∀ z : CostState,
      (h i).1.2 = Sum.inl z → ∀ b₀ b₁ : ℝ, 0 < b₀ →
      stateSide z.1 = .even → 209/100 ≤ stateRatio z.1 → stateRatio z.1 ≤ 213/100 →
      10*b₀/(313/100) ≤ currentExponent (Real.log start.gap) z →
      currentExponent (Real.log start.gap) z ≤ b₁/(309/100) →
      hasPrimeWindow w b₀ b₁ start p.primes := by
  filter_upwards [sourceHistory_prior_live hw hell hS0 hS hr hs hsS mesh N,
    sourceHistory_transports_marked_window hw hell hS0 hS hr hs hsS hc hm hmesh N herror] with h hp hmks
  intro hflag i j hij p hpj z hzi b₀ b₁ hb₀ heven ht₀ ht₁ hx₀ hx₁
  obtain ⟨q,hqi,hwin⟩ := hmks hflag i z hzi b₀ b₁ hb₀ heven ht₀ ht₁ hx₀ hx₁
  obtain ⟨q',hqi',tail,happend⟩ := hp i j hij p hpj
  have heq : q' = q := Option.some.inj (hqi'.symm.trans hqi)
  subst q'
  exact ⟨q.primes,tail,happend,hwin⟩

end NumberTheoryLean.PriorPrimeWindow

end

section

namespace NumberTheoryLean.PrimePrefixRecovery
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open FiniteHistoryTransport ActualCoupledHistories FlaggedSourceStart ActualProcessCoupling
open PriorPrimeWindow SourceThresholdCoupling ReconstructedParentCoupling

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_stages (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,∀ j : Finset.Iic N,
      stage j.1 (h j).1.1 := by
  apply ae_all_iff.mpr
  intro j
  have hP : MeasurableSet {q : PersistentFailureFlag.FlagState (JointState w ell S start) | stage j.1 q.1.1} :=
    (measurable_fst.comp measurable_fst) (stage_measurable j.1)
  have hc : Measurable (fun h : Hist (PersistentFailureFlag.FlagState (JointState w ell S start)) N => h j) :=
    measurable_pi_apply j
  apply (ae_map_iff hc.aemeasurable hP).mp
  rw [sourceHistoryLaw_coordinate hw hell hS0 hS hr hs hsS mesh N j.1 (Finset.mem_Iic.mp j.2)]
  have hh : ∀ᵐ p ∂(sourceLaw hw hell hS0 hS hr hs hsS mesh j.1).map (fun q => q.1.1),stage j.1 p := by
    rw [sourceLaw_prime hw hell hS0 hS hr hs hsS mesh j.1]
    exact pathLaw_stage j.1
  exact (ae_map_iff (measurable_fst.comp measurable_fst).aemeasurable (stage_measurable j.1)).mp hh

theorem sourceHistory_recovers_prefix (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p →
      ∀ pre tail : List ℕ,p.primes=pre++tail →
      ∃ hk : pre.length ≤ N,∃ q : History w ell S start,
        (h ⟨pre.length,Finset.mem_Iic.mpr hk⟩).1.1=some q ∧ q.primes=pre := by
  filter_upwards [sourceHistory_stages hw hell hS0 hS hr hs hsS mesh N,
    sourceHistory_prior_live hw hell hS0 hS hr hs hsS mesh N] with h hstage hprior
  intro j p hp pre tail hword
  have hlen : p.primes.length=j.1 := by
    have hh := hstage j
    rw [hp] at hh
    exact hh
  have hprej : pre.length ≤ j.1 := by rw [hword,List.length_append] at hlen; omega
  have hpreN := hprej.trans (Finset.mem_Iic.mp j.2)
  let i : Finset.Iic N := ⟨pre.length,Finset.mem_Iic.mpr hpreN⟩
  obtain ⟨q,hq,suf,hsuf⟩ := hprior i j hprej p hp
  have hqlen : q.primes.length=pre.length := by
    have hh := hstage i
    rw [hq] at hh
    exact hh
  have htakeP : p.primes.take pre.length=pre := by rw [hword]; simp
  have htakeQ : p.primes.take q.primes.length=q.primes := by rw [hsuf]; simp
  rw [hqlen] at htakeQ
  exact ⟨hpreN,q,hq,htakeQ.symm.trans htakeP⟩

def hasNearThresholdPrefix (w d : ℝ) (start : Node) (ps : List ℕ) : Prop :=
  ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ≠ [] ∧ primeNearThreshold d (terminal w start pre)

theorem recovered_near_prefix_occurs (mesh d : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p →
        hasNearThresholdPrefix w d start p.primes → primeThresholdOccurs d N h := by
  filter_upwards [sourceHistory_recovers_prefix hw hell hS0 hS hr hs hsS mesh N] with h hh
  intro j p hp hnear
  obtain ⟨pre,tail,hword,hne,hbad⟩ := hnear
  obtain ⟨hk,q,hq,hqpre⟩ := hh j p hp pre tail hword
  have hlen : 1 ≤ pre.length := List.length_pos_iff.mpr hne
  let k : Fin N := ⟨pre.length-1,by omega⟩
  refine ⟨k,?_⟩
  have he : k.1+1=pre.length := by dsimp [k]; omega
  change nearPrimeNode d ((h ⟨k.1+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.1)
  have hcoord : (h ⟨k.1+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.1=some q := by
    simpa only [he] using hq
  rw [hcoord]
  change primeNearThreshold d (terminal w start q.primes)
  rw [hqpre]
  exact hbad
end NumberTheoryLean.PrimePrefixRecovery

end

section

namespace NumberTheoryLean.AdjacentPrimeRecovery
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw ActualCoupledHistories
open PrimePrefixRecovery PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_recovers_adjacent (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p →
      ∀ pre : List ℕ,∀ a b : ℕ,∀ tail : List ℕ,p.primes=pre++a::b::tail →
      ∃ k : Fin N,∃ q r : History w ell S start,
        (atIndex N h k.castSucc).1.1=some q ∧ (atIndex N h k.succ).1.1=some r ∧
        q.primes=pre++[a] ∧ r.primes=(pre++[a])++[b] := by
  filter_upwards [sourceHistory_recovers_prefix hw hell hS0 hS hr hs hsS mesh N] with h hh
  intro j p hp pre a b tail hword
  have hparent : p.primes=(pre++[a])++(b::tail) := by simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hword
  have hchild : p.primes=((pre++[a])++[b])++tail := by simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hword
  obtain ⟨hqN,q,hq,hqword⟩ := hh j p hp (pre++[a]) (b::tail) hparent
  obtain ⟨hrN,r,hr,hrword⟩ := hh j p hp ((pre++[a])++[b]) tail hchild
  have hlen : ((pre++[a])++[b]).length=(pre++[a]).length+1 := by simp
  let k : Fin N := ⟨(pre++[a]).length,by omega⟩
  refine ⟨k,q,r,hq,?_,hqword,hrword⟩
  change (h ⟨(pre++[a]).length+1,Finset.mem_Iic.mpr (by omega)⟩).1.1=some r
  simpa only [hlen] using hr
end NumberTheoryLean.AdjacentPrimeRecovery

end

end Erdos970

end OAI
