import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Endpoints

namespace OAI

namespace MatchingFPRAS.Counting

theorem trial_output_error (K : ℕ) (hK : 1 ≤ K) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (Z : ℕ → ℝ)
    (hZ : ∀ j, 0 < Z j) (estimates : Fin K → ℝ)
    (herr : ∀ j, |estimates j/(Z (j.val+1)/Z j.val)-1| ≤ epsilon/(100*K)) :
    (1-epsilon/100)*Z K ≤ productEstimate (Z 0) estimates ∧
    productEstimate (Z 0) estimates ≤ (1+epsilon/50)*Z K := by
  let f : Fin K → ℝ := fun j => estimates j/(Z (j.val+1)/Z j.val)
  have hprod := stage_product_error K hK epsilon he he1 f herr
  have hid : productEstimate (Z 0) estimates = (∏ j, f j)*Z K := by
    rw [show (∏ j, f j)=(∏ j, estimates j)/(∏ j : Fin K, Z (j.val+1)/Z j.val) from
      Finset.prod_div_distrib _ _]
    rw [positive_telescope Z hZ K]
    unfold productEstimate
    field_simp [(hZ 0).ne', (hZ K).ne']
  rw [hid]
  exact ⟨mul_le_mul_of_nonneg_right hprod.1 (hZ K).le,
    mul_le_mul_of_nonneg_right hprod.2 (hZ K).le⟩

end MatchingFPRAS.Counting

namespace MatchingFPRAS.UnitRefresh

lemma pairingCount_le_half_power (n : ℕ) : pairingCount n ≤ n^(n/2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [pairingCount_add_two,show (n+2)/2=n/2+1 by omega,pow_succ]
    calc
      (n+1)*pairingCount n ≤ (n+2)*((n+2)^(n/2)) :=
        Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) (n/2)))
      _ = (n+2)^(n/2)*(n+2) := Nat.mul_comm _ _

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Trial

open Finset Switching

lemma initial_raw_partition (G : GraphInput) : partition (raw G 0) ∅=(Z (completeGraph G.n):ℝ) := by
  rw [raw_zero,Initializer.uniform_partition,Finset.card_empty,Nat.sub_zero,one_pow,mul_one,
    Fintype.card_fin,GraphBridge.complete_count]

theorem final_padding (G : GraphInput) (ε : ℚ) (hε : 0<ε) (K : ℕ)
    (hK : Counting.scheduleAdmissible G.n ε K) (hZ : 0<Z G) :
    (Z G:ℝ) ≤ partition (raw G K) ∅ ∧
      partition (raw G K) ∅ ≤ (1+(ε:ℝ)/32)*(Z G:ℝ) := by
  let x : ℚ := ((1+1/(G.n:ℚ))⁻¹)^K
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    apply inv_le_one_of_one_le₀
    have hh : (0:ℚ)≤1/(G.n:ℚ) := by positivity
    linarith
  have hcast : (x:ℝ)=cooling G.n^K := by
    dsimp [x,cooling]
    push_cast
    rfl
  have hp : (rawPartition G x:ℝ)=partition (raw G K) ∅ := by
    rw [GraphBridge.raw_partition,hcast]
    rfl
  have hb := raw_padding_bound G x hx hx1
  have hb0 : (Z G:ℝ)≤partition (raw G K) ∅ := by rw [←hp]; exact_mod_cast hb.1
  have hb1 : partition (raw G K) ∅≤(Z G:ℝ)+(Z (completeGraph G.n):ℝ)*(x:ℝ) := by
    rw [←hp]; exact_mod_cast hb.2
  have hcount : (Z (completeGraph G.n):ℝ)≤(G.n:ℝ)^(G.n/2) := by
    rw [GraphBridge.complete_count]
    exact_mod_cast UnitRefresh.pairingCount_le_half_power G.n
  have hsmall : (G.n:ℝ)^(G.n/2)*(x:ℝ) ≤ (ε:ℝ)/32 := by
    have hq : (G.n:ℚ)^(G.n/2)*x ≤ ε/32 := by
      simpa only [x,div_eq_mul_inv,inv_pow] using hK.2
    exact_mod_cast hq
  have hz1 : (1:ℝ)≤Z G := by exact_mod_cast hZ
  have he0 : (0:ℝ)<ε := by exact_mod_cast hε
  have hh := mul_le_mul_of_nonneg_right hcount (by exact_mod_cast hx : (0:ℝ)≤x)
  refine ⟨hb0,?_⟩
  nlinarith

theorem final_trial_interval (G : GraphInput) (heven : Even G.n) (ε : ℚ)
    (hε : 0<ε) (hε1 : ε<1) (K : ℕ) (hK : Counting.scheduleAdmissible G.n ε K)
    (hZ : 0<Z G) (r : Fin K → ℝ)
    (hr : ∀ j,|r j/(partition (raw G (j.val+1)) ∅/partition (raw G j.val) ∅)-1|≤(ε:ℝ)/(100*K)) :
    let Y := (Z (completeGraph G.n):ℝ)*∏ j,r j
    (1-(ε:ℝ))*(Z G:ℝ)≤Y ∧ Y≤(1+(ε:ℝ))*(Z G:ℝ) := by
  dsimp only
  have he : (0:ℝ)<ε := by exact_mod_cast hε
  have he1 : (ε:ℝ)<1 := by exact_mod_cast hε1
  have h := Counting.trial_output_error K hK.1 ε he he1
    (fun j=>partition (raw G j) ∅) (raw_partition_pos G heven) r hr
  simp only [Counting.productEstimate,initial_raw_partition] at h
  have hb := final_padding G ε hε K hK hZ
  have hz : (0:ℝ)≤Z G := Nat.cast_nonneg _
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hb.1 (by linarith : (0:ℝ)≤1-(ε:ℝ)/100)
    nlinarith [mul_nonneg he.le hz]
  · have hmul := mul_le_mul_of_nonneg_left hb.2 (by positivity : (0:ℝ)≤1+(ε:ℝ)/50)
    have hscalar : (1+(ε:ℝ)/50)*(1+(ε:ℝ)/32)≤1+(ε:ℝ) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hscalar hz
    nlinarith

end MatchingFPRAS.Trial

namespace MatchingFPRAS.Adaptive

open Finset

variable {Ω : Type*} [Fintype Ω]

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x,0 ≤ mass x
  total : ∑ x,mass x=1

instance : CoeFun (Law Ω) (fun _ => Ω → ℝ) := ⟨Law.mass⟩

noncomputable def Law.event (μ : Law Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ x,if P x then μ x else 0

lemma Law.event_nonneg (μ : Law Ω) (P : Ω → Prop) : 0 ≤ μ.event P := by
  classical
  apply sum_nonneg
  intro x _
  split_ifs
  · exact μ.nonneg x
  · rfl

lemma Law.event_le_one (μ : Law Ω) (P : Ω → Prop) : μ.event P ≤ 1 := by
  classical
  rw [← μ.total]
  apply sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact μ.nonneg x

noncomputable def Law.step (μ : Law Ω) (k : Ω → Law Ω) : Law Ω where
  mass y := ∑ x,μ x*k x y
  nonneg y := sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) ((k x).nonneg y)
  total := by
    rw [sum_comm]
    simp only [← mul_sum,Law.total,mul_one]

lemma Law.step_event (μ : Law Ω) (k : Ω → Law Ω) (P : Ω → Prop) :
    (μ.step k).event P=∑ x,μ x*(k x).event P := by
  classical
  unfold Law.event
  change (∑ y,if P y then ∑ x,μ x*k x y else 0)=_
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  split_ifs <;> simp

theorem first_failure_step (μ : Law Ω) (k : Ω → Law Ω) (P Q : Ω → Prop)
    (η : ℝ) (hη : 0 ≤ η) (h : ∀ x,P x → (k x).event (fun y => ¬Q y) ≤ η) :
    (μ.step k).event (fun y => ¬Q y) ≤ μ.event (fun x => ¬P x)+η := by
  classical
  rw [Law.step_event,← mul_one η,← μ.total,mul_sum]
  unfold Law.event
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases hx : P x
  · have hh := mul_le_mul_of_nonneg_left (h x hx) (μ.nonneg x)
    simpa [Law.event,hx,mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left ((k x).event_le_one (fun y => ¬Q y)) (μ.nonneg x)
    have hz := mul_nonneg hη (μ.nonneg x)
    dsimp [Law.event] at hh
    dsimp [Law.event]
    simp only [hx,not_false_eq_true,ite_true]
    nlinarith

noncomputable def Law.evolve (μ : Law Ω) (k : ℕ → Ω → Law Ω) : ℕ → Law Ω
  | 0 => μ
  | n+1 => (μ.evolve k n).step (k n)

theorem first_failure_bound (μ : Law Ω) (k : ℕ → Ω → Law Ω) (P : ℕ → Ω → Prop)
    (η : ℝ) (hη : 0 ≤ η) (h0 : μ.event (fun x => ¬P 0 x)=0)
    (h : ∀ n x,P n x → (k n x).event (fun y => ¬P (n+1) y) ≤ η) (n : ℕ) :
    (μ.evolve k n).event (fun x => ¬P n x) ≤ n*η := by
  induction n with
  | zero => simp [Law.evolve,h0]
  | succ n ih =>
    change ((μ.evolve k n).step (k n)).event _ ≤ _
    have hh := first_failure_step (μ.evolve k n) (k n) (P n) (P (n+1)) η hη (h n)
    push_cast
    linarith

theorem source_trial_failure (μ : Law Ω) (k : ℕ → Ω → Law Ω) (P : ℕ → Ω → Prop)
    (K : ℕ) (hK : 0 < K) (h0 : μ.event (fun x => ¬P 0 x)=0)
    (h : ∀ n x,P n x → (k n x).event (fun y => ¬P (n+1) y) ≤ 13/(1000*K)) :
    (μ.evolve k K).event (fun x => ¬P K x) ≤ 13/1000 := by
  have hh := first_failure_bound μ k P (13/(1000*K)) (by positivity) h0 h K
  convert hh using 1
  have hz : (K:ℝ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  field_simp



open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω] {Ψ : Ω → Type*} [∀ x,Fintype (Ψ x)]

noncomputable def Law.sigma (μ : Law Ω) (ν : ∀ x,Law (Ψ x)) : Law (Sigma Ψ) where
  mass z := μ z.1*ν z.1 z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) ((ν z.1).nonneg z.2)
  total := by
    rw [Fintype.sum_sigma]
    change (∑ x,∑ y,μ x*(ν x) y)=1
    simp_rw [←mul_sum,Law.total,mul_one]
    exact μ.total

lemma Law.sigma_event (μ : Law Ω) (ν : ∀ x,Law (Ψ x)) (P : Sigma Ψ → Prop) :
    (μ.sigma ν).event P=∑ x,μ x*(ν x).event (fun y=>P ⟨x,y⟩) := by
  unfold Law.event
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  split_ifs <;> simp [Law.sigma]

lemma Law.event_mono (μ : Law Ω) {P Q : Ω → Prop} (h : ∀ x,P x→Q x) :
    μ.event P ≤ μ.event Q := by
  unfold Law.event
  apply sum_le_sum
  intro x _
  split_ifs with hp hq hq
  · rfl
  · exact False.elim (hq (h x hp))
  · exact μ.nonneg x
  · rfl

lemma first_failure_sigma (μ : Law Ω) (ν : ∀ x,Law (Ψ x))
    (P : Ω → Prop) (Q : Sigma Ψ → Prop) (η : ℝ) (hη : 0≤η)
    (h : ∀ x,P x→(ν x).event (fun y=>¬Q ⟨x,y⟩) ≤ η) :
    (μ.sigma ν).event (fun z=>¬Q z) ≤ μ.event (fun x=>¬P x)+η := by
  rw [Law.sigma_event,←mul_one η,←μ.total,mul_sum]
  unfold Law.event
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases hx : P x
  · have hh := mul_le_mul_of_nonneg_left (h x hx) (μ.nonneg x)
    simpa [Law.event,hx,mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left ((ν x).event_le_one (fun y=>¬Q ⟨x,y⟩)) (μ.nonneg x)
    have hz := mul_nonneg hη (μ.nonneg x)
    dsimp [Law.event] at hh
    dsimp [Law.event]
    simp only [hx,not_false_eq_true,ite_true]
    nlinarith



open Finset
open MatchingFPRAS.Enlargement MatchingFPRAS.Transport MatchingFPRAS.Replica.Ladder
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

noncomputable def Law.changeFintype {Ω : Type*} {i j : Fintype Ω} (μ : @Law Ω i) : @Law Ω j := by
  have hij : i=j := Subsingleton.elim _ _
  cases hij
  exact μ

@[simp] theorem Law.changeFintype_mass {Ω : Type*} {i j : Fintype Ω} (μ : @Law Ω i) (x : Ω) :
    @Law.mass Ω j (@Law.changeFintype Ω i j μ) x = @Law.mass Ω i μ x := by
  have hij : i=j := Subsingleton.elim _ _
  cases hij
  rfl

noncomputable def Law.iid (μ : Law Ω) (S : ℕ) : Law (Fin S → Ω) where
  mass := Variation.iid μ.mass S
  nonneg := Variation.iid_nonneg μ.mass μ.nonneg S
  total := Variation.iid_sum μ.mass μ.total S

end MatchingFPRAS.Adaptive

namespace MatchingFPRAS.Enlargement

open Finset MatchingFPRAS.Transport MatchingFPRAS.Adaptive MatchingFPRAS.Replica.Ladder
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourcePM w K) := Classical.decEq _

noncomputable def sourceRunLawBase (w : V → V → ℝ) (hw : ∀ a b,0<w a b) (K : ℕ)
    (hK : ∀ a b,a≠b → Switching.edgeActivity w a b ≤ (4:ℝ)^K)
    (T q : ℕ) (hq : 0<q) (z : Slot T q → SourcePM w K) (t : ℕ) : Law (SourceMarked w K) where
  mass := sourceRun w K hK T q hq z t
  nonneg := sourceRun_nonneg w hw K hK T q hq z t
  total := sourceRun_sum w hw K hK T q hq z t

noncomputable def sourceRunLaw (w : V → V → ℝ) (hw : ∀ a b,0<w a b) (K : ℕ)
    (hK : ∀ a b,a≠b → Switching.edgeActivity w a b ≤ (4:ℝ)^K)
    (T q : ℕ) (hq : 0<q) (z : Slot T q → SourcePM w K) (t : ℕ)
    (i : Fintype (SourceMarked w K)) : @Law (SourceMarked w K) i :=
  @Law.changeFintype _ _ i (sourceRunLawBase w hw K hK T q hq z t)

@[simp] lemma sourceRunLaw_mass (w : V → V → ℝ) (hw : ∀ a b,0<w a b) (K : ℕ)
    (hK : ∀ a b,a≠b → Switching.edgeActivity w a b ≤ (4:ℝ)^K)
    (T q : ℕ) (hq : 0<q) (z : Slot T q → SourcePM w K) (t : ℕ)
    (i : Fintype (SourceMarked w K)) (a : SourceMarked w K) :
    @Law.mass _ i (sourceRunLaw w hw K hK T q hq z t i) a=sourceRun w K hK T q hq z t a := by
  simp only [sourceRunLaw,Law.changeFintype_mass]
  rfl

@[instance_reducible]
noncomputable def sourceMarkedFintype (w : V → V → ℝ) (K : ℕ) : Fintype (SourceMarked w K) := inferInstance

theorem sourceRunLaw_budget (hn : 2 ≤ Fintype.card V)
    (w w₁ : V → V → ℝ) (hw : ∀ a b,0<w a b)
    (hw₁ : ∀ a b,0≤w₁ a b) (hle : ∀ a b,a≠b → w₁ a b≤w a b)
    (hz : 0<Switching.partition w ∅) (K T S : ℕ) (hT : 0<T) (hS : 0<S)
    (hK : ∀ a b,a≠b → Switching.edgeActivity w a b≤(4:ℝ)^K)
    (σ : ℝ) (hσ : 0≤σ) (hSσ : 10*((Fintype.card V:ℝ)+T+1)≤(S:ℝ)*σ^2)
    (L : ℕ) (hL : max (sourceD (V:=V) K:ℝ) (3*4^K)≤(tierBase (SourceVertex V K))^L)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K))
    (z : Slot L (ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K)) → SourcePM w K)
    (i : Fintype (SourceMarked w K)) :
    ((sourceRunLaw w hw K hK L _ hq z
      (ladderSteps (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K) K L (1/(1000*T*S))) i).iid S).event
      (fun x=>¬StageGood w w₁ K σ x) < 13/(1000*T) := by
  have hi : i=sourceMarkedFintype w K := Subsingleton.elim _ _
  subst i
  have h := source_run_stage_budget hn w w₁ hw hw₁ hle hz K T S hT hS hK σ hσ hSσ L hL hq z
  convert h using 1
  unfold Law.event Law.iid Variation.event Variation.iid sourceMarkedFintype
  congr 1

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

structure Parameters (G : GraphInput) where
  hn : 2 ≤ G.n
  even : Even G.n
  K : ℕ
  epsilon : ℚ
  epsilon_pos : 0<epsilon
  epsilon_lt_one : epsilon<1
  schedule : Counting.scheduleAdmissible G.n epsilon K

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourcePM w K) := Classical.decEq _

omit [Nontrivial (Fin G.n)] in
lemma Parameters.K_pos (p : Parameters G) : 0<p.K := p.schedule.1

omit [Nontrivial (Fin G.n)] in
lemma Parameters.epsilon_real_pos (p : Parameters G) : (0:ℝ)<p.epsilon := by exact_mod_cast p.epsilon_pos

omit [Nontrivial (Fin G.n)] in
lemma Parameters.epsilon_real_lt_one (p : Parameters G) : (p.epsilon:ℝ)<1 := by exact_mod_cast p.epsilon_lt_one

noncomputable def Parameters.D (p : Parameters G) : ℕ := sourceD (V:=Fin G.n) p.K

def Parameters.N (p : Parameters G) : ℕ := Fintype.card (SourceVertex (Fin G.n) p.K)

omit [Nontrivial (Fin G.n)] in
lemma Parameters.N_pos (p : Parameters G) : 0<p.N := by
  have h := sourceVertex_card_ge (V:=Fin G.n) p.K
  simp only [Fintype.card_fin] at h
  exact lt_of_lt_of_le (by have := p.hn; omega) h

lemma Parameters.D_pos (p : Parameters G) : 0<p.D := sourceD_one _

noncomputable def Parameters.T (p : Parameters G) : ℕ := ladderTier p.N p.D p.K p.N_pos

noncomputable def Parameters.q (p : Parameters G) : ℕ := ladderQ p.N p.D

lemma Parameters.q_pos (p : Parameters G) : 0<p.q := by
  unfold Parameters.q ladderQ ladderL
  have hn := p.N_pos
  have hd := p.D_pos
  positivity

noncomputable def Parameters.sigma (p : Parameters G) : ℝ := RealStage.sigma p.D p.K p.epsilon

noncomputable def Parameters.S (p : Parameters G) : ℕ := stageSampleCount G.n p.D p.K p.epsilon

noncomputable def Parameters.initialData (p : Parameters G) : StageData G.n p.K p.K :=
  stageData G p.hn p.even p.K p.K_pos p.epsilon p.epsilon_real_pos p.epsilon_real_lt_one 0
    (Nat.zero_le _) (initialScaleState G p.hn) (initial_balanced G p.hn p.even)

lemma Parameters.sigma_pos (p : Parameters G) : 0<p.sigma := p.initialData.sigma_pos

lemma Parameters.S_pos (p : Parameters G) : 0<p.S := p.initialData.sampleCount_pos

lemma Parameters.S_bound (p : Parameters G) : 10*((G.n:ℝ)+p.K+1) ≤ (p.S:ℝ)*p.sigma^2 :=
  p.initialData.sampleCount_bound

lemma sourcePM_nonempty (w : Fin G.n → Fin G.n → ℝ) (hw : ∀ a b,0<w a b)
    (hz : 0<partition w ∅) (K : ℕ) : Nonempty (SourcePM w K) := by
  have hp := sourceBagZ_pos w hw hz K (sourceD (V:=Fin G.n) K)
  by_contra hn
  have : IsEmpty (SourcePM w K) := not_nonempty_iff.mp hn
  change 0<(∑ M : SourcePM w K,∏ e ∈ M.val,sourceBagWeight w K (sourceD (V:=Fin G.n) K) e) at hp
  simp at hp

noncomputable def ScaleState.start (p : Parameters G) {j : ℕ} (s : ScaleState G j) : SourcePM s.activity p.K :=
  Classical.choice (sourcePM_nonempty s.activity s.activity_pos (s.partition_pos p.even) p.K)

noncomputable def ScaleState.runLaw (p : Parameters G) {j : ℕ} (hj : j ≤ p.K) (s : ScaleState G j) :
    Law (SourceMarked s.activity p.K) :=
  sourceRunLaw s.activity s.activity_pos p.K (s.cap hj) p.T p.q p.q_pos (fun _=>s.start p)
    (ladderSteps p.N p.D p.K p.T (1/(1000*p.K*p.S))) inferInstance

noncomputable def ScaleState.sampleLaw (p : Parameters G) {j : ℕ} (hj : j ≤ p.K) (s : ScaleState G j) :
    Law (Fin p.S → SourceMarked s.activity p.K) := (s.runLaw p hj).iid p.S

theorem ScaleState.sampleLaw_budget (p : Parameters G) {j : ℕ} (hj : j ≤ p.K) (s : ScaleState G j)
    (_hs : s.Balanced p.hn) :
    (s.sampleLaw p hj).event (fun x=>¬StageGood s.activity s.nextActivity p.K p.sigma x) < 13/(1000*p.K) := by
  exact sourceRunLaw_budget (by simpa using p.hn) s.activity s.nextActivity s.activity_pos
    (fun a b=>(s.nextActivity_pos a b).le) (fun a b _=>(s.cooling a b).2) (s.partition_pos p.even)
    p.K p.K p.S p.K_pos p.S_pos (s.cap hj) p.sigma p.sigma_pos.le (by simpa using p.S_bound)
    p.T (ladderTier_spec p.N p.D p.K p.N_pos) p.q_pos (fun _=>s.start p) inferInstance

structure Layer (p : Parameters G) (j : ℕ) where
  Ω : Type
  finite : Fintype Ω
  law : @Law Ω finite
  state : Ω → ScaleState G j
  ratios : Ω → Fin j → ℝ
  ratios_nonneg : ∀ x i,0 ≤ ratios x i

attribute [instance] Layer.finite

noncomputable def Layer.good (p : Parameters G) {j : ℕ} (L : Layer p j) (x : L.Ω) : Prop :=
  (L.state x).Balanced p.hn ∧ ∀ i : Fin j,
    |L.ratios x i/(partition (raw G (i.val+1)) ∅/partition (raw G i.val) ∅)-1| ≤ (p.epsilon:ℝ)/(100*p.K)

noncomputable def firstLayer (p : Parameters G) : Layer p 0 where
  Ω := PUnit
  finite := inferInstance
  law := ⟨fun _=>1,fun _=>by norm_num,by simp⟩
  state _ := initialScaleState G p.hn
  ratios _ := Fin.elim0
  ratios_nonneg _ i := Fin.elim0 i

noncomputable def Layer.append (p : Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) : Layer p (j+1) where
  Ω := Σ x : L.Ω, Fin p.S → SourceMarked (L.state x).activity p.K
  finite := inferInstance
  law := L.law.sigma (fun x=>(L.state x).sampleLaw p hj)
  state x := (L.state x.1).update p.hn x.2
  ratios x := Fin.snoc (L.ratios x.1) ((L.state x.1).ratioEstimate x.2)
  ratios_nonneg x i := by
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa using (L.state x.1).ratioEstimate_nonneg p.S_pos x.2
    · simpa using L.ratios_nonneg x.1 i

theorem Layer.append_good (p : Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) (x : L.Ω)
    (hx : L.good p x) (y : Fin p.S → SourceMarked (L.state x).activity p.K)
    (hy : StageGood (L.state x).activity (L.state x).nextActivity p.K p.sigma y) :
    (L.append p hj).good p ⟨x,y⟩ := by
  have h := successful_update p.hn p.even p.K_pos p.epsilon p.epsilon_real_pos p.epsilon_real_lt_one
    hj (L.state x) hx.1 y hy
  refine ⟨h.1,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simpa [Layer.append] using h.2
  · simpa [Layer.append] using hx.2 i

theorem Layer.append_failure (p : Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) :
    (L.append p hj).law.event (fun x=>¬(L.append p hj).good p x) ≤
      L.law.event (fun x=>¬L.good p x)+13/(1000*p.K) := by
  apply first_failure_sigma L.law (fun x=>(L.state x).sampleLaw p hj) (L.good p)
    ((L.append p hj).good p) _ (by positivity)
  intro x hx
  apply le_trans ((L.state x).sampleLaw p hj |>.event_mono ?_)
    ((L.state x).sampleLaw_budget p hj hx.1).le
  intro y hy hgood
  exact hy (L.append_good p hj x hx y hgood)

noncomputable def layers (p : Parameters G) : (j : ℕ) → j ≤ p.K → Layer p j
  | 0, _ => firstLayer p
  | j+1, h => (layers p j (by omega)).append p (by omega)

theorem layers_failure (p : Parameters G) (j : ℕ) (hj : j ≤ p.K) :
    (layers p j hj).law.event (fun x=>¬(layers p j hj).good p x) ≤ j*(13/(1000*p.K)) := by
  induction j with
  | zero =>
    have hg : ∀ x,(firstLayer p).good p x := by
      intro x
      constructor
      · exact initial_balanced G p.hn p.even
      · intro i; exact Fin.elim0 i
    simp [layers,Law.event,hg]
  | succ j ih =>
    refine le_trans ((layers p j (by omega)).append_failure p (by omega)) ?_
    calc
      _ ≤ (j:ℝ)*(13/(1000*p.K))+13/(1000*p.K) := by linarith only [ih (by omega)]
      _ = _ := by push_cast; ring

noncomputable def output (p : Parameters G) (x : (layers p p.K le_rfl).Ω) : ℝ :=
  (Z (completeGraph G.n):ℝ)*∏ i,(layers p p.K le_rfl).ratios x i

lemma output_nonneg (p : Parameters G) (x : (layers p p.K le_rfl).Ω) : 0 ≤ output p x := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact prod_nonneg fun i _=>(layers p p.K le_rfl).ratios_nonneg x i

def Accurate (p : Parameters G) (y : ℝ) : Prop :=
  (1-(p.epsilon:ℝ))*(Z G:ℝ)≤y ∧ y≤(1+(p.epsilon:ℝ))*(Z G:ℝ)

theorem good_output (p : Parameters G) (hZ : 0<Z G) (x : (layers p p.K le_rfl).Ω)
    (hx : (layers p p.K le_rfl).good p x) : Accurate p (output p x) :=
  final_trial_interval G p.even p.epsilon p.epsilon_pos p.epsilon_lt_one p.K p.schedule hZ
    ((layers p p.K le_rfl).ratios x) hx.2

theorem actual_ideal_trial_failure (p : Parameters G) (hZ : 0<Z G) :
    (layers p p.K le_rfl).law.event (fun x=>¬Accurate p (output p x)) ≤ 13/1000 := by
  have hh := layers_failure p p.K le_rfl
  have he : (p.K:ℝ)*(13/(1000*p.K))=13/1000 := by
    have hk : (p.K:ℝ)≠0 := by exact_mod_cast p.K_pos.ne'
    field_simp
  rw [he] at hh
  apply le_trans ((layers p p.K le_rfl).law.event_mono ?_) hh
  intro x hx hg
  exact hx (good_output p hZ x hg)

end MatchingFPRAS.Trial

end OAI
