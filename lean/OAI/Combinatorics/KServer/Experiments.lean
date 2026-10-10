import Mathlib
import OAI.Combinatorics.KServer.Amplification
import OAI.Combinatorics.KServer.Ranks

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.FiniteExperiment
attribute [local instance] Classical.propDecidable
open Finset Episode PosteriorRanks
universe u v
variable {Y : Type u} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

/-- A fixed minimizing labeled trajectory for each complete input. -/
def optimalTrace (s : Configuration k Y) (σ : Fin H → Y) : List (Y × Fin k) :=
  serviceTrace (List.ofFn σ) (optimalCost_attained s (List.ofFn σ)).choose

omit [Fintype Y] in
lemma optimalTrace_requests (s : Configuration k Y) (σ : Fin H → Y) :
    (optimalTrace s σ).map Prod.fst=List.ofFn σ :=
  serviceTrace_requests _ _

omit [Fintype Y] in
lemma optimalTrace_cost (s : Configuration k Y) (σ : Fin H → Y) :
    traceCost s (optimalTrace s σ)=optimalCost s (List.ofFn σ) := by
  rw [optimalTrace,serviceTrace_cost]
  exact (optimalCost_attained s (List.ofFn σ)).choose_spec

omit [Fintype Y] in
lemma optimalTrace_length (s : Configuration k Y) (σ : Fin H → Y) :
    (optimalTrace s σ).length=H := by
  simpa only [List.length_map,List.length_ofFn] using
    congrArg List.length (optimalTrace_requests s σ)

/-- The genuine hidden configuration, frozen when the finite input ends. -/
def hidden (s : Configuration k Y) (σ : Fin H → Y) (t : ℕ) : Configuration k Y :=
  configurationAfter s ((optimalTrace s σ).take t)

omit [Fintype Y] in
lemma hidden_zero (s : Configuration k Y) (σ : Fin H → Y) : hidden s σ 0=s := by
  simp [hidden,configurationAfter]

/-- Current designated occurrence in the selected optimum; it is not observed. -/
def mover (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) : Fin k :=
  ((optimalTrace s σ)[t.val]'(by rw [optimalTrace_length]; exact t.isLt)).2

omit [Fintype Y] in
lemma optimalTrace_get_request (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    ((optimalTrace s σ)[t.val]'(by rw [optimalTrace_length]; exact t.isLt)).1=σ t := by
  have he := congrArg (fun l : List Y => l[t.val]?) (optimalTrace_requests s σ)
  apply Option.some.inj
  simpa only [List.getElem?_map,List.getElem?_eq_getElem
    (show t.val<(optimalTrace s σ).length by rw [optimalTrace_length]; exact t.isLt),
    Option.map_some,List.getElem?_ofFn,Fin.isLt,dite_eq_left] using he

omit [Fintype Y] in
lemma hidden_step (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    hidden s σ (t.val+1)=serve (hidden s σ t.val) (mover s σ t) (σ t) := by
  have ht : t.val<(optimalTrace s σ).length := by rw [optimalTrace_length]; exact t.isLt
  rw [hidden,List.take_succ_eq_append_getElem ht,configurationAfter_append]
  simp only [configurationAfter]
  rw [optimalTrace_get_request]
  rfl

omit [Fintype Y] in
lemma hidden_covers (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    hidden s σ (t.val+1) (mover s σ t)=σ t := by
  rw [hidden_step]
  simp [serve]

/-- A finite observation sufficient for exactly the request requestPrefix. -/
def requestPrefix (σ : Fin H → Y) (t : ℕ) : Fin H → Option Y :=
  fun i => if i.val<t then some (σ i) else none

omit [MetricSpace Y] [Fintype Y] in
lemma prefix_refines (σ ρ : Fin H → Y) (t : ℕ)
    (h : requestPrefix σ (t+1)=requestPrefix ρ (t+1)) : requestPrefix σ t=requestPrefix ρ t := by
  funext i
  by_cases hi : i.val<t
  · have he := congrFun h i
    simpa [requestPrefix,hi,show i.val<t+1 by omega] using he
  · simp [requestPrefix,hi]

omit [MetricSpace Y] [Fintype Y] in
lemma prefix_request {σ ρ : Fin H → Y} (t : Fin H)
    (h : requestPrefix σ (t.val+1)=requestPrefix ρ (t.val+1)) : σ t=ρ t := by
  have he := congrFun h t
  simpa [requestPrefix] using he

variable {T : Type v} [Fintype T]

/-- Histories include the independent partition tape from time zero. Coding a
finite observation by a natural number is injective, not a loss of information. -/
def history (t : ℕ) (ω : (Fin H → Y) × T) : ℕ :=
  (Fintype.equivFin (T × (Fin H → Option Y)) (ω.2,requestPrefix ω.1 t)).val

omit [MetricSpace Y] in
lemma history_eq_iff (t : ℕ) (ω z : (Fin H → Y) × T) :
    history t ω=history t z ↔ ω.2=z.2 ∧ requestPrefix ω.1 t=requestPrefix z.1 t := by
  unfold history
  rw [Fin.val_inj,(Fintype.equivFin _).injective.eq_iff,Prod.mk.injEq]

omit [MetricSpace Y] in
lemma history_refines (t : ℕ) (ω z : (Fin H → Y) × T)
    (h : history (t+1) ω=history (t+1) z) : history t ω=history t z := by
  rw [history_eq_iff] at h ⊢
  exact ⟨h.1,prefix_refines _ _ _ h.2⟩

/-- Literal independent product weights, before any requestPrefix is revealed. -/
def weight (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (ω : (Fin H → Y) × T) : ℝ := law.val ω.1*tape.val ω.2

omit [MetricSpace Y] in
lemma weight_nonneg (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (ω : (Fin H → Y) × T) : 0≤weight law tape ω :=
  mul_nonneg (law.property.1 _) (tape.property.1 _)

omit [MetricSpace Y] in
lemma weight_sum (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T) :
    ∑ ω,weight law tape ω=1 := by
  simp only [weight,Fintype.sum_prod_type,←mul_sum,tape.property.2,mul_one,law.property.2]

/-- All ranks queried by the allocation are actual conditional hidden counts.
The online map may depend on the partition tape and request requestPrefix; it never
changes how the old hidden quantity is filtered. -/
def count (s : Configuration k Y) {V : Type*} (map : ℕ → ((Fin H → Y) × T) → Y → V)
    (under : V → V → Bool) (v : V) (t : ℕ) (ω : (Fin H → Y) × T) : ℕ :=
  univ.sum fun i : Fin k => if under v (map t ω (hidden s ω.1 t i)) then 1 else 0

omit [Fintype Y] [Fintype T] in
lemma count_le (s : Configuration k Y) {V : Type*}
    (map : ℕ → ((Fin H → Y) × T) → Y → V) (under : V → V → Bool)
    (v : V) (t : ℕ) (ω : (Fin H → Y) × T) : count s map under v t ω≤k := by
  calc
    _ ≤ ∑ _i : Fin k,1 := sum_le_sum fun _ _ => by aesop
    _ = k := by simp

/-- This concrete process discharges the signed all-step filtering premise. -/
def ranks (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (tape : FiniteDistribution T) {V : Type*}
    (map : ℕ → ((Fin H → Y) × T) → Y → V) (under : V → V → Bool)
    (v : V) (a : Fin k) : RankTracking.FilteredRanks (weight law tape) :=
  rankProcess (weight_nonneg law tape) history history_refines (count s map under v) a.val

lemma ranks_drift (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (tape : FiniteDistribution T) {V : Type*}
    (map : ℕ → ((Fin H → Y) × T) → Y → V) (under : V → V → Bool)
    (v : V) (t : ℕ) :
    (∑ a : Fin k,RankTracking.avg (weight law tape) (fun ω =>
      |(ranks s law tape map under v a).p (t+1) ω-
        (ranks s law tape map under v a).before (t+1) ω|)) ≤
      RankTracking.avg (weight law tape) (fun ω =>
        |(count s map under v (t+1) ω:ℝ)-count s map under v t ω|) :=
  rankProcess_drift (weight_nonneg law tape) history history_refines
    (count s map under v) (count_le s map under v) t


omit [Fintype Y] in
lemma hidden_movement (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    (∑ i,dist (hidden s σ t.val i) (hidden s σ (t.val+1) i))=
      dist (hidden s σ t.val (mover s σ t)) (σ t) := by
  classical
  rw [hidden_step]
  simp [serve,Function.update_apply,apply_ite]

omit [Fintype Y] in
lemma hidden_total_cost (s : Configuration k Y) (σ : Fin H → Y) :
    (∑ t : Fin H,∑ i,dist (hidden s σ t.val i) (hidden s σ (t.val+1) i))=
      optimalCost s (List.ofFn σ) := by
  have he (n : ℕ) (hn : n≤H) :
      traceCost s ((optimalTrace s σ).take n)=
        ∑ t ∈ range n,∑ i,dist (hidden s σ t i) (hidden s σ (t+1) i) := by
    induction n with
    | zero => simp [traceCost]
    | succ n ih =>
      have hlt : n<(optimalTrace s σ).length := by rw [optimalTrace_length]; omega
      rw [List.take_succ_eq_append_getElem hlt,traceCost_append,ih (by omega),sum_range_succ]
      congr 1
      rw [hidden_movement s σ ⟨n,by omega⟩]
      simp only [traceCost,add_zero]
      rw [optimalTrace_get_request s σ ⟨n,by omega⟩]
      rfl
  have htake : (optimalTrace s σ).take H=optimalTrace s σ := by
    apply List.take_of_length_le
    exact (optimalTrace_length s σ).le
  rw [←optimalTrace_cost,←htake,he H le_rfl]
  exact (Finset.sum_range (fun t : ℕ => ∑ i,
    dist (hidden s σ t i) (hidden s σ (t+1) i))).symm

lemma expected_hidden_cost (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (tape : FiniteDistribution T) :
    (∑ ω,weight law tape ω*(∑ t : Fin H,∑ i,
      dist (hidden s ω.1 t.val i) (hidden s ω.1 (t.val+1) i)))=
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ) := by
  simp only [hidden_total_cost,weight,Fintype.sum_prod_type]
  simp_rw [mul_right_comm (law.val _) (tape.val _),←mul_sum,tape.property.2,mul_one]

/-- True request history alone, for computing the metric posterior independently
of the partition tape. -/
def requestHistory (t : ℕ) (σ : Fin H → Y) : ℕ :=
  (Fintype.equivFin (Fin H → Option Y) (requestPrefix σ t)).val

omit [MetricSpace Y] in
lemma requestHistory_eq_iff (t : ℕ) (σ ρ : Fin H → Y) :
    requestHistory t σ=requestHistory t ρ ↔ requestPrefix σ t=requestPrefix ρ t := by
  unfold requestHistory
  rw [Fin.val_inj,(Fintype.equivFin _).injective.eq_iff]

omit [MetricSpace Y] in
lemma mass_product (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (t : ℕ) (ω : (Fin H → Y) × T) :
    mass (weight law tape) (history t) (history t ω)=
      mass law.val (requestHistory t) (requestHistory t ω.1)*tape.val ω.2 := by
  classical
  simp only [mass,fiber,sum_filter,history_eq_iff,requestHistory_eq_iff,
    Fintype.sum_prod_type,weight]
  rw [sum_mul]
  apply sum_congr rfl
  intro σ _
  by_cases hp : requestPrefix σ t=requestPrefix ω.1 t
  · simp [hp]
  · simp [hp]

omit [MetricSpace Y] in
lemma numerator_product (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (t : ℕ) (ω : (Fin H → Y) × T) (f : (Fin H → Y) → ℝ) :
    numerator (weight law tape) (history t) (fun z => f z.1) (history t ω)=
      numerator law.val (requestHistory t) f (requestHistory t ω.1)*tape.val ω.2 := by
  classical
  simp only [numerator,fiber,sum_filter,history_eq_iff,requestHistory_eq_iff,
    Fintype.sum_prod_type,weight]
  rw [sum_mul]
  apply sum_congr rfl
  intro σ _
  by_cases hp : requestPrefix σ t=requestPrefix ω.1 t
  · simp [hp]; ring
  · simp [hp]

omit [MetricSpace Y] in
/-- The precise independence statement legitimately used by the manuscript.
It does not assert independence of partition events after conditioning on the
tape, nor does it select reset events in a martingale estimate. -/
lemma posterior_tape_irrelevant (law : FiniteDistribution (Fin H → Y))
    (tape : FiniteDistribution T) (t : ℕ) (ω : (Fin H → Y) × T)
    (ht : tape.val ω.2≠0) (f : (Fin H → Y) → ℝ) :
    posterior (weight law tape) (history t) (fun z => f z.1) ω=
      posterior law.val (requestHistory t) f ω.1 := by
  simp only [posterior,numerator_product,mass_product]
  exact mul_div_mul_right _ _ ht

/-- Counting measure of a labeled configuration; repetitions contribute separately. -/
def metricCount (c : Configuration k Y) (y : Y) : ℝ := by
  classical
  exact ∑ i : Fin k, if c i=y then 1 else 0

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_nonneg (c : Configuration k Y) (y : Y) : 0 ≤ metricCount c y := by
  classical
  exact sum_nonneg fun i _ => by split_ifs <;> norm_num

omit [MetricSpace Y] [NeZero k] in
lemma metricCount_total (c : Configuration k Y) : ∑ y,metricCount c y=(k:ℝ) := by
  classical
  simp only [metricCount]
  rw [sum_comm]
  simp

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_at (c : Configuration k Y) (y : Y) (h : ∃ i,c i=y) :
    1 ≤ metricCount c y := by
  classical
  obtain ⟨i,hi⟩ := h
  have hs := single_le_sum (s := (univ : Finset (Fin k))) (f := fun j =>
    if c j=y then (1:ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
  simpa [hi,metricCount] using hs

/-- The true-metric posterior after t requests, independent of algorithmic tapes. -/
def mu (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (y : Y) : ℝ :=
  posterior law.val (requestHistory t) (fun ρ => metricCount (hidden s ρ t) y) σ

lemma mu_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (y : Y) : 0 ≤ mu s law t σ y :=
  posterior_nonneg law.property.1 _ (fun _ => metricCount_nonneg _ _) _

lemma mu_total (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (hσ : 0<law.val σ) : ∑ y,mu s law t σ y=(k:ℝ) := by
  unfold mu
  rw [←posterior_sum]
  exact posterior_fiber_const σ (fun ρ _ => metricCount_total _) (mass_pos_of_weight law.property.1 _ σ hσ).ne'

omit [MetricSpace Y] in
lemma request_of_history (t : Fin H) (σ ρ : Fin H → Y)
    (h : requestHistory (t.val+1) σ=requestHistory (t.val+1) ρ) : σ t=ρ t := by
  have he := congrFun ((requestHistory_eq_iff _ _ _).mp h) t
  simpa [requestPrefix,t.isLt] using he

lemma mu_served (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : 1 ≤ mu s law (t.val+1) σ (σ t) := by
  have hc : posterior law.val (requestHistory (t.val+1)) (fun _ => (1:ℝ)) σ=1 :=
    posterior_fiber_const σ (fun _ _ => rfl) (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  rw [←hc]
  apply posterior_mono_fiber law.property.1
  intro ρ hρ
  apply metricCount_at
  rw [←request_of_history t ρ σ hρ]
  exact ⟨mover s ρ t,hidden_covers s ρ t⟩

lemma mu_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (y : Y) : RankTracking.Adapted (requestHistory t) (fun σ => mu s law t σ y) :=
  posterior_adapted _ _ _

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_move (c : Configuration k Y) (i : Fin k) (x y : Y) :
    metricCount (serve c i x) y=metricCount c y-(if c i=y then 1 else 0)+
      (if x=y then 1 else 0) := by
  classical
  unfold metricCount
  rw [←add_sum_erase univ _ (mem_univ i),←add_sum_erase univ _ (mem_univ i)]
  have he : (∑ j∈univ.erase i,if serve c i x j=y then (1:ℝ) else 0)=
      ∑ j∈univ.erase i,if c j=y then (1:ℝ) else 0 := by
    apply sum_congr rfl
    intro j hj
    simp [serve,Function.update_of_ne (mem_erase.mp hj).1]
  rw [he]
  simp only [serve,Function.update_self]
  ring

/-- Old counting measure filtered through the new true request. -/
def muBefore (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : ℝ :=
  posterior law.val (requestHistory (t.val+1)) (fun ρ => metricCount (hidden s ρ t.val) y) σ

/-- The conditional old-location law of the single designated optimum mover. -/
def nu (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : ℝ := by
  classical
  exact posterior law.val (requestHistory (t.val+1))
    (fun ρ => if hidden s ρ t.val (mover s ρ t)=y then 1 else 0) σ

lemma muBefore_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : 0 ≤ muBefore s law t σ y :=
  posterior_nonneg law.property.1 _ (fun _ => metricCount_nonneg _ _) _

lemma nu_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : 0 ≤ nu s law t σ y := by
  apply posterior_nonneg law.property.1
  intro ρ
  split_ifs <;> norm_num

lemma nu_total (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : ∑ y,nu s law t σ y=1 := by
  classical
  unfold nu
  rw [←posterior_sum]
  apply posterior_fiber_const σ _ (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  intro ρ _
  simp

lemma nu_le_muBefore (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : nu s law t σ y ≤ muBefore s law t σ y := by
  apply posterior_mono_fiber law.property.1
  intro ρ _
  split_ifs with he
  · exact metricCount_at _ _ ⟨mover s ρ t,he⟩
  · exact metricCount_nonneg _ _

lemma muBefore_total (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : ∑ y,muBefore s law t σ y=(k:ℝ) := by
  unfold muBefore
  rw [←posterior_sum]
  exact posterior_fiber_const σ (fun ρ _ => metricCount_total _) (mass_pos_of_weight law.property.1 _ σ hσ).ne'

/-- Exact one-mover decomposition used by the pilot potential. -/
lemma mu_move (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) (y : Y) :
    mu s law (t.val+1) σ y=muBefore s law t σ y-nu s law t σ y+
      (if σ t=y then 1 else 0) := by
  classical
  unfold mu muBefore nu
  simp_rw [hidden_step,metricCount_move]
  rw [posterior_add,posterior_sub]
  congr 1
  apply posterior_fiber_const σ _ (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  intro ρ hρ
  rw [request_of_history t ρ σ hρ]

lemma conditional_moveCost (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) :
    (∑ y,nu s law t σ y*dist y (σ t))=
      posterior law.val (requestHistory (t.val+1))
        (fun ρ => dist (hidden s ρ t.val (mover s ρ t)) (ρ t)) σ := by
  classical
  unfold nu
  simp_rw [←posterior_mul]
  rw [←posterior_sum]
  unfold posterior numerator
  congr 1
  apply sum_congr rfl
  intro ρ hρ
  dsimp only
  rw [request_of_history t ρ σ (mem_filter.mp hρ).2]
  simp

/-- The entire physical-drift budget is the expectation of the attained optimum,
not a separate assumed bound or a policy-dependent comparator. -/
lemma expected_moveCost (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) :
    (∑ t : Fin H,∑ σ,law.val σ*(∑ y,nu s law t σ y*dist y (σ t)))=
      ∑ σ,law.val σ*optimalCost s (List.ofFn σ) := by
  simp_rw [conditional_moveCost]
  change (∑ t : Fin H,RankTracking.avg law.val
    (posterior law.val (requestHistory (t.val+1))
      (fun ρ => dist (hidden s ρ t.val (mover s ρ t)) (ρ t))))=_
  simp_rw [posterior_avg law.property.1]
  unfold RankTracking.avg
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  rw [←mul_sum]
  congr 1
  simp_rw [←hidden_movement]
  exact hidden_total_cost s σ

end KServer.FiniteExperiment

end

end OAI
