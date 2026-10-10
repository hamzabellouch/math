import Mathlib

namespace OAI

/-!
# Finite Bellman propagation and warmup

The action minimum is computed by a finite list with the initial cone as
fallback. Empty action families need no extended-real convention. The
warmup lemmas concern the actual repeated finite Bellman operator.
-/

namespace EditApproximation

open Finset

def finiteMinimum (fallback : ℝ) : List ℝ → ℝ
  | [] => fallback
  | value :: rest => min value (finiteMinimum fallback rest)

theorem le_finiteMinimum_iff (lower fallback : ℝ) (values : List ℝ) :
    lower ≤ finiteMinimum fallback values ↔ lower ≤ fallback ∧ ∀ v ∈ values, lower ≤ v := by
  induction values with
  | nil => simp [finiteMinimum]
  | cons v rest ih => simp only [finiteMinimum, le_min_iff, ih, List.mem_cons,
      forall_eq_or_imp]; tauto

theorem finiteMinimum_le_fallback (fallback : ℝ) (values : List ℝ) :
    finiteMinimum fallback values ≤ fallback := by
  induction values with
  | nil => rfl
  | cons v rest ih => exact (min_le_right _ _).trans ih

theorem finiteMinimum_le_member (fallback : ℝ) (values : List ℝ)
    {value : ℝ} (hvalue : value ∈ values) : finiteMinimum fallback values ≤ value := by
  induction values with
  | nil => simp at hvalue
  | cons v rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hvalue
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hvalue)

theorem finiteMinimum_map_mono {ι : Type*} (indices : List ι)
    (fallback fallback' : ℝ) (value value' : ι → ℝ)
    (hfallback : fallback ≤ fallback') (hvalue : ∀ i ∈ indices, value i ≤ value' i) :
    finiteMinimum fallback (indices.map value) ≤
      finiteMinimum fallback' (indices.map value') := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    simp only [List.map_cons, finiteMinimum]
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem finiteMinimum_map_add {ι : Type*} (indices : List ι)
    (fallback charge : ℝ) (value : ι → ℝ) :
    finiteMinimum (fallback + charge) (indices.map fun i => value i + charge) =
      finiteMinimum fallback (indices.map value) + charge := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, finiteMinimum, ih, min_add_add_right]

theorem finiteMinimum_map_spatial {ι : Type*} (indices : List ι)
    (fallback fallback' charge : ℝ) (value value' : ι → ℝ)
    (hfallback : fallback ≤ fallback' + charge)
    (hvalue : ∀ i ∈ indices, value i ≤ value' i + charge) :
    finiteMinimum fallback (indices.map value) ≤
      finiteMinimum fallback' (indices.map value') + charge := by
  rw [← finiteMinimum_map_add]
  exact finiteMinimum_map_mono indices _ _ _ _ hfallback hvalue

structure BellmanAction (Parent Child : Type*) (M : ℕ) where
  center : Parent
  connection : ℝ
  childState : Fin M → Child

def bellmanActionValue {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℝ) (L : ℝ) (child : Child → ℝ)
    (query : Parent) (action : BellmanAction Parent Child M) : ℝ :=
  L * distance query action.center + action.connection + ∑ i, child (action.childState i)

def finiteBellman {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ) (query : Parent) : ℝ :=
  finiteMinimum (fallback query) (actions.map (bellmanActionValue distance L child query))

theorem finiteBellman_le_fallback {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ) (query : Parent) :
    finiteBellman fallback distance L actions child query ≤ fallback query :=
  finiteMinimum_le_fallback _ _

theorem finiteBellman_mono {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) {child child' : Child → ℝ}
    (hchild : child ≤ child') :
    finiteBellman fallback distance L actions child ≤
      finiteBellman fallback distance L actions child' := by
  intro query
  apply finiteMinimum_map_mono _ _ _ _ _ le_rfl
  intro action _
  exact add_le_add le_rfl (sum_le_sum fun i _ => hchild (action.childState i))

theorem finiteBellman_le_action {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (query : Parent) (action : BellmanAction Parent Child M) (haction : action ∈ actions) :
    finiteBellman fallback distance L actions child query ≤
      bellmanActionValue distance L child query action :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

theorem finiteBellman_lower {Parent Child : Type*} {M : ℕ}
    (fallback lower : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (hfallback : lower ≤ fallback)
    (haction : ∀ query, ∀ action ∈ actions,
      lower query ≤ bellmanActionValue distance L child query action) :
    lower ≤ finiteBellman fallback distance L actions child := by
  intro query
  exact (le_finiteMinimum_iff _ _ _).2
    ⟨hfallback query, fun v hv => by
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      exact haction query action ha⟩

theorem finiteBellman_spatial {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (hL : 0 ≤ L) (query query' : Parent)
    (hfallback : fallback query ≤ fallback query' + L * distance query query')
    (htriangle : ∀ center, distance query center ≤ distance query' center + distance query query') :
    finiteBellman fallback distance L actions child query ≤
      finiteBellman fallback distance L actions child query' + L * distance query query' := by
  apply finiteMinimum_map_spatial _ _ _ _ _ _ hfallback
  intro action _
  have hdist := mul_le_mul_of_nonneg_left (htriangle action.center) hL
  dsimp [bellmanActionValue]
  linarith

def warmup {State : Type*} (operator : (State → ℝ) → State → ℝ)
    (initial : State → ℝ) : ℕ → State → ℝ
  | 0 => initial
  | t + 1 => operator (warmup operator initial t)

/-- A finite system of node-specific action lists. Child states may
belong to any lower level of the source tree. -/
def finiteBellmanSystem {State : Type*} {M : ℕ}
    (initial : State → ℝ) (distance : State → State → ℝ) (L : ℝ)
    (actions : State → List (BellmanAction State State M))
    (child : State → ℝ) (query : State) : ℝ :=
  finiteBellman initial distance L (actions query) child query

theorem finiteBellmanSystem_monotone {State : Type*} {M : ℕ}
    (initial : State → ℝ) (distance : State → State → ℝ) (L : ℝ)
    (actions : State → List (BellmanAction State State M)) :
    Monotone (finiteBellmanSystem initial distance L actions) := by
  intro child child' hchild query
  exact finiteBellman_mono initial distance L (actions query) hchild query

theorem finiteBellmanSystem_le_initial {State : Type*} {M : ℕ}
    (initial : State → ℝ) (distance : State → State → ℝ) (L : ℝ)
    (actions : State → List (BellmanAction State State M)) (child : State → ℝ) :
    finiteBellmanSystem initial distance L actions child ≤ initial := by
  intro query
  exact finiteBellman_le_fallback initial distance L (actions query) child query

theorem warmup_nonincreasing {State : Type*}
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (hmono : Monotone operator) (hfirst : operator initial ≤ initial) :
    ∀ t, warmup operator initial (t + 1) ≤ warmup operator initial t := by
  intro t
  induction t with
  | zero => exact hfirst
  | succ t ih => exact hmono ih

theorem warmup_lower {State : Type*}
    (operator : (State → ℝ) → State → ℝ) (initial lower : State → ℝ)
    (hinit : lower ≤ initial)
    (hpreserve : ∀ value, lower ≤ value → lower ≤ operator value) :
    ∀ t, lower ≤ warmup operator initial t := by
  intro t
  induction t with
  | zero => exact hinit
  | succ t ih => exact hpreserve _ ih

theorem finite_bellman_warmup_nonincreasing {State : Type*} {M : ℕ}
    (initial : State → ℝ) (distance : State → State → ℝ) (L : ℝ)
    (actions : State → List (BellmanAction State State M)) :
    ∀ t, warmup (finiteBellmanSystem initial distance L actions) initial (t + 1) ≤
      warmup (finiteBellmanSystem initial distance L actions) initial t :=
  warmup_nonincreasing _ _ (finiteBellmanSystem_monotone initial distance L actions)
    (finiteBellmanSystem_le_initial initial distance L actions initial)

noncomputable def warmupAverage {State : Type*}
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (T : ℕ) (state : State) : ℝ :=
  (∑ t ∈ range T, warmup operator initial t state) / T

theorem warmup_average_sandwich {State : Type*}
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (T : ℕ) (hT : 0 < T) (hmono : Monotone operator)
    (hfirst : operator initial ≤ initial) (state : State) :
    warmup operator initial T state ≤ warmupAverage operator initial T state ∧
      warmupAverage operator initial T state ≤ initial state := by
  have hanti : Antitone (fun t => warmup operator initial t state) :=
    antitone_nat_of_succ_le fun t => warmup_nonincreasing operator initial hmono hfirst t state
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · apply (le_div_iff₀ hTr).2
    have hsum := sum_le_sum (s := range T) fun t ht => hanti (show t ≤ T from (mem_range.mp ht).le)
    simpa only [sum_const, card_range, nsmul_eq_mul, mul_comm] using hsum
  · apply (div_le_iff₀ hTr).2
    have hsum := sum_le_sum (s := range T) fun t _ => hanti (Nat.zero_le t)
    simpa only [sum_const, card_range, nsmul_eq_mul, warmup, mul_comm] using hsum

/-- Averaging the actual one-step action inequality gives the warmup
mass slack, with the exact endpoint correction before its simplification
to the nonnegative initial-cone charge. -/
theorem warmup_average_action_bound {State ι : Type*} [Fintype ι]
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (T : ℕ) (hT : 0 < T) (parent : State) (child : ι → State) (charge : ℝ)
    (haction : ∀ t < T, warmup operator initial (t + 1) parent ≤
      charge + ∑ i, warmup operator initial t (child i)) :
    warmupAverage operator initial T parent -
        (initial parent - warmup operator initial T parent) / T ≤
      charge + ∑ i, warmupAverage operator initial T (child i) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have htelAll : ∀ K : ℕ, (∑ t ∈ range K, warmup operator initial t parent) -
      (∑ t ∈ range K, warmup operator initial (t + 1) parent) =
        initial parent - warmup operator initial K parent := by
    intro K
    induction K with
    | zero => simp [warmup]
    | succ K ih =>
      rw [sum_range_succ, sum_range_succ]
      linarith
  have htel := htelAll T
  have hsum := sum_le_sum (s := range T) fun t ht => haction t (mem_range.mp ht)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm] at hsum
  unfold warmupAverage
  rw [← sub_div, ← sum_div]
  apply (div_le_iff₀ hTr).2
  have hright : (charge + (∑ i, ∑ t ∈ range T,
      warmup operator initial t (child i)) / T) * T =
        (T : ℝ) * charge + ∑ i, ∑ t ∈ range T, warmup operator initial t (child i) := by
    field_simp
  rw [hright, ← htel]
  linarith

end EditApproximation

end OAI
