import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.UnitTime
import OAI.Combinatorics.TriangleRemoval.Probability.ProductPMF

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O P : Type*}

def bind : ExposureTree K V O → (O → ExposureTree K V P) → ExposureTree K V P
  | .done o, f => f o
  | .ask k g, f => .ask k (fun v => bind (g v) f)

@[simp] theorem evaluate_bind (ω : K → V) (A : ExposureTree K V O)
    (f : O → ExposureTree K V P) : evaluate ω (bind A f) = evaluate ω (f (evaluate ω A)) := by
  induction A with
  | done o => rfl
  | ask k g ih => exact ih (ω k)

@[simp] theorem fresh_bind (ν : K → PMF V) (A : ExposureTree K V O)
    (f : O → ExposureTree K V P) : fresh ν (bind A f) = (fresh ν A).bind (fun o => fresh ν (f o)) := by
  induction A with
  | done o => simp [bind, fresh]
  | ask k g ih => simp only [bind, fresh, ih, PMF.bind_bind]

def exposeValues : List K → ExposureTree K V (List (K × V))
  | [] => .done []
  | k :: ks => .ask k (fun v => bind (exposeValues ks) (fun xs => .done ((k, v) :: xs)))

def checkNone : List (ExposureTree K V Bool) → ExposureTree K V Bool
  | [] => .done true
  | A :: As => bind A (fun b => if b then .done false else checkNone As)

end ExposureTree

noncomputable def trueProbability (p : PMF Bool) : ℝ := (p true).toReal
noncomputable def falseProbability (p : PMF Bool) : ℝ := (p false).toReal

theorem bool_probability_sum (p : PMF Bool) : trueProbability p + falseProbability p = 1 := by
  have hh := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at hh
  have hr := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_add (p.apply_ne_top _) (p.apply_ne_top _),
    ENNReal.toReal_one, trueProbability, falseProbability] using hr

theorem trueProbability_nonneg (p : PMF Bool) : 0 ≤ trueProbability p := ENNReal.toReal_nonneg

theorem falseProbability_nonneg (p : PMF Bool) : 0 ≤ falseProbability p := ENNReal.toReal_nonneg

theorem trueProbability_le_one (p : PMF Bool) : trueProbability p ≤ 1 := by
  have := bool_probability_sum p
  have := falseProbability_nonneg p
  linarith

@[simp] theorem trueProbability_pure (b : Bool) : trueProbability (PMF.pure b) = if b then 1 else 0 := by
  cases b <;> simp [trueProbability]

@[simp] theorem falseProbability_pure (b : Bool) : falseProbability (PMF.pure b) = if b then 0 else 1 := by
  cases b <;> simp [falseProbability]

theorem trueProbability_bind {V : Type*} [Fintype V] (p : PMF V) (f : V → PMF Bool) :
    trueProbability (p.bind f) = ∑ v, (p v).toReal * trueProbability (f v) := by
  unfold trueProbability
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro v _
    exact ENNReal.mul_ne_top (p.apply_ne_top v) ((f v).apply_ne_top true)

theorem trueProbability_bool_bind (p : PMF Bool) (f : Bool → PMF Bool) :
    trueProbability (p.bind f) = trueProbability p * trueProbability (f true) +
      falseProbability p * trueProbability (f false) := by
  rw [trueProbability_bind, Fintype.sum_bool]
  rfl

namespace ExposureTree
variable {K V : Type*}

theorem fresh_checkNone_true (ν : K → PMF V) (As : List (ExposureTree K V Bool)) :
    trueProbability (fresh ν (checkNone As)) = (As.map (fun A => falseProbability (fresh ν A))).prod := by
  induction As with
  | nil => simp [checkNone, fresh]
  | cons A As ih =>
    rw [checkNone, fresh_bind, trueProbability_bool_bind]
    simp [fresh, ih]

theorem exposeValues_product [Fintype V] (ν : K → PMF V) (ks : List K)
    (C : List (K × V) → ExposureTree K V Bool) (h : K → V → ℝ)
    (hc : ∀ xs, trueProbability (fresh ν (C xs)) = (xs.map (fun p => h p.1 p.2)).prod) :
    trueProbability (fresh ν (ExposureTree.bind (exposeValues ks) C)) =
      (ks.map (fun k => ∑ v, (ν k v).toReal * h k v)).prod := by

  suffices hh : ∀ (ks : List K) (a : ℝ) (C : List (K × V) → ExposureTree K V Bool),
      (∀ xs, trueProbability (fresh ν (C xs)) = a * (xs.map (fun p => h p.1 p.2)).prod) →
      trueProbability (fresh ν (ExposureTree.bind (exposeValues ks) C)) =
        a * (ks.map (fun k => ∑ v, (ν k v).toReal * h k v)).prod by
    simpa only [one_mul] using hh ks 1 C (by simpa only [one_mul] using hc)
  intro ks
  induction ks with
  | nil =>
    intro a C hh
    simpa only [exposeValues, bind, List.map_nil, List.prod_nil] using hh []
  | cons k ks ih =>
    intro a C hh
    simp only [exposeValues, bind, fresh, trueProbability_bind]
    have hx : ∀ v, trueProbability (fresh ν
        (bind (bind (exposeValues ks) (fun xs => .done ((k, v) :: xs))) C)) =
        (a * h k v) * (ks.map (fun k => ∑ v, (ν k v).toReal * h k v)).prod := by
      intro v
      have hassoc : bind (bind (exposeValues (V := V) ks) (fun xs => .done ((k, v) :: xs))) C =
          bind (exposeValues ks) (fun xs => C ((k, v) :: xs)) := by
        induction exposeValues (V := V) ks with
        | done xs => rfl
        | ask k f hi => simp only [bind, hi]
      rw [hassoc]
      apply ih
      intro xs
      rw [hh]
      simp only [List.map_cons, List.prod_cons]
      ring
    simp only [hx, List.map_cons, List.prod_cons]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring

def exposeLabeled {A : Type*} (key : A → K) : List A → ExposureTree K V (List (A × V))
  | [] => .done []
  | a :: as => .ask (key a) (fun v => bind (exposeLabeled key as)
      (fun xs => .done ((a, v) :: xs)))

theorem exposeLabeled_product {A : Type*} [Fintype V] (ν : K → PMF V) (key : A → K) (ks : List A)
    (C : List (A × V) → ExposureTree K V Bool) (h : A → V → ℝ)
    (hc : ∀ xs, trueProbability (fresh ν (C xs)) = (xs.map (fun p => h p.1 p.2)).prod) :
    trueProbability (fresh ν (ExposureTree.bind (exposeLabeled key ks) C)) =
      (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod := by

  suffices hh : ∀ (ks : List A) (a : ℝ) (C : List (A × V) → ExposureTree K V Bool),
      (∀ xs, trueProbability (fresh ν (C xs)) = a * (xs.map (fun p => h p.1 p.2)).prod) →
      trueProbability (fresh ν (ExposureTree.bind (exposeLabeled key ks) C)) =
        a * (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod by
    simpa only [one_mul] using hh ks 1 C (by simpa only [one_mul] using hc)
  intro ks
  induction ks with
  | nil =>
    intro a C hh
    simpa only [exposeLabeled, bind, List.map_nil, List.prod_nil] using hh []
  | cons k ks ih =>
    intro a C hh
    simp only [exposeLabeled, bind, fresh, trueProbability_bind]
    have hx : ∀ v, trueProbability (fresh ν
        (bind (bind (exposeLabeled key ks) (fun xs => .done ((k, v) :: xs))) C)) =
        (a * h k v) * (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod := by
      intro v
      have hassoc : bind (bind (exposeLabeled (V := V) key ks) (fun xs => .done ((k, v) :: xs))) C =
          bind (exposeLabeled key ks) (fun xs => C ((k, v) :: xs)) := by
        induction exposeLabeled (V := V) key ks with
        | done xs => rfl
        | ask k f hi => simp only [bind, hi]
      rw [hassoc]
      apply ih
      intro xs
      rw [hh]
      simp only [List.map_cons, List.prod_cons]
      ring
    simp only [hx, List.map_cons, List.prod_cons]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring

end ExposureTree

section GridQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def gridCandidates (H : τ → Finset ι) (focus : Finset ι) (parent : Option τ) :
    Finset (ι × τ) :=
  (focus.product Finset.univ).filter (fun p => p.1 ∈ H p.2 ∧ some p.2 ≠ parent)

noncomputable def gridQueryDepth (H : τ → Finset ι) (N : ℕ) :
    ℕ → ℕ → Finset ι → Option τ → ExposureTree τ (Fin N) Bool
  | 0, _, focus, parent =>
      ExposureTree.bind
        (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
        (fun _ => .done true)
  | d + 1, k, focus, parent =>
      ExposureTree.bind
        (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
        (fun values => ExposureTree.checkNone
          (((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
            (fun p => if p.2.val < k then
              gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)
              else .done false))))

noncomputable def gridPriorities (N : ℕ) [NeZero N] : τ → PMF (Fin N) :=
  fun _ => PMF.uniformOfFintype (Fin N)

noncomputable def gridAnswerProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) : ℝ :=
  trueProbability (ExposureTree.fresh (gridPriorities N) (gridQueryDepth H N d k focus parent))

theorem gridAnswerProbability_step (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N (d + 1) k focus parent =
      ∏ p ∈ gridCandidates H focus parent,
        ∑ u : Fin N, (1 / (N : ℝ)) *
          (if u.val < k then 1 - gridAnswerProbability H N d u.val
            ((H p.2).erase p.1) (some p.2) else 1) := by
  unfold gridAnswerProbability
  rw [gridQueryDepth]
  have hh := ExposureTree.exposeLabeled_product (gridPriorities (τ := τ) N) Prod.snd
    (gridCandidates H focus parent).toList
    (fun values => ExposureTree.checkNone
      (((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
        (fun p => if p.2.val < k then
          gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)
          else .done false))))
    (fun p u => if u.val < k then 1 - gridAnswerProbability H N d u.val
      ((H p.2).erase p.1) (some p.2) else 1) (by
      intro values
      rw [ExposureTree.fresh_checkNone_true, List.map_map]
      have hp := (List.mergeSort_perm values (fun a b => a.2.val ≤ b.2.val)).map
        (fun p => falseProbability (ExposureTree.fresh (gridPriorities N)
          (if p.2.val < k then gridQueryDepth H N d p.2.val
            ((H p.1.2).erase p.1.1) (some p.1.2) else .done false)))
      refine hp.prod_eq.trans ?_
      congr 1
      apply List.map_congr_left
      intro p _
      by_cases hpk : p.2.val < k
      · simp only [hpk, ite_true]
        have hb := bool_probability_sum (ExposureTree.fresh (gridPriorities N)
          (gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)))
        change falseProbability _ = 1 - trueProbability _
        linarith
      · simp [hpk, ExposureTree.fresh])
  convert hh using 1
  simp only [gridPriorities, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin, one_div]
  exact (Finset.prod_map_toList _ _).symm

@[simp] theorem gridAnswerProbability_zero (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N 0 k focus parent = 1 := by
  simp [gridAnswerProbability, gridQueryDepth, ExposureTree.fresh_bind,
    ExposureTree.fresh, PMF.bind_const]

theorem gridAnswerProbability_mem_unit (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N d k focus parent ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨trueProbability_nonneg _, trueProbability_le_one _⟩

theorem prod_gridCandidates {M : Type*} [CommMonoid M] (H : τ → Finset ι)
    (focus : Finset ι) (parent : Option τ) (f : ι × τ → M) :
    (∏ p ∈ gridCandidates H focus parent, f p) =
      ∏ e ∈ focus, ∏ T ∈ messageCandidates H e parent, f (e, T) := by
  simp only [gridCandidates, messageCandidates, Finset.prod_filter]
  exact Finset.prod_product _ _ _

theorem gridAnswerProbability_factor (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N d k focus parent =
      ∏ e ∈ focus, gridAnswerProbability H N d k {e} parent := by
  cases d with
  | zero => simp
  | succ d =>
    simp only [gridAnswerProbability_step, prod_gridCandidates, Finset.prod_singleton]

noncomputable def gridMessage (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (parent : Option τ) : ℝ :=
  gridAnswerProbability H N d k {e} parent

theorem uniform_grid_average (N : ℕ) [NeZero N] (k : ℕ) (f : Fin N → ℝ) :
    (∑ u : Fin N, (1 / (N : ℝ)) * (if u.val < k then 1 - f u else 1)) =
      1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), f u := by
  have hpoint : ∀ u : Fin N, (if u.val < k then 1 - f u else 1) =
      1 - (if u.val < k then f u else 0) := by
    intro u; split_ifs <;> ring
  simp only [hpoint, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
    Finset.sum_filter, mul_ite, mul_zero]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [mul_one_div_cancel hN]

theorem gridMessage_step (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (parent : Option τ) :
    gridMessage H N (d + 1) k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k),
          ∏ f ∈ (H T).erase e, gridMessage H N d u.val f (some T)) := by
  simp only [gridMessage, gridAnswerProbability_step, prod_gridCandidates,
    Finset.prod_singleton, uniform_grid_average]
  apply Finset.prod_congr rfl
  intro T _
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  exact gridAnswerProbability_factor H N d u.val ((H T).erase e) (some T)

namespace ExposureTree
@[simp] theorem checkNone_done_false {K V A : Type*} (xs : List A) :
    checkNone (xs.map (fun _ => (done false : ExposureTree K V Bool))) = done true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, checkNone, bind, Bool.false_eq_true,
      ↓reduceIte, ih]
end ExposureTree

theorem gridQueryDepth_threshold_zero (H : τ → Finset ι) (N d : ℕ)
    (focus : Finset ι) (parent : Option τ) :
    gridQueryDepth H N d 0 focus parent = gridQueryDepth H N 0 0 focus parent := by
  cases d with
  | zero => rfl
  | succ d => simp only [gridQueryDepth, Nat.not_lt_zero, ↓reduceIte,
      ExposureTree.checkNone_done_false]

theorem gridQueryDepth_stable (H : τ → Finset ι) (N k d d' : ℕ)
    (hd : k ≤ d) (hd' : k ≤ d') (focus : Finset ι) (parent : Option τ) :
    gridQueryDepth H N d k focus parent = gridQueryDepth H N d' k focus parent := by
  induction k using Nat.strong_induction_on generalizing d d' focus parent with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      exact (gridQueryDepth_threshold_zero H N d focus parent).trans
        (gridQueryDepth_threshold_zero H N d' focus parent).symm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d' ≠ 0)
      simp only [gridQueryDepth]
      congr 1
      funext values
      congr 1
      apply List.map_congr_left
      intro x _
      split_ifs with hx
      · exact ih x.2.val hx d d' (by omega) (by omega) _ _
      · rfl

theorem gridMessage_stable (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k d d' : ℕ) (hd : k ≤ d) (hd' : k ≤ d') (e : ι) (parent : Option τ) :
    gridMessage H N d k e parent = gridMessage H N d' k e parent := by
  unfold gridMessage gridAnswerProbability
  rw [gridQueryDepth_stable H N k d d' hd hd']

theorem gridMessage_exact (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (parent : Option τ) :
    gridMessage H N N k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k),
          ∏ f ∈ (H T).erase e, gridMessage H N N u.val f (some T)) := by
  rw [gridMessage_stable H N k N (N + 1) hk (by omega), gridMessage_step]

end GridQuery
end SharpTerminalLeave

end

end OAI
