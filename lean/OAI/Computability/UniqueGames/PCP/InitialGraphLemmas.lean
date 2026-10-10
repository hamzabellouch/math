import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.NameCompaction

namespace OAI

section

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.InitialGraph

open Target

abbrev Label := Bool × Bool × Bool
abbrev Vertex (F : Formula) := (Fin F.variables ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableVertex (F : Formula) (v : Fin F.variables) : Vertex F := .inl (.inl v)
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Vertex F := .inl (.inr i)
def dummyVertex (F : Formula) : Vertex F := .inr ()
def dummyDart (F : Formula) : Dart F := .inr ()

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩
instance dartNonempty (F : Formula) : Nonempty (Dart F) := ⟨dummyDart F⟩

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)
def variableLabel (value : Bool) : Label := (value, false, false)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

theorem raw_forward (F : Formula) (labeling : Vertex F → Label) (event : RandomEvent F) :
    (raw F).edgeSatisfied labeling (.inl (event, false)) =
      incidenceAccept F event (labeling (clauseVertex F event.1))
        (labeling (variableVertex F (nameAt (clauseAt F event.1) event.2))) := rfl

theorem incidenceAccept_true (F : Formula) (event : RandomEvent F) (a b : Label)
    (h : incidenceAccept F event a b = true) :
    localSatisfies (clauseAt F event.1) (toClauseAnswer a) = true ∧
      answerAt (toClauseAnswer a) event.2 = b.1 := by
  simp only [incidenceAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

def honestLabeling (F : Formula) (A : Fin F.variables → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

theorem incidence_honest (F : Formula) (A : Fin F.variables → Bool)
    (sat : ∀ c ∈ F.clauses, c.eval A = true) (event : RandomEvent F) :
    incidenceAccept F event (honestLabeling F A (clauseVertex F event.1))
      (honestLabeling F A (variableVertex F (nameAt (clauseAt F event.1) event.2))) = true := by
  have hc : (clauseAt F event.1).eval A = true := sat _ (List.getElem_mem _)
  simp [incidenceAccept, honestLabeling, clauseVertex, variableVertex, variableLabel,
    variableValid, honest_satisfies, honest_answerAt, hc]

theorem raw_completeness (F : Formula) (sat : F.Satisfiable) : (raw F).Satisfiable := by
  rcases sat with ⟨A, hA⟩
  refine ⟨honestLabeling F A, fun d => ?_⟩
  cases d with
  | inl pair =>
    rcases pair with ⟨event, orientation⟩
    cases orientation <;> exact incidence_honest F A hA event
  | inr u => rfl

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

theorem raw_reflects (F : Formula) (sat : (raw F).Satisfiable) : F.Satisfiable := by
  rcases sat with ⟨labeling, hlabeling⟩
  let A : Fin F.variables → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  refine ⟨A, fun c hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.variables + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

abbrev CompactVertex (F : Formula) := Vertex (NameCompaction.compact F)
abbrev CompactDart (F : Formula) := Dart (NameCompaction.compact F)

def build (F : Formula) : ConstraintGraph (CompactVertex F) (CompactDart F) Label :=
  raw (NameCompaction.compact F)

theorem build_satisfiable_iff (F : Formula) : (build F).Satisfiable ↔ F.Satisfiable := by
  exact (raw_satisfiable_iff (NameCompaction.compact F)).trans
    (NameCompaction.compact_satisfiable_iff F)

theorem build_vertex_bound (F : Formula) :
    Fintype.card (CompactVertex F) ≤ 4 * F.clauses.length + 1 := by
  have h := NameCompaction.compact_active_bound F
  simp only [CompactVertex, card_vertex, NameCompaction.compact_clause_count]
  omega

theorem build_dart_count (F : Formula) :
    Fintype.card (CompactDart F) = 6 * F.clauses.length + 1 := by
  simp only [CompactDart, card_dart, NameCompaction.compact_clause_count]

/-- The initial inverse-size gap follows from the original unsatisfiability,
without a PCP, bounded-degree, or constant-gap premise. -/
theorem build_initial_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : CompactVertex F → Label) : 1 ≤ (build F).rejectionCount labeling := by
  apply ConstraintGraph.rejectionCount_positive
  intro h
  exact unsat ((build_satisfiable_iff F).mp h)

theorem build_inverse_size_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : CompactVertex F → Label) :
    Fintype.card (CompactDart F) ≤
      (6 * F.clauses.length + 1) * (build F).rejectionCount labeling := by
  rw [build_dart_count]
  simpa only [Nat.mul_one] using
    Nat.mul_le_mul_left (6 * F.clauses.length + 1) (build_initial_gap F unsat labeling)

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

section

/-! Actual indicator counting and the second-moment rejection estimate.
The hypotheses describe event inclusion and moment bounds, while the
Cauchy--Schwarz conclusion and all positivity properties are proved here. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_sq (p : Prop) : bit p ^ 2 = bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_mul (p q : Prop) : bit p * bit q = bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, hpq hp]
  · have hz : bit p = 0 := by simp [bit, hp]
    rw [hz]
    exact bit_nonneg q

theorem hits_nonneg {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ hits E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := Finset.expect_nonneg (fun ω _ => hf ω)

theorem mean_hits {I Ω : Type*} [Fintype I] [Fintype Ω] (E : I → Ω → Prop) :
    mean (hits E) = ∑ i, mean (fun ω => bit (E i ω)) := by
  exact Finset.expect_sum_comm _ _ _

theorem second_moment_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E : I → Ω → Prop) :
    mean (fun ω => hits E ω ^ 2) =
      ∑ i, ∑ j, mean (fun ω => bit (E i ω ∧ E j ω)) := by
  simp only [hits, pow_two, Finset.sum_mul, Finset.mul_sum, bit_mul,
    mean, Finset.expect_sum_comm]
  exact Finset.sum_comm

theorem mean_witness_sq_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω) :
    mean (hits W) ^ 2 ≤
      mean (fun ω => bit (reject ω)) * mean (fun ω => hits E ω ^ 2) := by
  classical
  have hNH (ω : Ω) : hits W ω ≤ hits E ω :=
    Finset.sum_le_sum (fun i _ => bit_mono (hWE i ω))
  have hzero (ω : Ω) (hr : ¬ reject ω) : hits W ω = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : ¬ W i ω := fun h => hr (hWR i ω h)
    simp [bit, hw]
  have hsupport (ω : Ω) : bit (reject ω) * hits W ω = hits W ω := by
    by_cases hr : reject ω
    · simp [bit, hr]
    · rw [hzero ω hr]
      simp
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => bit (reject ω)) (hits W)
  have hsquares : mean (fun ω => hits W ω ^ 2) ≤ mean (fun ω => hits E ω ^ 2) := by
    apply Finset.expect_le_expect
    intro ω _
    simpa only [pow_two] using
      (mul_le_mul (hNH ω) (hNH ω) (hits_nonneg W ω) (hits_nonneg E ω))
  calc
    _ ≤ mean (fun ω => bit (reject ω)) * mean (fun ω => hits W ω ^ 2) := by
      simpa only [mean, hsupport, bit_sq] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares
      (mean_nonneg _ (fun ω => bit_nonneg (reject ω)))

theorem rejection_lower_bound {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a ≤ mean (hits W))
    (hsecond : mean (fun ω => hits E ω ^ 2) ≤ b) :
    a ^ 2 / b ≤ mean (fun ω => bit (reject ω)) := by
  have hN : 0 ≤ mean (hits W) := mean_nonneg _ (hits_nonneg W)
  have hρ : 0 ≤ mean (fun ω => bit (reject ω)) :=
    mean_nonneg _ (fun ω => bit_nonneg (reject ω))
  have haSq : a ^ 2 ≤ mean (hits W) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfirst hfirst ha.le hN
  have hCS := mean_witness_sq_le E W reject hWE hWR
  apply (div_le_iff₀ hb).2
  exact haSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsecond hρ))

end UniqueGamesTheorem.Foundations.PCP.PoweringMoment

end

end

section

/-!
# The scalar bound for all positive error densities

The first lemma bounds a ratio using only a nonnegative coefficient bounded
by a positive cutoff. The second applies it to a positive natural count and
the first- and second-moment expressions in the powering argument.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringNumeric

/-- A bounded nonnegative coefficient gives the required ratio bound both
below and above the cutoff `1/t`. -/
theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

/-- A positive natural count supplies `0 ≤ m - 1`. After cancelling the
positive mass `m*ε`, the ratio of moments dominates a constant times
`min ε (1/t)`. No sign condition on `α` is needed for its fourth power. -/
theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end UniqueGamesTheorem.Foundations.PCP.PoweringNumeric

end

section

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

/-- Exposes the first dart and the independent remaining port word. -/
def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Advance across the first edge while retaining its reverse port. -/
def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

/-- Relabeling time coordinates is a bijection on actual port words. -/
def permutePorts {t : Nat} (σ : Fin t ≃ Fin t) : Walk V D t ≃ Walk V D t where
  toFun w := (w.1, fun j => w.2 (σ j))
  invFun w := (w.1, fun j => w.2 (σ.symm j))
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.apply_symm_apply j)
  right_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.symm_apply_apply j)

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

theorem natCard_walk [Finite V] [Finite D] (n : Nat) :
    Nat.card (Walk V D n) = Nat.card V * Nat.card D ^ n := by
  simp [Walk, Nat.card_prod, Nat.card_fun]

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

/-- The dart at the indicated time, computed by the actual preceding steps. -/
def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

/-- Isolate any actual path edge. Previously traversed ports are replaced by
their arrival ports, so the change of coordinates remains invertible. -/
def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

theorem pivotEquiv_zero_apply (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    pivotEquiv G n 0 w = ((w.1, w.2 0), fun j => w.2 j.succ) := by
  cases n <;> rfl

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def projectedFiberEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (a : E) : {x // f x = a} ≃ R where
  toFun x := (e x.val).2
  invFun r := ⟨e.symm (a, r), by
    exact (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (a, r)))⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext ((he x.val).trans x.property).symm rfl
  right_inv r := congrArg Prod.snd (e.apply_symm_apply (a, r))

def projectedEventEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (P : E → Prop) :
    {x // P (f x)} ≃ ({a // P a} × R) where
  toFun x := (⟨(e x.val).1, by rw [he]; exact x.property⟩, (e x.val).2)
  invFun ar := ⟨e.symm (ar.1.val, ar.2), by
    have h : f (e.symm (ar.1.val, ar.2)) = ar.1.val :=
      (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2)))
    simpa only [h] using ar.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv ar := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2))
    · change (e (e.symm (ar.1.val, ar.2))).2 = ar.2
      exact congrArg Prod.snd (e.apply_symm_apply (ar.1.val, ar.2))

/-- Every fixed dart has exactly the same number of path realizations. -/
theorem natCard_edgeAt_fiber (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (a : Edge V D) :
    Nat.card {w : Walk V D (n + 1) // edgeAt G n w k = a} = Nat.card D ^ n := by
  calc
    _ = Nat.card (Fin n → D) := Nat.card_congr
      (projectedFiberEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) a)
    _ = _ := by simp [Nat.card_fun]

/-- The exact event count underlying the uniform-pivot probability law. -/
theorem natCard_edgeAt_event (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (P : Edge V D → Prop) :
    Nat.card {w : Walk V D (n + 1) // P (edgeAt G n w k)} =
      Nat.card {a : Edge V D // P a} * Nat.card D ^ n := by
  calc
    _ = Nat.card ({a : Edge V D // P a} × (Fin n → D)) := Nat.card_congr
      (projectedEventEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) P)
    _ = _ := by simp [Nat.card_prod, Nat.card_fun]

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_zero (G : PortGraph V D) (n : Nat)
    (v : V) (r : Fin n → D) : leftFromPivot G n 0 v r = v := by
  cases n <;> rfl

theorem rightFromPivot_zero (G : PortGraph V D) (n : Nat)
    (e : Edge V D) (r : Fin n → D) :
    rightFromPivot G n 0 e r = wordEnd G n (next G e.1 e.2) r := by
  cases n <;> rfl

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringWalks

end

section

/-!
Cloud replacement for arbitrary finite constraint graphs. The new vertices are
the old darts; internal ports enforce equality inside each cloud, and one
external port applies the original constraint. Dummy loop darts allow padding
each cloud independently before replacement.

The supplied cloud port graphs are explicit parameters; no expansion or
soundness claim is assumed.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

/-- The darts departing a specified vertex. -/
abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

/-- Conjugate the disjoint union of cloud rotations into global dart coordinates. -/
def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

/-- Internal ports rotate inside a cloud; the extra port reverses an old dart. -/
def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

/-- The equality constraints and inherited original constraints on the actual rotation. -/
def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem replacement_satisfiable [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (h : G.Satisfiable) : (replacementGraph G H).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact ⟨liftLabel G labeling, replacement_complete G H labeling hlabeling⟩

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Lifted labels reject precisely one external dart for each rejected original dart. -/
theorem replacement_rejectionCount [Fintype E] [Fintype D] [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) :
    (replacementGraph G H).rejectionCount (liftLabel G labeling) =
      G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

/-- Additional darts are attached to their specified original vertex. -/
abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

/-- Dummy darts are self-reversing loops with an always-accepting constraint. -/
def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

theorem padded_satisfiable (G : ConstraintGraph V E A) (dummy : V → Type*)
    (h : G.Satisfiable) : (paddedGraph G dummy).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact ⟨labeling, padded_complete G dummy labeling hlabeling⟩

theorem card_paddedDart [Fintype V] [Fintype E] (G : ConstraintGraph V E A)
    (dummy : V → Type*) [∀ v, Fintype (dummy v)] :
    Fintype.card (PaddedDart G dummy) =
      Fintype.card E + ∑ v, Fintype.card (dummy v) := by
  rw [Fintype.card_sum, Fintype.card_sigma]

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type]
  simp
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

theorem paddedReplacement_rejectionCount
    [Fintype V] [Fintype E] [Fintype D] [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) (labeling : V → A) :
    (paddedReplacementGraph G dummy H).rejectionCount
        (liftLabel (paddedGraph G dummy) labeling) = G.rejectionCount labeling :=
  (replacement_rejectionCount (paddedGraph G dummy) H labeling).trans
    (padded_rejectionCount G dummy labeling)

/-- Omitting all dummy darts recovers exactly the original dart set. -/
def noDummyEquiv (G : ConstraintGraph V E A) :
    PaddedDart G (fun _ : V => Empty) ≃ E where
  toFun z := match z with
    | Sum.inl e => e
    | Sum.inr z => Empty.elim z.2
  invFun := Sum.inl
  left_inv := by
    intro z
    cases z with
    | inl e => rfl
    | inr z => exact Empty.elim z.2
  right_inv _ := rfl

end UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

end

end OAI
