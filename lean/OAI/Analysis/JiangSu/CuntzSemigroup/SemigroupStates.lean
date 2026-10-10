import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

noncomputable section
namespace Pureness
namespace OrderedSemigroup
open scoped ENNReal

variable {S : Type*} [AddCommMonoid S] [PartialOrder S]

def IsNormalizedState (u : S) (f : S → ℝ≥0∞) : Prop :=
  f 0 = 0 ∧ (∀ a b, f (a+b) = f a + f b) ∧ Monotone f ∧ f u = 1

abbrev StateSpace (u : S) := {f : S → ℝ≥0∞ // IsNormalizedState u f}

namespace StateSpace
variable {u : S}
def toAddHom (f : StateSpace u) : S →+ ℝ≥0∞ where
  toFun := f.1
  map_zero' := f.2.1
  map_add' := f.2.2.1

lemma monotone (f : StateSpace u) : Monotone f.1 := f.2.2.2.1
@[simp] lemma at_unit (f : StateSpace u) : f.1 u = 1 := f.2.2.2.2
@[simp] lemma at_zero (f : StateSpace u) : f.1 0 = 0 := f.2.1
@[simp] lemma at_add (f : StateSpace u) (a b : S) : f.1 (a+b) = f.1 a + f.1 b := f.2.2.1 a b
@[simp] lemma at_nsmul (f : StateSpace u) (a : S) (n : ℕ) : f.1 (n • a) = n • f.1 a :=
  map_nsmul f.toAddHom n a

lemma continuous_eval (a : S) : Continuous (fun f : StateSpace u => f.1 a) :=
  (continuous_apply a).comp continuous_subtype_val
end StateSpace

lemma isClosed_normalizedStates (u : S) : IsClosed {f : S → ℝ≥0∞ | IsNormalizedState u f} := by
  have hzero : IsClosed {f : S → ℝ≥0∞ | f 0 = 0} := isClosed_eq (continuous_apply 0) continuous_const
  have hadd : IsClosed {f : S → ℝ≥0∞ | ∀ a b, f (a+b) = f a + f b} :=
    by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (continuous_apply (a+b)) ((continuous_apply a).add (continuous_apply b))
  have hmono : IsClosed {f : S → ℝ≥0∞ | Monotone f} := by
    simp only [Monotone, Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun (_ : a ≤ b) =>
      isClosed_le (continuous_apply a) (continuous_apply b)
  have hunit : IsClosed {f : S → ℝ≥0∞ | f u = 1} := isClosed_eq (continuous_apply u) continuous_const
  exact hzero.inter (hadd.inter (hmono.inter hunit))

instance compactSpace_states (u : S) : CompactSpace (StateSpace u) :=
  isCompact_iff_compactSpace.mp (isClosed_normalizedStates u).isCompact

variable [IsOrderedAddMonoid S]

def principalIdeal (u : S) : AddSubmonoid S where
  carrier := {a | ∃ n : ℕ, a ≤ n • u}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n+m, by simpa only [add_nsmul] using add_le_add hn hm⟩

lemma mem_principalIdeal (u : S) : u ∈ principalIdeal u := ⟨1, by simp⟩
lemma principalIdeal_downward {u a b : S} (h : a ≤ b) (hb : b ∈ principalIdeal u) :
    a ∈ principalIdeal u := by
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, h.trans hn⟩

lemma add_mem_principalIdeal_iff (hzero : ∀ a : S, 0 ≤ a) (u a b : S) :
    a+b ∈ principalIdeal u ↔ a ∈ principalIdeal u ∧ b ∈ principalIdeal u := by
  constructor
  · intro h
    exact ⟨principalIdeal_downward (le_add_of_nonneg_right (hzero b)) h,
      principalIdeal_downward (le_add_of_nonneg_left (hzero a)) h⟩
  · exact fun h => (principalIdeal u).add_mem h.1 h.2

theorem state_finite_on_principalIdeal {u a : S} (f : StateSpace u)
    (ha : a ∈ principalIdeal u) : f.1 a ≠ ⊤ := by
  obtain ⟨n, hn⟩ := ha
  have h := f.monotone hn
  rw [f.at_nsmul, f.at_unit, nsmul_eq_mul, mul_one] at h
  exact ne_top_of_le_ne_top (by simp) h

def extendState (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (f : StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u)) : StateSpace u := by
  classical
  let g : S → ℝ≥0∞ := fun a => if ha : a ∈ principalIdeal u then f.1 ⟨a,ha⟩ else ⊤
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · simp only [g, dite_eq_left (principalIdeal u).zero_mem]
    exact f.at_zero
  · intro a b
    by_cases ha : a ∈ principalIdeal u <;> by_cases hb : b ∈ principalIdeal u
    · simp only [g, dite_eq_left ha, dite_eq_left hb,
        dite_eq_left ((principalIdeal u).add_mem ha hb)]
      exact f.at_add ⟨a,ha⟩ ⟨b,hb⟩
    · have hab : a+b ∉ principalIdeal u := fun h => hb ((add_mem_principalIdeal_iff hzero u a b).mp h).2
      simp [g, ha, hb, hab]
    · have hab : a+b ∉ principalIdeal u := fun h => ha ((add_mem_principalIdeal_iff hzero u a b).mp h).1
      simp [g, ha, hb, hab]
    · have hab : a+b ∉ principalIdeal u := fun h => ha ((add_mem_principalIdeal_iff hzero u a b).mp h).1
      simp [g, ha, hb, hab]
  · intro a b hab
    by_cases hb : b ∈ principalIdeal u
    · have ha := principalIdeal_downward hab hb
      simp only [g, dite_eq_left ha, dite_eq_left hb]
      exact f.monotone hab
    · simp [g, hb]
  · simp only [g, dite_eq_left (mem_principalIdeal u)]
    exact f.at_unit

lemma extendState_apply (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (f : StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u))
    (a : principalIdeal u) : (extendState hzero u f).1 a = f.1 a := by
  simp only [extendState, dite_eq_left a.2]

end OrderedSemigroup

namespace OrderedSemigroup
open scoped ENNReal

variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

def restrictState (u : S) (f : StateSpace u) :
    StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u) :=
  ⟨fun a => f.1 a, f.at_zero, fun a b => f.at_add a b, fun _ _ h => f.monotone h, f.at_unit⟩

theorem restrict_extendState (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (f : StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u)) :
    restrictState u (extendState hzero u f) = f := by
  apply Subtype.ext
  funext a
  exact extendState_apply hzero u f a

theorem nonempty_states_iff_principalIdeal (hzero : ∀ a : S, 0 ≤ a) (u : S) :
    Nonempty (StateSpace u) ↔
      Nonempty (StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u)) :=
  ⟨fun ⟨f⟩ => ⟨restrictState u f⟩, fun ⟨f⟩ => ⟨extendState hzero u f⟩⟩

theorem state_gap_iff_principalIdeal (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (a : principalIdeal u) :
    (∀ f : StateSpace u, f.1 a < 1) ↔
      ∀ f : StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u), f.1 a < 1 := by
  constructor
  · intro h f
    simpa only [extendState_apply] using h (extendState hzero u f)
  · intro h f
    exact h (restrictState u f)

omit [IsOrderedAddMonoid S] in
theorem uniform_state_gap [IsOrderedAddMonoid S] (u a : S)
    (h : ∀ f : StateSpace u, f.1 a < 1) :
    ∃ r : ℝ≥0∞, r < 1 ∧ ∀ f : StateSpace u, f.1 a ≤ r := by
  classical
  by_cases hn : Nonempty (StateSpace u)
  · obtain ⟨f₀⟩ := hn
    obtain ⟨f, _, hf⟩ := isCompact_univ.exists_isMaxOn
      (⟨f₀, Set.mem_univ _⟩ : (Set.univ : Set (StateSpace u)).Nonempty)
      (StateSpace.continuous_eval a).continuousOn
    exact ⟨f.1 a, h f, fun g => hf (Set.mem_univ g)⟩
  · exact ⟨0, zero_lt_one, fun f => False.elim (hn ⟨f⟩)⟩

def stateRealOnIdeal (u : S) (f : StateSpace u) : principalIdeal u →+ ℝ where
  toFun a := (f.1 a).toReal
  map_zero' := by simp
  map_add' a b := by
    change (f.1 (a.1+b.1)).toReal = _
    rw [f.at_add]
    exact ENNReal.toReal_add (state_finite_on_principalIdeal f a.2)
      (state_finite_on_principalIdeal f b.2)

theorem stateRealOnIdeal_monotone (u : S) (f : StateSpace u) :
    Monotone (stateRealOnIdeal u f) := by
  intro a b hab
  exact ENNReal.toReal_mono (state_finite_on_principalIdeal f b.2) (f.monotone hab)

theorem stateRealOnIdeal_unit (u : S) (f : StateSpace u) :
    stateRealOnIdeal u f ⟨u, mem_principalIdeal u⟩ = 1 := by
  change (f.1 u).toReal = 1
  simp

omit [IsOrderedAddMonoid S] in
theorem no_state_of_properlyInfinite [IsOrderedAddMonoid S] (u : S) (h : 2 • u ≤ u) :
    IsEmpty (StateSpace u) := by
  refine ⟨fun f => ?_⟩
  have hb := f.monotone h
  rw [f.at_nsmul, f.at_unit] at hb
  norm_num [nsmul_eq_mul] at hb

end OrderedSemigroup
end Pureness
end

end OAI
