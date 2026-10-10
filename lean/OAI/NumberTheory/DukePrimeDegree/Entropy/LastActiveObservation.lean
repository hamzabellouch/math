import OAI.NumberTheory.DukePrimeDegree.Entropy.RefinedReturnPartition
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Data.Finset.Max

namespace OAI

/-! # Countable observations at the last active scale

Summably small sections overlap only finitely often almost everywhere.
Recording the largest active scale therefore preserves arbitrarily fine
visits while keeping the observation alphabet countable.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

def lastActiveSection {Y : Type*} (S : ℕ → Set Y) (n : ℕ) : Set Y :=
  {x | x ∈ S n ∧ ∀ m, n < m → x ∉ S m}

lemma measurableSet_lastActiveSection {Y : Type*} [MeasurableSpace Y]
    {S : ℕ → Set Y} (hS : ∀ n, MeasurableSet (S n)) (n : ℕ) :
    MeasurableSet (lastActiveSection S n) := by
  have he : lastActiveSection S n = S n ∩ ⋂ m : ℕ, ⋂ (_ : n < m), (S m)ᶜ := by
    ext x
    simp only [lastActiveSection,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff]
  rw [he]
  exact (hS n).inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hS m).compl)

lemma lastActiveSection_unique {Y : Type*} {S : ℕ → Set Y} {n m : ℕ} {x : Y}
    (hn : x ∈ lastActiveSection S n) (hm : x ∈ lastActiveSection S m) : n=m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hn.2 m h hm.1).elim
  · exact h
  · exact (hm.2 n h hn.1).elim

lemma exists_lastActiveSection_of_finite {Y : Type*} {S : ℕ → Set Y} {x : Y}
    (hfin : {n | x ∈ S n}.Finite) {n : ℕ} (hn : x ∈ S n) :
    ∃ m, n ≤ m ∧ x ∈ lastActiveSection S m := by
  classical
  have hne : hfin.toFinset.Nonempty := ⟨n,hfin.mem_toFinset.mpr hn⟩
  let m := hfin.toFinset.max' hne
  have hm : x ∈ S m := hfin.mem_toFinset.mp (hfin.toFinset.max'_mem hne)
  refine ⟨m,hfin.toFinset.le_max' n (hfin.mem_toFinset.mpr hn),hm,?_⟩
  intro j hj hjS
  have hjle := hfin.toFinset.le_max' j (hfin.mem_toFinset.mpr hjS)
  exact (not_le_of_gt hj) hjle

def lastActiveObservationAtom {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) : Option (Σ n : ℕ, Fin (K n)) → Set Y
  | none => (⋃ n, lastActiveSection S n)ᶜ
  | some z => {x | x ∈ lastActiveSection S z.1 ∧ B z.1 x=z.2}

lemma lastActiveObservation_covers {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (x : Y) :
    ∃ z, x ∈ lastActiveObservationAtom S B z := by
  classical
  by_cases h : ∃ n, x ∈ lastActiveSection S n
  · obtain ⟨n,hn⟩ := h
    exact ⟨some ⟨n,B n x⟩,hn,rfl⟩
  · exact ⟨none,by simpa only [lastActiveObservationAtom,mem_compl_iff,mem_iUnion,not_exists] using h⟩

lemma lastActiveObservationAtom_unique {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n))
    {a b : Option (Σ n : ℕ, Fin (K n))} {x : Y}
    (ha : x ∈ lastActiveObservationAtom S B a)
    (hb : x ∈ lastActiveObservationAtom S B b) : a=b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => exact (ha (mem_iUnion.mpr ⟨b.1,hb.1⟩)).elim
  | some a =>
      cases b with
      | none => exact (hb (mem_iUnion.mpr ⟨a.1,ha.1⟩)).elim
      | some b =>
        rcases a with ⟨n,i⟩
        rcases b with ⟨m,j⟩
        have he := lastActiveSection_unique ha.1 hb.1
        dsimp at he
        subst m
        have hij : i=j := ha.2.symm.trans hb.2
        subst j
        rfl

def lastActiveObservation {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (x : Y) :
    Option (Σ n : ℕ, Fin (K n)) := (lastActiveObservation_covers S B x).choose

lemma lastActiveObservation_fiber {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (z : Option (Σ n : ℕ, Fin (K n))) :
    {x | lastActiveObservation S B x=z}=lastActiveObservationAtom S B z := by
  ext x
  constructor
  · intro hx
    have hm : x ∈ lastActiveObservationAtom S B (lastActiveObservation S B x) :=
      (lastActiveObservation_covers S B x).choose_spec
    rwa [hx] at hm
  · intro hx
    exact lastActiveObservationAtom_unique S B (lastActiveObservation_covers S B x).choose_spec hx

lemma measurable_lastActiveObservation {Y : Type*} [MeasurableSpace Y]
    {S : ℕ → Set Y} (hS : ∀ n, MeasurableSet (S n))
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n)) :
    @Measurable Y (Option (Σ n : ℕ, Fin (K n))) _ ⊤ (lastActiveObservation S B) := by
  let : MeasurableSpace (Option (Σ n : ℕ, Fin (K n))) := ⊤
  apply measurable_to_countable'
  intro z
  change MeasurableSet {x | lastActiveObservation S B x=z}
  rw [lastActiveObservation_fiber]
  cases z with
  | none => exact (MeasurableSet.iUnion (measurableSet_lastActiveSection hS)).compl
  | some z =>
      exact (measurableSet_lastActiveSection hS z.1).inter
        (hB z.1 (measurableSet_singleton z.2))

/-- A visit to scale n is recorded at some scale at least n whenever
only finitely many sections contain the current point. -/
lemma lastActiveObservation_scale_ge {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) {x : Y}
    (hfin : {n | x ∈ S n}.Finite) {n : ℕ} (hn : x ∈ S n) :
    ∃ m, n ≤ m ∧ lastActiveObservation S B x=some ⟨m,B m x⟩ := by
  obtain ⟨m,hnm,hm⟩ := exists_lastActiveSection_of_finite hfin hn
  refine ⟨m,hnm,?_⟩
  exact Set.ext_iff.mp (lastActiveObservation_fiber S B (some ⟨m,B m x⟩)) x |>.mpr ⟨hm,rfl⟩

end DukePrimeDegree

end

end OAI
