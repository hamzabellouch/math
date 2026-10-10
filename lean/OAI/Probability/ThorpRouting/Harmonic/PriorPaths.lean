import Mathlib
import OAI.Probability.ThorpRouting.Harmonic.AssignmentSlots

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter
namespace RoutingNetwork
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)
lemma mem_exposedPaths (b : ι → Bool) (V : Finset (α)) (s : ι) :
    s ∈ exposedPaths R b V ↔ (R.users b s).1 ∈ V ∨ (R.users b s).2 ∈ V := by
  classical
  simp only [exposedPaths,Finset.mem_biUnion,R.mem_path]
  constructor
  · rintro ⟨x,hx,h | h⟩
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  · rintro (h | h)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨_,h,Or.inr rfl⟩

lemma terminalCharge_sum (b : ι → Bool) (z : α) (V : Finset (α))
    (hz : z ∉ V) :
    (terminalCharge R b z V : ℝ) = ∑ s : ι,
      ((if (R.users b s).1 = z ∧ (R.users b s).2 ∈ V then (1:ℝ) else 0) +
      (if (R.users b s).2 = z ∧ (R.users b s).1 ∈ V then (1:ℝ) else 0)) := by
  classical
  have he : R.path b z ∩ exposedPaths R b V =
      Finset.univ.filter (fun s =>
        ((R.users b s).1 = z ∧ (R.users b s).2 ∈ V) ∨
        ((R.users b s).2 = z ∧ (R.users b s).1 ∈ V)) := by
    ext s
    simp only [Finset.mem_inter,R.mem_path,mem_exposedPaths,
      Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h₁ : (R.users b s).1 = z <;>
      by_cases h₂ : (R.users b s).2 = z <;> simp [h₁,h₂,hz]
  rw [terminalCharge,he]
  simp only [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h₁ : (R.users b s).1 = z <;>
    by_cases h₂ : (R.users b s).2 = z <;> simp [h₁,h₂,hz]

noncomputable def priorPaths {A : ℕ} (o : α → Option (Fin A)) (t : ℕ) : Finset (α) :=
  Finset.univ.filter (fun x => ∃ i : Fin A, o x = some i ∧ i.val < t)

omit [DecidableEq α] in
@[simp] lemma mem_priorPaths {A : ℕ} (o : α → Option (Fin A)) (t : ℕ) (x : α) :
    x ∈ priorPaths o t ↔ ∃ i : Fin A, o x = some i ∧ i.val < t := by
  classical
  simp [priorPaths]

lemma terminalCharge_prior_sum {A : ℕ} (o : α → Option (Fin A))
    (b : ι → Bool) (z : Terminal o) (i : Fin A) :
    (terminalCharge R b (z i).val ((priorPaths o (i.val+1)).erase (z i).val) : ℝ) =
      ∑ s : ι,
        ((if (z i).val = (R.users b s).1 ∧ (R.users b s).2 ∈ priorPaths o (i.val+1)
          then (1:ℝ) else 0) +
        (if (z i).val = (R.users b s).2 ∧ (R.users b s).1 ∈ priorPaths o (i.val+1)
          then (1:ℝ) else 0)) := by
  classical
  rw [terminalCharge_sum _ _ _ _ (Finset.notMem_erase _ _)]
  apply Finset.sum_congr rfl
  intro s _
  have hn := R.users_ne b s
  simp only [Finset.mem_erase]
  by_cases h₁ : (z i).val = (R.users b s).1 <;>
    by_cases h₂ : (z i).val = (R.users b s).2 <;> simp_all [eq_comm]

lemma rotationMeeting_eq_slot_sum {A : ℕ} (o : α → Option (Fin A))
    (z : Terminal o) (u v : α) :
    rotationMeeting o z u v = ∑ i : Fin A,
      ((if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) +
      (if (z i).val = v ∧ u ∈ priorPaths o (i.val+1) then (1:ℝ) else 0)) := by
  classical
  have only_owner (u : α) (a : Fin A) (hou : o u = some a)
      (i : Fin A) (hia : i ≠ a) : (z i).val ≠ u := by
    intro h
    have hi := (z i).property
    rw [h,hou] at hi
    exact hia (Option.some.inj hi).symm
  have sum_one (u v : α) (a : Fin A) (hou : o u = some a) :
      (∑ i : Fin A, if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) =
      if (z a).val = u ∧ v ∈ priorPaths o (a.val+1) then 1 else 0 := by
    apply Finset.sum_eq_single a
    · intro i _ hia
      simp [only_owner u a hou i hia]
    · simp
  have sum_none (u v : α) (hou : o u = none) :
      (∑ i : Fin A, if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : (z i).val ≠ u := by
      intro h
      have hi := (z i).property
      rw [h,hou] at hi
      contradiction
    simp [hn]
  rw [Finset.sum_add_distrib]
  cases hou : o u with
  | none =>
    rw [sum_none u v hou]
    simp [rotationMeeting,hou,mem_priorPaths]
  | some a =>
    rw [sum_one u v a hou]
    cases hov : o v with
    | none =>
      rw [sum_none v u hov]
      simp [rotationMeeting,hou,hov,mem_priorPaths]
    | some b =>
      rw [sum_one v u b hov]
      simp only [rotationMeeting,hou,hov,mem_priorPaths,Option.some.injEq]
      rcases lt_trichotomy a b with hab | rfl | hba
      · have hn : ¬ b.val < a.val+1 := by omega
        have hy : a.val < b.val+1 := by omega
        simp [hab,hn,hy]
      · simp
      · have hn : ¬ a.val < b.val+1 := by omega
        have hy : b.val < a.val+1 := by omega
        simp [hba,not_lt_of_ge (le_of_lt hba),hn,hy]

lemma rotationCharge_eq_terminal_sum {A : ℕ} (o : α → Option (Fin A))
    (b : ι → Bool) (z : Terminal o) :
    rotationCharge R o b z = ∑ i : Fin A,
      (terminalCharge R b (z i).val ((priorPaths o (i.val+1)).erase (z i).val) : ℝ) := by
  simp only [rotationCharge,rotationMeeting_eq_slot_sum,terminalCharge_prior_sum]
  exact Finset.sum_comm

omit [DecidableEq α] in
@[simp] lemma priorPaths_zero {A : ℕ} (o : α → Option (Fin A)) : priorPaths o 0 = ∅ := by
  classical
  ext x
  simp

lemma priorPaths_succ {A : ℕ} (o : α → Option (Fin A)) (t : ℕ) (ht : t < A) :
    priorPaths o (t+1) = priorPaths o t ∪ cycleFiber o ⟨t,ht⟩ := by
  classical
  ext x
  simp only [mem_priorPaths,Finset.mem_union,mem_cycleFiber]
  constructor
  · rintro ⟨i,hi,hit⟩
    by_cases h : i.val < t
    · exact Or.inl ⟨i,hi,h⟩
    · have he : i = ⟨t,ht⟩ := Fin.ext (by change i.val = t; omega)
      exact Or.inr (he ▸ hi)
  · rintro (⟨i,hi,hit⟩ | hi)
    · exact ⟨i,hi,by omega⟩
    · exact ⟨⟨t,ht⟩,hi,by change t < t+1; omega⟩

omit [DecidableEq α] in
lemma priorPaths_disjoint {A : ℕ} (o : α → Option (Fin A)) (i : Fin A) :
    Disjoint (priorPaths o i.val) (cycleFiber o i) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨j,hj,hji⟩ := (mem_priorPaths _ _ _).mp hx
  have he : j = i := Option.some.inj (hj.symm.trans ((mem_cycleFiber _ _ _).mp hx'))
  subst j
  exact (lt_irrefl _ hji)

namespace QueryTree
open Thorp.QueryTree

lemma seekCycles_owned {A : ℕ} (S : Finset (α)) (r : Fin A → ℕ)
    (o : α → Option (Fin A)) (z : Terminal o) (ω : ι → Bool)
    (hS : ∀ i, cycleFiber o i ⊆ S)
    (hO : ∀ i, orbitSet (R.perm ω) (z i).val = cycleFiber o i)
    (hC : ∀ i, (cycleFiber o i).card = r i+1) :
    let p := R.perm ω
    let L := List.ofFn (fun i : Fin A => (p (z i).val,r i))
    (seekCycles R S L ∅).succeeds ω = true ∧
      ((seekCycles R S L ∅).staleCharge ∅ ω : ℝ) = rotationCharge R o (ω) z := by
  classical
  let b := ω
  let p := R.perm b
  let f (i : Fin A) := (p (z i).val,r i)
  let c (i : Fin A) : ℝ := terminalCharge R b (z i).val ((priorPaths o (i.val+1)).erase (z i).val)
  have hc (i : Fin A) : Function.minimalPeriod p (z i).val - 1 = r i := by
    have he := orbitSet_card p (z i).val
    rw [hO,hC] at he
    omega
  have hs (t : ℕ) (ht : t ≤ A) :
      (seekCycles R S ((List.ofFn f).drop t) (priorPaths o t)).succeeds ω = true ∧
        ((seekCycles R S ((List.ofFn f).drop t) (priorPaths o t)).staleCharge (exposedPaths R b (priorPaths o t)) ω : ℝ) =
          ((List.ofFn c).drop t).sum := by
    induction ht using Nat.decreasingInduction with
    | self => simp only [List.length_ofFn,le_refl,List.drop_eq_nil_of_le,List.sum_nil,seekCycles,Thorp.QueryTree.succeeds,staleCharge,Nat.cast_zero,and_self]
    | of_succ t ht ih =>
      have htf : t < (List.ofFn f).length := by simpa using ht
      have htc : t < (List.ofFn c).length := by simpa using ht
      rw [List.drop_eq_getElem_cons htf,List.drop_eq_getElem_cons htc]
      simp only [List.getElem_ofFn,List.sum_cons,seekCycles]
      have h := seekCycle_orbit R S (priorPaths o t) (z ⟨t,ht⟩).val
        (fun V => seekCycles R S ((List.ofFn f).drop (t+1)) V) ω
        (by rw [hO]; exact hS _) (by rw [hO]; exact priorPaths_disjoint o ⟨t,ht⟩)
      dsimp only at h
      rw [hc,hO,←priorPaths_succ o t ht] at h
      dsimp only [f]
      constructor
      · exact h.1.trans ih.1
      · rw [h.2,Nat.cast_add,ih.2]
        exact add_comm _ _
  have h := hs 0 (Nat.zero_le _)
  simp only [List.drop_zero,priorPaths_zero,exposedPaths_empty,List.sum_ofFn] at h
  dsimp only
  exact ⟨h.1,h.2.trans (rotationCharge_eq_terminal_sum R o b z).symm⟩

end QueryTree
section Collections
variable {A : ℕ}

def ValidCycleSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ)
    (o : α → Option (Fin A)) : Prop :=
  (∀ i, (cycleFiber o i).card = r i + 1) ∧
  (∀ i, cycleFiber o i ⊆ S) ∧
  (∀ i x, o x = some i → orbitSet p x = cycleFiber o i)

abbrev CycleSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  {o : α → Option (Fin A) // ValidCycleSlots p S r o}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    Fintype (CycleSlots p S r) := Fintype.ofFinite _

lemma CycleSlots.terminal_nonempty {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (c : CycleSlots p S r) (i : Fin A) : Nonempty {x : α // c.val x = some i} := by
  have hn : (cycleFiber c.val i).Nonempty := Finset.card_pos.mp (by rw [c.property.1]; omega)
  obtain ⟨x,hx⟩ := hn
  exact ⟨x,(mem_cycleFiber _ _ _).mp hx⟩

omit [DecidableEq α] in
lemma owner_ext {o o' : α → Option (Fin A)}
    (h : ∀ i, cycleFiber o i = cycleFiber o' i) : o = o' := by
  funext x
  have he (i : Fin A) : o x = some i ↔ o' x = some i := by
    simpa only [mem_cycleFiber] using (Finset.ext_iff.mp (h i) x)
  cases ho : o x with
  | some i => exact ((he i).mp ho).symm
  | none =>
    cases ho' : o' x with
    | none => rfl
    | some i => have hn := (he i).mpr ho'; rw [ho] at hn; contradiction

abbrev RootedSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  Σ c : CycleSlots p S r, Terminal c.val

noncomputable def rootedStart {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (c : RootedSlots p S r) : Fin A → S := fun i =>
  ⟨p (c.2 i).val,c.1.property.2.1 i (by
    rw [←c.1.property.2.2 i (c.2 i).val (c.2 i).property]
    exact (mem_orbitSet _ _ _).mpr (Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.refl p _)))⟩

lemma rootedStart_injective {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ} :
    Function.Injective (rootedStart (p:=p) (S:=S) (r:=r)) := by
  rintro ⟨c,z⟩ ⟨c',z'⟩ h
  have hz (i : Fin A) : (z i).val = (z' i).val :=
    p.injective (congrArg Subtype.val (congrFun h i))
  have hc : c = c' := Subtype.ext (owner_ext (fun i => by
    rw [←c.property.2.2 i (z i).val (z i).property,
      ←c'.property.2.2 i (z' i).val (z' i).property,hz]))
  subst c'
  have hzz : z = z' := funext (fun i => Subtype.ext (hz i))
  subst z'
  rfl

lemma rooted_weight_sum_le (S : Finset (α)) (r : Fin A → ℕ) (ω : ι → Bool) :
    (∑ c : RootedSlots (R.perm ω) S r,
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2)) ≤
    ∑ a : Fin A → S,
      if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
        ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
      else 0 := by
  classical
  let p := R.perm ω
  let g (a : Fin A → S) : ℝ :=
    if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
      ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
    else 0
  have he (c : RootedSlots p S r) :
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2) =
      g (rootedStart c) := by
    have hs := QueryTree.seekCycles_owned R S r c.1.val c.2 ω c.1.property.2.1
      (fun i => c.1.property.2.2 i (c.2 i).val (c.2 i).property) c.1.property.1
    dsimp only at hs
    unfold g
    rw [ite_eq_left (show (QueryTree.seekCycles R S (List.ofFn (fun i => ((rootedStart c i).val,r i))) ∅).succeeds ω = true from hs.1)]
    rw [← hs.2,neg_mul,Real.exp_neg,mul_comm (Real.log 2),Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rfl
  simp_rw [he]
  exact sum_comp_injective_le rootedStart rootedStart_injective g (fun a => by dsimp [g]; split_ifs <;> positivity)

lemma collection_rotation_lower (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r)
    (ω : ι → Bool) (c : CycleSlots (R.perm ω) S r) :
    collectionWeight d r ≤ ∑ z : Terminal c.val,
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.val (ω) z) := by
  classical
  let (i : Fin A) : Nonempty {x : α // c.val x = some i} := c.terminal_nonempty i
  have hm : Monotone (fun i => (cycleFiber c.val i).card) := by
    intro i j hij
    dsimp only
    rw [c.property.1,c.property.1]
    exact Nat.add_le_add_right (hr hij) 1
  have hb := rotation_exp_bound R hm (ω)
  have hcard : (Fintype.card (Terminal c.val) : ℝ) = ∏ i : Fin A, (r i+1 : ℝ) := by
    rw [Fintype.card_pi,Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [card_cycleFiber,c.property.1,Nat.cast_add,Nat.cast_one]
  have hp : (0:ℝ) < Fintype.card (Terminal c.val) := Nat.cast_pos.mpr Fintype.card_pos
  have hl : rotationLower d r ≤ finiteMean (fun z : Terminal c.val => Real.exp (-Real.log 2 * rotationCharge R c.val (ω) z)) := by
    simpa only [rotationLower,c.property.1,Nat.cast_add,Nat.cast_one] using hb
  have hh := (le_div_iff₀ hp).mp hl
  rw [hcard] at hh
  unfold collectionWeight
  rw [← Finset.mul_sum]
  calc
    _ = ((2:ℝ)^d)^A * (rotationLower d r * ∏ i : Fin A, (r i+1 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

lemma cycleSlots_weighted_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) *
      collectionWeight d r ≤ (S.card : ℝ)^A := by
  classical
  let g (a : Fin A → S) (ω : ι → Bool) : ℝ :=
    if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
      ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
    else 0
  have hω (ω : ι → Bool) :
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ) * collectionWeight d r ≤
        ∑ a : Fin A → S, g a ω := by
    calc
      _ = ∑ _c : CycleSlots (R.perm ω) S r, collectionWeight d r := by simp
      _ ≤ ∑ c : CycleSlots (R.perm ω) S r,
          ∑ z : Terminal c.val, ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.val (ω) z) :=
        Finset.sum_le_sum (fun c _ => collection_rotation_lower R S r hr ω c)
      _ = ∑ c : RootedSlots (R.perm ω) S r,
          ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2) :=
        (Fintype.sum_sigma (fun c : RootedSlots (R.perm ω) S r =>
          ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2))).symm
      _ ≤ _ := rooted_weight_sum_le R S r ω
  have hb := finiteMean_mono hω
  rw [finiteMean_mul_const,finiteMean_sum] at hb
  calc
    _ ≤ ∑ a : Fin A → S, finiteMean (g a) := hb
    _ ≤ ∑ _a : Fin A → S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have hh := QueryTree.cycles_weighted_success R S (List.ofFn (fun i : Fin A => ((a i).val,r i)))
      simpa only [List.length_ofFn] using hh
    _ = _ := by simp

lemma cycleSlots_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) ≤
        (S.card : ℝ)^A / collectionWeight d r := by
  exact (le_div_iff₀ (collectionWeight_pos d r)).mpr (cycleSlots_weighted_moment R S r hr)

lemma butterfly_cycleSlots_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) ≤
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt (r i+1)) := by
  have h := cycleSlots_moment R S r hr
  rw [collectionWeight_eq_sqrt,div_mul_eq_div_mul_one_div] at h
  rw [div_pow]
  simpa only [one_div,Finset.prod_inv_distrib] using h

end Collections

section CycleCounting
variable {A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (α)) (S : Finset (α)) :=
  {C : Finset (α) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

lemma SelectedCycle.nonempty {p : Equiv.Perm (α)} {S : Finset (α)}
    (C : SelectedCycle p S) : C.val.Nonempty := by
  obtain ⟨x,hx⟩ := C.property.1
  rw [hx]
  exact orbitSet_nonempty p x

lemma SelectedCycle.orbit_eq {p : Equiv.Perm (α)} {S : Finset (α)}
    (C : SelectedCycle p S) {x : α} (hx : x ∈ C.val) : orbitSet p x = C.val := by
  obtain ⟨y,hy⟩ := C.property.1
  rw [hy] at hx ⊢
  exact (orbitSet_eq p ((mem_orbitSet _ _ _).mp hx)).symm

lemma SelectedCycle.eq_of_mem {p : Equiv.Perm (α)} {S : Finset (α)}
    (C D : SelectedCycle p S) {x : α} (hC : x ∈ C.val) (hD : x ∈ D.val) : C = D := by
  apply Subtype.ext
  exact (C.orbit_eq hC).symm.trans (D.orbit_eq hD)

abbrev SlotAssignment (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  {f : Fin A → SelectedCycle p S // Function.Injective f ∧ ∀ i, (f i).val.card = r i+1}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    Fintype (SlotAssignment p S r) := Fintype.ofFinite _

noncomputable def slotsToAssignment {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (c : CycleSlots p S r) : SlotAssignment p S r := by
  classical
  let f (i : Fin A) : SelectedCycle p S := ⟨cycleFiber c.val i,by
    obtain ⟨x,hx⟩ := c.terminal_nonempty i
    exact ⟨⟨x,(c.property.2.2 i x hx).symm⟩,c.property.2.1 i⟩⟩
  refine ⟨f,?_,fun i => c.property.1 i⟩
  intro i j hij
  have he : cycleFiber c.val i = cycleFiber c.val j := congrArg Subtype.val hij
  obtain ⟨x,hx⟩ := c.terminal_nonempty i
  have hxi : x ∈ cycleFiber c.val i := (mem_cycleFiber _ _ _).mpr hx
  rw [he] at hxi
  exact Option.some.inj (hx.symm.trans ((mem_cycleFiber _ _ _).mp hxi))

noncomputable def assignmentOwner {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (x : α) : Option (Fin A) := by
  classical
  exact if h : ∃ i, x ∈ (f.val i).val then some (Classical.choose h) else none

lemma assignmentOwner_eq_some {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (x : α) (i : Fin A) :
    assignmentOwner f x = some i ↔ x ∈ (f.val i).val := by
  classical
  unfold assignmentOwner
  split_ifs with h
  · constructor
    · intro hi
      have hx := Classical.choose_spec h
      rw [Option.some.inj hi] at hx
      exact hx
    · intro hx
      have he := (f.val (Classical.choose h)).eq_of_mem (f.val i) (Classical.choose_spec h) hx
      exact congrArg some (f.property.1 he)
  · constructor
    · intro hi; contradiction
    · intro hx; exact (h ⟨i,hx⟩).elim

lemma assignmentOwner_fiber {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (i : Fin A) : cycleFiber (assignmentOwner f) i = (f.val i).val := by
  ext x
  simp only [mem_cycleFiber,assignmentOwner_eq_some]

noncomputable def assignmentToSlots {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) : CycleSlots p S r :=
  ⟨assignmentOwner f,by
    refine ⟨?_,?_,?_⟩
    · intro i
      rw [assignmentOwner_fiber]
      exact f.property.2 i
    · intro i
      rw [assignmentOwner_fiber]
      exact (f.val i).property.2
    · intro i x hx
      rw [assignmentOwner_fiber]
      exact (f.val i).orbit_eq ((assignmentOwner_eq_some f x i).mp hx)⟩

noncomputable def cycleSlotsEquivAssignments (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    CycleSlots p S r ≃ SlotAssignment p S r where
  toFun := slotsToAssignment
  invFun := assignmentToSlots
  left_inv c := by
    apply Subtype.ext
    apply owner_ext
    intro i
    rw [assignmentToSlots,assignmentOwner_fiber]
    rfl
  right_inv f := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact assignmentOwner_fiber f i

end CycleCounting

section GroupedCounting
variable {A : ℕ}

abbrev LengthClass (r : Fin A → ℕ) := {j : ℕ // j ∈ Finset.univ.image (fun i => r i + 1)}

def slotClass (r : Fin A → ℕ) (i : Fin A) : LengthClass r :=
  ⟨r i+1, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

abbrev SlotsOfLength (r : Fin A → ℕ) (j : LengthClass r) := {i : Fin A // slotClass r i = j}
abbrev CyclesOfLength (p : Equiv.Perm (α)) (S : Finset (α)) (j : ℕ) :=
  {C : SelectedCycle p S // C.val.card = j}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) (j : ℕ) :
    Fintype (CyclesOfLength p S j) := Fintype.ofFinite _

abbrev GroupedAssignments (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  ∀ j : LengthClass r, SlotsOfLength r j ↪ CyclesOfLength p S j.val

noncomputable def assignmentToGroups {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) : GroupedAssignments p S r := fun _j =>
  { toFun := fun i => ⟨f.val i.val, (f.property.2 i.val).trans (congrArg Subtype.val i.property)⟩
    inj' := fun _i _k h => Subtype.ext (f.property.1 (congrArg Subtype.val h)) }

noncomputable def groupsEmbedding {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (F : GroupedAssignments p S r) : Fin A ↪ SelectedCycle p S :=
  ((Equiv.sigmaFiberEquiv (slotClass r)).symm.toEmbedding.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl _) F)).trans
    ((Function.Embedding.sigmaMap (Function.Embedding.subtype _) (fun _ => Function.Embedding.refl _)).trans
      (Equiv.sigmaFiberEquiv (fun C : SelectedCycle p S => C.val.card)).toEmbedding)

noncomputable def groupsToAssignment {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (F : GroupedAssignments p S r) : SlotAssignment p S r :=
  ⟨groupsEmbedding F, (groupsEmbedding F).injective,
    fun i => (F (slotClass r i) ⟨i,rfl⟩).property⟩

noncomputable def assignmentEquivGroups (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    SlotAssignment p S r ≃ GroupedAssignments p S r where
  toFun := assignmentToGroups
  invFun := groupsToAssignment
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv F := by
    funext j
    apply Function.Embedding.ext
    intro i
    rcases i with ⟨i,hi⟩
    subst j
    rfl

lemma card_cycleSlots_factorial (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    Fintype.card (CycleSlots p S r) =
      ∏ j : LengthClass r, (Fintype.card (CyclesOfLength p S j.val)).descFactorial
        (Fintype.card (SlotsOfLength r j)) := by
  classical
  rw [Fintype.card_congr (cycleSlotsEquivAssignments p S r),
    Fintype.card_congr (assignmentEquivGroups p S r), Fintype.card_pi]
  simp only [Fintype.card_embedding_eq]

lemma butterfly_factorial_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
       (∏ j : LengthClass r,
         (Fintype.card (CyclesOfLength (R.perm ω) S j.val)).descFactorial
           (Fintype.card (SlotsOfLength r j)) : ℕ)) ≤
      ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
        ∏ i : Fin A, (1 / Real.sqrt (r i+1)) := by
  simpa only [←card_cycleSlots_factorial] using butterfly_cycleSlots_moment R S r hr

end GroupedCounting

section AllLengths
variable {A : ℕ}

noncomputable def assignmentRelabel (p : Equiv.Perm (α)) (S : Finset (α))
    (r : Fin A → ℕ) (e : Equiv.Perm (Fin A)) :
    SlotAssignment p S r ≃ SlotAssignment p S (r ∘ e) where
  toFun f := ⟨f.val ∘ e, f.property.1.comp e.injective, fun i => f.property.2 (e i)⟩
  invFun f := ⟨f.val ∘ e.symm, f.property.1.comp e.symm.injective, fun i => by
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using f.property.2 (e.symm i)⟩
  left_inv f := by apply Subtype.ext; funext i; simp
  right_inv f := by apply Subtype.ext; funext i; simp

lemma card_cycleSlots_relabel (p : Equiv.Perm (α)) (S : Finset (α))
    (r : Fin A → ℕ) (e : Equiv.Perm (Fin A)) :
    Fintype.card (CycleSlots p S r) = Fintype.card (CycleSlots p S (r ∘ e)) := by
  exact Fintype.card_congr ((cycleSlotsEquivAssignments p S r).trans
    ((assignmentRelabel p S r e).trans (cycleSlotsEquivAssignments p S (r ∘ e)).symm))

lemma butterfly_cycleSlots_moment_all (S : Finset (α)) (r : Fin A → ℕ) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) ≤
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt (r i+1)) := by
  have h := butterfly_cycleSlots_moment R S (r ∘ Tuple.sort r) (Tuple.monotone_sort r)
  simp_rw [←card_cycleSlots_relabel] at h
  have hp := Equiv.prod_comp (Tuple.sort r) (fun i : Fin A => (1 / Real.sqrt (r i+1) : ℝ))
  simpa only [Function.comp_apply,hp] using h

abbrev ShortCycle (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :=
  {C : SelectedCycle p S // C.val.card ≤ J}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype (ShortCycle p S J) := Fintype.ofFinite _

noncomputable def shortCycleLength {p : Equiv.Perm (α)} {S : Finset (α)} {J : ℕ}
    (C : ShortCycle p S J) : Fin J :=
  ⟨C.val.val.card-1, by have := C.val.nonempty.card_pos; have := C.property; omega⟩

lemma shortCycleLength_add_one {p : Equiv.Perm (α)} {S : Finset (α)} {J : ℕ}
    (C : ShortCycle p S J) : (shortCycleLength C : ℕ)+1 = C.val.val.card := by
  have := C.val.nonempty.card_pos
  simp only [shortCycleLength]
  omega

noncomputable def shortEmbeddingEquiv (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    (Fin A ↪ ShortCycle p S J) ≃
      Σ r : Fin A → Fin J, SlotAssignment p S (fun i => (r i : ℕ)) where
  toFun f := ⟨fun i => shortCycleLength (f i),
    ⟨fun i => (f i).val, fun i j h => f.injective (Subtype.ext h),
      fun i => (shortCycleLength_add_one (f i)).symm⟩⟩
  invFun c :=
    { toFun := fun i => ⟨c.2.val i, by rw [c.2.property.2]; exact (c.1 i).isLt⟩
      inj' := fun _i _j h => c.2.property.1 (congrArg Subtype.val h) }
  left_inv f := by
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv c := by
    rcases c with ⟨r,f⟩
    have he : (fun i => shortCycleLength (⟨f.val i, by rw [f.property.2]; exact (r i).isLt⟩ : ShortCycle p S J)) = r := by
      funext i
      apply Fin.ext
      simp only [shortCycleLength,f.property.2,Nat.add_sub_cancel]
    apply Sigma.ext he
    apply (Subtype.heq_iff_coe_eq (by
      intro x
      change (Function.Injective x ∧ ∀ i, (x i).val.card = (f.val i).val.card - 1 + 1) ↔ _
      simp only [f.property.2,Nat.add_sub_cancel])).mpr
    rfl

lemma shortCycle_factorial_eq (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    (Fintype.card (ShortCycle p S J)).descFactorial A =
      ∑ r : Fin A → Fin J, Fintype.card (CycleSlots p S (fun i => (r i : ℕ))) := by
  classical
  have hc := Fintype.card_embedding_eq (α := Fin A) (β := ShortCycle p S J)
  simp only [Fintype.card_fin] at hc
  rw [←hc, Fintype.card_congr (shortEmbeddingEquiv p S J),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact (Fintype.card_congr (cycleSlotsEquivAssignments p S (fun i => (r i : ℕ)))).symm

end AllLengths

section CycleMGF

lemma butterfly_shortCycle_moment (S : Finset (α)) (J A : ℕ) :
    finiteMean (fun ω : ι → Bool =>
      ((Fintype.card (ShortCycle (R.perm ω) S J)).descFactorial A : ℝ)) ≤
      ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d) * ∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1))^A := by
  classical
  simp_rw [shortCycle_factorial_eq,Nat.cast_sum,finiteMean_sum]
  calc
    _ ≤ ∑ r : Fin A → Fin J,
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt ((r i : ℕ)+1)) := by
      apply Finset.sum_le_sum
      intro r _
      exact butterfly_cycleSlots_moment_all R S (fun i => (r i : ℕ))
    _ = _ := by
      rw [←Finset.mul_sum,mul_pow]
      congr 1
      rw [←Fintype.prod_sum (fun (_ : Fin A) (j : Fin J) => (1 / Real.sqrt ((j:ℕ)+1) : ℝ))]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

noncomputable def cycleMass (p : Equiv.Perm (α)) (S : Finset (α)) : ℕ :=
  ∑ C : SelectedCycle p S, C.val.card

lemma cycleMass_le (p : Equiv.Perm (α)) (S : Finset (α)) : cycleMass p S ≤ S.card := by
  classical
  let f : (Σ C : SelectedCycle p S, {x : α // x ∈ C.val}) → S :=
    fun c => ⟨c.2.val,c.1.property.2 c.2.property⟩
  have hi : Function.Injective f := by
    intro c e h
    have hx : c.2.val = e.2.val := congrArg Subtype.val h
    have hC : c.1 = e.1 := c.1.eq_of_mem e.1 c.2.property (hx ▸ e.2.property)
    rcases c with ⟨c,x⟩
    rcases e with ⟨e,y⟩
    dsimp only at hC
    subst e
    have he : x=y := Subtype.ext hx
    cases he
    rfl
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_sigma,Fintype.card_coe,cycleMass] using hh

lemma shortCycle_card_le (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype.card (ShortCycle p S J) ≤ S.card := by
  classical
  calc
    _ ≤ Fintype.card (SelectedCycle p S) := Fintype.card_subtype_le _
    _ = ∑ _ : SelectedCycle p S, 1 := by simp
    _ ≤ cycleMass p S := Finset.sum_le_sum (fun C _ => C.nonempty.card_pos)
    _ ≤ _ := cycleMass_le p S

lemma butterfly_shortCycle_mgf (S : Finset (α)) (J : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (ShortCycle (R.perm ω) S J))) ≤
      Real.exp ((q-1)*((S.card : ℝ) / Real.sqrt ((2:ℝ)^d) * ∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1))) := by
  apply factorial_mgf _ S.card _ q (fun ω => shortCycle_card_le _ _ _)
  · positivity
  · exact hq
  · exact butterfly_shortCycle_moment R S J

end CycleMGF


abbrev LongCycle (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :=
  {C : SelectedCycle p S // ¬ C.val.card ≤ J}
noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype (LongCycle p S J) := Fintype.ofFinite _

lemma selectedCycle_card_split (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype.card (SelectedCycle p S) =
      Fintype.card (ShortCycle p S J) + Fintype.card (LongCycle p S J) := by
  classical
  rw [←Fintype.card_congr (Equiv.sumCompl (fun C : SelectedCycle p S => C.val.card ≤ J)),Fintype.card_sum]

lemma longCycle_card_bound (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    J * Fintype.card (LongCycle p S J) ≤ S.card := by
  classical
  have hs := Equiv.sum_comp (Equiv.sumCompl (fun C : SelectedCycle p S => C.val.card ≤ J))
    (fun C : SelectedCycle p S => C.val.card)
  rw [Fintype.sum_sum_type] at hs
  have h0 : J * Fintype.card (LongCycle p S J) ≤
      ∑ C : LongCycle p S J, C.val.val.card := by
    calc
      _ = ∑ _C : LongCycle p S J, J := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun C _ => Nat.le_of_lt (Nat.lt_of_not_ge C.property))
  have hh := cycleMass_le p S
  unfold cycleMass at hh
  rw [←hs] at hh
  exact h0.trans ((Nat.le_add_left _ _).trans hh)

lemma longCycle_pow_bound (p : Equiv.Perm (α)) (S : Finset (α))
    (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    q^(Fintype.card (LongCycle p S J)) ≤ Real.exp ((S.card : ℝ)/J * Real.log q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hc : (Fintype.card (LongCycle p S J) : ℝ) ≤ (S.card : ℝ)/J := by
    apply (le_div_iff₀ (by exact_mod_cast hJ)).mpr
    have hh := longCycle_card_bound p S J
    exact_mod_cast (by simpa only [mul_comm] using hh)
  calc
    _ = Real.exp ((Fintype.card (LongCycle p S J) : ℝ)*Real.log q) := by
      rw [Real.exp_nat_mul,Real.exp_log hq0]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (Real.log_nonneg hq))

lemma butterfly_cycle_log_mgf (S : Finset (α)) (J : ℕ) (hJ : 0 < J)
    (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (SelectedCycle (R.perm ω) S)))) ≤
      (S.card : ℝ)/J * Real.log q + 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^d) := by
  let lam : ℝ := (S.card : ℝ)/Real.sqrt ((2:ℝ)^d) * ∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1)
  let c : ℝ := (S.card : ℝ)/J * Real.log q
  have hnum : (q-1)*lam ≤ 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^d) := by
    have hsum := sum_inv_sqrt J
    have hp : 0 ≤ (S.card : ℝ)/Real.sqrt ((2:ℝ)^d) := by positivity
    have h0 : 0 ≤ 2*Real.sqrt J := by positivity
    have hh := mul_le_mul_of_nonneg_left hsum hp
    have hq1 : 0 ≤ q-1 := sub_nonneg.mpr hq
    calc
      _ ≤ (q-1)*((S.card : ℝ)/Real.sqrt ((2:ℝ)^d)*(2*Real.sqrt J)) :=
        mul_le_mul_of_nonneg_left hh hq1
      _ ≤ q*((S.card : ℝ)/Real.sqrt ((2:ℝ)^d)*(2*Real.sqrt J)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp h0)
      _ = _ := by ring
  have hm : finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (SelectedCycle (R.perm ω) S))) ≤
      Real.exp (c+(q-1)*lam) := by
    calc
      _ ≤ finiteMean (fun ω : ι → Bool =>
          q^(Fintype.card (ShortCycle (R.perm ω) S J))*Real.exp c) := by
        apply finiteMean_mono
        intro ω
        rw [selectedCycle_card_split _ _ J,pow_add]
        exact mul_le_mul_of_nonneg_left (longCycle_pow_bound _ S J hJ q hq) (by positivity)
      _ = finiteMean (fun ω : ι → Bool =>
          q^(Fintype.card (ShortCycle (R.perm ω) S J))) * Real.exp c :=
        finiteMean_mul_const _ _
      _ ≤ Real.exp ((q-1)*lam) * Real.exp c :=
        mul_le_mul_of_nonneg_right (butterfly_shortCycle_mgf R S J q hq) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add,add_comm]
  have hpos : 0 < finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (SelectedCycle (R.perm ω) S))) := by
    apply finiteMean_pos
    intro ω
    positivity
  have hlog := Real.log_le_log hpos hm
  rw [Real.log_exp] at hlog
  dsimp [c] at hlog
  linarith


end RoutingNetwork

variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

def parallelPerm (ω : B × SwitchIndex d → Bool) : Equiv.Perm (B × Card d) where
  toFun x := (x.1,butterflyPerm d (decodeButterfly d (fun i => ω (x.1,i))) x.2)
  invFun y := (y.1,(butterflyPerm d (decodeButterfly d (fun i => ω (y.1,i)))).symm y.2)
  left_inv x := by simp
  right_inv y := by simp

def relabeledPerm (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) : Equiv.Perm α :=
  (pre.trans (parallelPerm ω)).trans post

noncomputable def parallelPath (pre : α ≃ B × Card d)
    (ω : B × SwitchIndex d → Bool) (x : α) : Finset (B × SwitchIndex d) :=
  (routeDomain d (pre x).2
    (butterflyPerm d (decodeButterfly d (fun i => ω ((pre x).1,i))) (pre x).2)).image
      (fun i => ((pre x).1,i))

def parallelUsers (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (i : B × SwitchIndex d) : α × α :=
  let u := switchUsers d (decodeButterfly d (fun j => ω (i.1,j))) i.2
  (pre.symm (i.1,u.1),pre.symm (i.1,u.2))

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelUsers_ne (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (i : B × SwitchIndex d) : (parallelUsers pre ω i).1 ≠ (parallelUsers pre ω i).2 := by
  intro h
  exact switchUsers_ne d _ _ (congrArg Prod.snd (pre.symm.injective h))

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma mem_parallelPath (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (x : α) (i : B × SwitchIndex d) :
    i ∈ parallelPath pre ω x ↔ (parallelUsers pre ω i).1 = x ∨ (parallelUsers pre ω i).2 = x := by
  classical
  obtain ⟨b,j⟩ := i
  simp only [parallelPath,Finset.mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨k,hk,hb,rfl⟩
    subst b
    rcases (mem_routeDomain_iff_user d _ _ _).mp hk with h | h
    · left
      apply pre.injective
      change pre (pre.symm ((pre x).1,_)) = pre x
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl h
    · right
      apply pre.injective
      change pre (pre.symm ((pre x).1,_)) = pre x
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl h
  · intro h
    have hh : (b,(switchUsers d (decodeButterfly d (fun j => ω (b,j))) j).1) = pre x ∨
        (b,(switchUsers d (decodeButterfly d (fun j => ω (b,j))) j).2) = pre x := by
      rcases h with h | h
      · exact Or.inl (by simpa only [parallelUsers,Equiv.apply_symm_apply] using congrArg pre h)
      · exact Or.inr (by simpa only [parallelUsers,Equiv.apply_symm_apply] using congrArg pre h)
    have hb : b = (pre x).1 := hh.elim (congrArg Prod.fst) (congrArg Prod.fst)
    subst b
    refine ⟨j,?_,rfl,rfl⟩
    apply (mem_routeDomain_iff_user d _ _ _).mpr
    exact hh.elim (fun h => Or.inl (congrArg Prod.snd h)) (fun h => Or.inr (congrArg Prod.snd h))

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma card_parallelPath (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool) (x : α) :
    (parallelPath pre ω x).card = d := by
  classical
  rw [parallelPath,Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),card_routeDomain]

noncomputable def blockMarks (pre : α ≃ B × Card d) (S : Finset α) (b : B) : Finset (Card d) :=
  Finset.univ.filter (fun x => pre.symm (b,x) ∈ S)

omit [Fintype α] [Fintype B] [DecidableEq B] in
@[simp] lemma mem_blockMarks (pre : α ≃ B × Card d) (S : Finset α) (b : B) (x : Card d) :
    x ∈ blockMarks pre S b ↔ pre.symm (b,x) ∈ S := by
  classical
  simp [blockMarks]

omit [DecidableEq B] in
lemma sum_card_blockMarks (pre : α ≃ B × Card d) (S : Finset α) :
    ∑ b : B, (blockMarks pre S b).card = S.card := by
  classical
  calc
    _ = ∑ b : B, ∑ x : Card d, if pre.symm (b,x) ∈ S then 1 else 0 := by
      simp only [blockMarks,Finset.card_filter]
    _ = ∑ u : B × Card d, if pre.symm u ∈ S then 1 else 0 := (Fintype.sum_prod_type (fun u : B × Card d => if pre.symm u ∈ S then (1:ℕ) else 0)).symm
    _ = ∑ x : α, if x ∈ S then 1 else 0 := Equiv.sum_comp pre.symm (fun x : α => if x ∈ S then (1:ℕ) else 0)
    _ = _ := by simp

omit [DecidableEq B] in
lemma card_blockMarks_le (pre : α ≃ B × Card d) (S : Finset α) (b : B) :
    (blockMarks pre S b).card ≤ S.card := by
  rw [←sum_card_blockMarks pre S]
  exact Finset.single_le_sum (f := fun b : B => (blockMarks pre S b).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

end Thorp

end ThorpNine.Harmonic

end OAI
