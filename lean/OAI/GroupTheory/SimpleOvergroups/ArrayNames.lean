import Mathlib
import OAI.Computability.FiniteCompiler.Quotients
import OAI.GroupTheory.FiniteType.SequentialLimit

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Array
noncomputable section
open scoped Classical
variable {A X D K : Type*} [AddCommMonoid D]
variable (coeff : A → D) (index : X → K)

abbrev Name (A X : Type*) := List (A × X)

def value (p : Name A X) : K →₀ D :=
  (p.map fun a => Finsupp.single (index a.2) (coeff a.1)).sum

@[simp] theorem value_nil : value coeff index [] = 0 := rfl
@[simp] theorem value_cons (a : A × X) (p : Name A X) :
    value coeff index (a::p) = Finsupp.single (index a.2) (coeff a.1) + value coeff index p := rfl
@[simp] theorem value_append (p q : Name A X) :
    value coeff index (p++q) = value coeff index p + value coeff index q := by
  simp [value]

theorem value_eq_zero_of_not_named (p : Name A X) (k : K)
    (h : ∀ a ∈ p, index a.2 ≠ k) : value coeff index p k = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [value_cons, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm (h a List.mem_cons_self))]
    simpa using ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem value_eq_iff (p q : Name A X) :
    value coeff index p = value coeff index q ↔
      ∀ a ∈ p++q, value coeff index p (index a.2) = value coeff index q (index a.2) := by
  constructor
  · intro h a _; rw [h]
  · intro h
    ext k
    by_cases hn : ∃ a ∈ p++q, index a.2 = k
    · obtain ⟨a,ha,rfl⟩ := hn
      exact h a ha
    · have hh : ∀ a ∈ p++q, index a.2 ≠ k := by simpa using hn
      rw [value_eq_zero_of_not_named coeff index p k (fun a ha => hh a (List.mem_append_left _ ha)),
        value_eq_zero_of_not_named coeff index q k (fun a ha => hh a (List.mem_append_right _ ha))]

theorem value_surjective (hc : Function.Surjective coeff) (hx : Function.Surjective index) :
    Function.Surjective (value coeff index) := by
  intro p
  induction p using Finsupp.induction with
  | zero => exact ⟨[], rfl⟩
  | single_add x d p hn hd ih =>
    obtain ⟨a,rfl⟩ := hc d
    obtain ⟨b,rfl⟩ := hx x
    obtain ⟨q,rfl⟩ := ih
    exact ⟨(a,b)::q, rfl⟩

theorem value_map_index {Y J : Type*} (f : X → Y) (j : Y → J) (g : K → J)
    (h : ∀ x, j (f x) = g (index x)) (p : Name A X) :
    value coeff j (p.map (fun a => (a.1, f a.2))) = Finsupp.mapDomain g (value coeff index p) := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih, h, Finsupp.mapDomain_add]

variable (zeroName : A) (addName : A → A → A)

def entry (p : Name A X) (x : X) : A :=
  (p.map fun a => if index a.2 = index x then a.1 else zeroName).foldl addName zeroName

theorem coefficient_fold
    (hadd : ∀ a b, coeff (addName a b) = coeff a + coeff b) (l : List A) (a : A) :
    coeff (l.foldl addName a) = coeff a + (l.map coeff).sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons,ih,hadd,List.map_cons,List.sum_cons,add_assoc]

theorem entry_correct (hzero : coeff zeroName = 0)
    (hadd : ∀ a b, coeff (addName a b) = coeff a + coeff b) (p : Name A X) (x : X) :
    coeff (entry index zeroName addName p x) = value coeff index p (index x) := by
  rw [entry, coefficient_fold coeff addName hadd, hzero, zero_add]
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons,List.sum_cons,value_cons,Finsupp.add_apply,ih]
    congr 1
    by_cases h : index a.2 = index x
    · simp [h]
    · simp [h,hzero]

variable [Primcodable A] [Primcodable X]
variable (ha : Primrec₂ addName)
variable (hx : ComputablePred (fun p : X × X => index p.1 = index p.2))
variable (hc : ComputablePred (fun p : A × A => coeff p.1 = coeff p.2))

include ha hx in
theorem computable_entry : Computable₂ (entry index zeroName addName) := by
  have hs : Computable₂ (fun (x : X) (a : A × X) =>
      if index a.2 = index x then a.1 else zeroName) := by
    refine (Computable.cond (hx.decide.comp
      ((Computable.snd.comp Computable.snd).pair Computable.fst))
      (Computable.fst.comp Computable.snd) (Computable.const zeroName)).of_eq ?_
    intro p
    simp only [Bool.cond_decide]
  have hl : Computable (fun p : Name A X × X =>
      p.1.map (fun a => if index a.2 = index p.2 then a.1 else zeroName)) :=
    (FiniteAlgebraicEnvelopes.Effect.computable_map_parameter hs).comp Computable.snd Computable.fst
  have hf : Primrec (fun l : List A => l.foldl addName zeroName) :=
    Primrec.list_foldl Primrec.id (Primrec.const zeroName)
      (ha.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hf.to_comp.comp hl

include ha hx hc in
omit [AddCommMonoid D] in
theorem computable_entries_eq : Computable₂
    (fun (p : Name A X × Name A X) (a : A × X) =>
      decide (coeff (entry index zeroName addName p.1 a.2) =
        coeff (entry index zeroName addName p.2 a.2))) := by
  have he : Computable₂ (entry index zeroName addName) :=
    computable_entry index zeroName addName ha hx
  have hl : Computable (fun p : (Name A X × Name A X) × (A × X) =>
      entry index zeroName addName p.1.1 p.2.2) :=
    he.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.snd)
  have hr : Computable (fun p : (Name A X × Name A X) × (A × X) =>
      entry index zeroName addName p.1.2 p.2.2) :=
    he.comp (Computable.snd.comp Computable.fst) (Computable.snd.comp Computable.snd)
  apply (hc.decide.comp (hl.pair hr)).of_eq
  intro p
  congr 1

include ha hx hc in
omit [AddCommMonoid D] in
theorem computable_entry_tests : Computable
    (fun p : Name A X × Name A X => (p.1++p.2).map fun a =>
      decide (coeff (entry index zeroName addName p.1 a.2) =
        coeff (entry index zeroName addName p.2 a.2))) :=
  (FiniteAlgebraicEnvelopes.Effect.computable_map_parameter
    (computable_entries_eq coeff index zeroName addName ha hx hc)).comp
      Computable.id (Primrec.list_append.to_comp.comp Computable.fst Computable.snd)

include ha hx hc in
theorem computable_value_eq (hzero : coeff zeroName = 0)
    (hadd : ∀ a b, coeff (addName a b) = coeff a + coeff b) :
    ComputablePred (fun p : Name A X × Name A X => value coeff index p.1 = value coeff index p.2) := by
  have hf : PrimrecPred (fun l : List Bool => ∀ b ∈ l, b = true) :=
    (show PrimrecPred (fun b : Bool => b = true) from
      Primrec.eq.comp Primrec.id (Primrec.const true)).forall_mem_list
  have ht := (hf.decide.to_comp.comp
    (computable_entry_tests coeff index zeroName addName ha hx hc)).computablePred
  apply ht.of_eq
  intro p
  rw [value_eq_iff]
  simp only [List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, decide_eq_true_eq, entry_correct coeff index zeroName addName hzero hadd]

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
