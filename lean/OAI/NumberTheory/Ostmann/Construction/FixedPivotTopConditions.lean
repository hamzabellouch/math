import OAI.NumberTheory.Ostmann.Construction.FixedPivotPrimeChecks
import OAI.NumberTheory.Ostmann.Construction.InsertedConstituentWords
import OAI.NumberTheory.Ostmann.Construction.AtomTopSupport

namespace OAI

/-! # Original-prime tests for a top atom pair containing a fixed pivot -/

namespace Ostmann

open scoped Classical

def TopPrimeCondition.HasVariable {V : Type*} : TopPrimeCondition (Option V) → Prop
  | .distinct none none => False
  | .external none _ => False
  | _ => True

def TopPrimeCondition.fixPivot {V : Type*} (M : ℕ) :
    (c : TopPrimeCondition (Option V)) → c.HasVariable → TopPrimeCondition V
  | .distinct none none, h => False.elim h
  | .distinct (some a) none, _ => .external a M
  | .distinct none (some b), _ => .external b M
  | .distinct (some a) (some b), _ => .distinct a b
  | .external none _, h => False.elim h
  | .external (some a) N, _ => .external a N

theorem TopPrimeCondition.fixPivot_holds {V : Type*} (M : ℕ)
    (c : TopPrimeCondition (Option V)) (hc : c.HasVariable) (x : V → ℕ) :
    (c.fixPivot M hc).Holds x ↔ c.Holds (fixedPivotPrimeValues M x) := by
  cases c with
  | distinct a b =>
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hc
      | some b =>
        exact Nat.coprime_comm
    | some a => cases b <;> rfl
  | external a N =>
    cases a with
    | none => exact False.elim hc
    | some a => rfl

theorem TopPrimeCondition.fixPivot_bounded {V : Type*} (M : ℕ) (R : ℝ) (hM : (M : ℝ) ≤ R)
    (c : TopPrimeCondition (Option V)) (hc : c.HasVariable) (hR : c.Bounded R) :
    (c.fixPivot M hc).Bounded R := by
  have hb : |((M : ℤ) : ℝ)| ≤ R := by
    simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)] using hM
  cases c with
  | distinct a b =>
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hc
      | some b => exact hb
    | some a =>
      cases b with
      | none => exact hb
      | some b => trivial
  | external a N =>
    cases a with
    | none => exact False.elim hc
    | some a => exact hR

theorem atomPairChecks_hasVariable {I V : Type*} [Fintype I]
    (words : I → List (Option V))
    (hunique : ∀ i j, none ∈ words i → none ∈ words j → i = j) :
    ∀ c ∈ atomPairChecks words, c.HasVariable := by
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
  by_cases hij : i = j
  · simp only [hij, ite_true, List.not_mem_nil] at hc
  rw [ite_eq_right hij] at hc
  obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  cases v <;> cases w
  · exact False.elim (hij (hunique i j hv hw))
  all_goals trivial

theorem insertedConstituentWord_none {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (hv : none ∈ insertedConstituentWord role size n v) :
    ∃ p : CurrentPivotConstituent role n, v = scheduledPartitionEquiv role n (.inl p) := by
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases a with p | h | y
  · exact ⟨p, rfl⟩
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_ofFn] at hv
    obtain ⟨k, hk⟩ := hv
    cases hk
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_ofFn] at hv
    obtain ⟨k, hk⟩ := hv
    cases hk

theorem insertedConstituentWord_none_unique {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b)
    (v w : CopyScheduleAtoms role n)
    (hv : none ∈ insertedConstituentWord role size n v)
    (hw : none ∈ insertedConstituentWord role size n w) : v = w := by
  obtain ⟨p, rfl⟩ := insertedConstituentWord_none role size n v hv
  obtain ⟨q, rfl⟩ := insertedConstituentWord_none role size n w hw
  have hpq : p = q := Subtype.ext (hu p.val q.val p.property q.property)
  rw [hpq]

theorem insertedAtomPairChecks_hasVariable {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b) :
    ∀ c ∈ atomPairChecks (insertedConstituentWord role size n), c.HasVariable :=
  atomPairChecks_hasVariable _ (insertedConstituentWord_none_unique role size n hu)

theorem none_mem_option_map_iff {V : Type*} (e : Equiv.Perm V) (w : List (Option V)) :
    none ∈ w.map (Equiv.optionCongr e) ↔ none ∈ w := by
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    cases v with
    | none => exact hv
    | some v => cases he
  · intro h
    exact List.mem_map.mpr ⟨none, h, rfl⟩

theorem insertedPermutedAtomPairChecks_hasVariable {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    ∀ c ∈ atomPairChecks (fun i =>
      (insertedConstituentWord role size n i).map (insertedConstituentPerm role size n e)),
      c.HasVariable := by
  apply atomPairChecks_hasVariable
  intro i j hi hj
  apply insertedConstituentWord_none_unique role size n hu i j
  · exact (none_mem_option_map_iff _ _).mp hi
  · exact (none_mem_option_map_iff _ _).mp hj

noncomputable def fixedPivotCheckAt {V : Type*} (M : ℕ)
    (tests : List (TopPrimeCondition (Option V)))
    (h : ∀ c ∈ tests, c.HasVariable) (i : Fin tests.length) : TopPrimeCondition V :=
  (tests[i.val]).fixPivot M (h _ (List.getElem_mem i.isLt))

theorem fixedPivotCheckAt_all {V : Type*} (M : ℕ)
    (tests : List (TopPrimeCondition (Option V)))
    (h : ∀ c ∈ tests, c.HasVariable) (x : V → ℕ) :
    (∀ i, (fixedPivotCheckAt M tests h i).Holds x) ↔
      ∀ c ∈ tests, c.Holds (fixedPivotPrimeValues M x) := by
  constructor
  · intro hall c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact (TopPrimeCondition.fixPivot_holds M _ _ x).mp (hall ⟨i, hi⟩)
  · intro hall i
    exact (TopPrimeCondition.fixPivot_holds M _ _ x).mpr (hall _ (List.getElem_mem i.isLt))

theorem fixedPivotCheckAt_bounded {V : Type*} (M : ℕ) (R : ℝ) (hM : (M : ℝ) ≤ R)
    (tests : List (TopPrimeCondition (Option V)))
    (h : ∀ c ∈ tests, c.HasVariable) (hR : ∀ c ∈ tests, c.Bounded R)
    (i : Fin tests.length) : (fixedPivotCheckAt M tests h i).Bounded R :=
  TopPrimeCondition.fixPivot_bounded M R hM _ _ (hR _ (List.getElem_mem i.isLt))

end Ostmann

end OAI
