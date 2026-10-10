import Mathlib
import OAI.Computability.DirectedFeedback.Machines.RuntimeFinish

namespace OAI


namespace DFVSGames.Integration.InstanceEquivalences

open DFVSGames.Foundations.Target
open GapSemantics

def renameConstraint {n m q : Nat} (e : Fin n ≃ Fin m) (c : Constraint n q) :
    Constraint m q where
  source := e c.source
  target := e c.target
  permutation := c.permutation

@[simp] theorem renameConstraint_satisfied {n m q : Nat} (e : Fin n ≃ Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (renameConstraint e c).satisfied labeling = c.satisfied (labeling ∘ e) := rfl

theorem rename_count {n m q : Nat} (e : Fin n ≃ Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (renameConstraint e)) =
      countSatisfied (labeling ∘ e) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ e) = true <;> simp [countSatisfied, ih, hc]

def renameInstance {q m : Nat} (g : Instance q) (e : Fin g.vertices ≃ Fin m) :
    Instance q where
  vertices := m
  constraints := g.constraints.map (renameConstraint e)
  nonempty := by
    intro h
    exact g.nonempty (List.map_eq_nil_iff.mp h)

theorem countSatisfied_perm {n q : Nat} (labeling : Fin n → Fin q)
    {constraints constraints' : List (Constraint n q)}
    (h : constraints.Perm constraints') :
    countSatisfied labeling constraints = countSatisfied labeling constraints' := by
  rw [countSatisfied_eq_sum, countSatisfied_eq_sum]
  exact (h.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum_eq

theorem satisfactionRate_eq_of_rename_perm {q : Nat} (g h : Instance q)
    (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e)))
    (labeling : Fin h.vertices → Fin q) :
    satisfactionRate h labeling = satisfactionRate g (labeling ∘ e) := by
  have hcount := countSatisfied_perm labeling hp
  rw [rename_count] at hcount
  have hlength := hp.length_eq
  simp only [List.length_map] at hlength
  unfold satisfactionRate
  rw [hcount, hlength]

theorem completeAt_iff_of_rename_perm {q : Nat} (error : RationalError)
    (g h : Instance q) (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e))) :
    CompleteAt error h ↔ CompleteAt error g := by
  rw [completeAt_iff, completeAt_iff]
  constructor
  · rintro ⟨labeling, hl⟩
    refine ⟨labeling ∘ e, ?_⟩
    rwa [satisfactionRate_eq_of_rename_perm g h e hp] at hl
  · rintro ⟨labeling, hl⟩
    refine ⟨labeling ∘ e.symm, ?_⟩
    rw [satisfactionRate_eq_of_rename_perm g h e hp]
    simpa [Function.comp_def] using hl

theorem soundAt_iff_of_rename_perm {q : Nat} (error : RationalError)
    (g h : Instance q) (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e))) :
    SoundAt error h ↔ SoundAt error g := by
  rw [soundAt_iff, soundAt_iff]
  constructor
  · intro hs labeling
    have hl := hs (labeling ∘ e.symm)
    rw [satisfactionRate_eq_of_rename_perm g h e hp] at hl
    simpa [Function.comp_def] using hl
  · intro hs labeling
    rw [satisfactionRate_eq_of_rename_perm g h e hp]
    exact hs (labeling ∘ e)

theorem rename_rate {q m : Nat} (g : Instance q) (e : Fin g.vertices ≃ Fin m)
    (labeling : Fin m → Fin q) :
    satisfactionRate (renameInstance g e) labeling = satisfactionRate g (labeling ∘ e) :=
  satisfactionRate_eq_of_rename_perm g (renameInstance g e) e (.refl _) labeling

theorem completeAt_rename_iff {q m : Nat} (error : RationalError)
    (g : Instance q) (e : Fin g.vertices ≃ Fin m) :
    CompleteAt error (renameInstance g e) ↔ CompleteAt error g :=
  completeAt_iff_of_rename_perm error g (renameInstance g e) e (.refl _)

theorem soundAt_rename_iff {q m : Nat} (error : RationalError)
    (g : Instance q) (e : Fin g.vertices ≃ Fin m) :
    SoundAt error (renameInstance g e) ↔ SoundAt error g :=
  soundAt_iff_of_rename_perm error g (renameInstance g e) e (.refl _)

end DFVSGames.Integration.InstanceEquivalences


namespace DFVSGames.MachineUniformCopyOrder

def occurrenceMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  edges.flatMap (fun edge => List.replicate C edge)

def copyMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  (List.replicate C edges).flatten

theorem occurrenceMajor_perm_copyMajor {α : Type*} (C : Nat) (edges : List α) :
    (occurrenceMajor C edges).Perm (copyMajor C edges) := by
  induction C with
  | zero => simp [occurrenceMajor, copyMajor]
  | succ C ih =>
    have split : (edges ++ occurrenceMajor C edges).Perm
        (occurrenceMajor (C + 1) edges) := by
      simpa only [occurrenceMajor, List.map_id, List.replicate_succ, id_eq] using
        List.map_append_flatMap_perm edges id (fun edge => List.replicate C edge)
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons] using
      split.symm.trans (ih.append_left edges)

theorem selected_count_eq {α : Type*} (C : Nat) (edges : List α)
    (keep : α → Bool) :
    ((occurrenceMajor C edges).filter keep).length =
      ((copyMajor C edges).filter keep).length :=
  ((occurrenceMajor_perm_copyMajor C edges).filter keep).length_eq

theorem mem_iff {α : Type*} (C : Nat) (edges : List α) (edge : α) :
    edge ∈ occurrenceMajor C edges ↔ edge ∈ copyMajor C edges :=
  (occurrenceMajor_perm_copyMajor C edges).mem_iff

theorem copyMajor_selected_count {α : Type*} (C : Nat) (edges : List α)
    (keep : α → Bool) :
    ((copyMajor C edges).filter keep).length = C * (edges.filter keep).length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    change (((edges ++ copyMajor C edges).filter keep).length) = _
    rw [List.filter_append, List.length_append, ih]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem occurrenceMajor_selected_count {α : Type*} (C : Nat) (edges : List α)
    (keep : α → Bool) :
    ((occurrenceMajor C edges).filter keep).length = C * (edges.filter keep).length := by
  rw [selected_count_eq, copyMajor_selected_count]

theorem encoded_rows_perm {α β : Type*} (C : Nat) (edges : List α)
    (encode : α → List β) :
    ((occurrenceMajor C edges).map encode).Perm ((copyMajor C edges).map encode) :=
  (occurrenceMajor_perm_copyMajor C edges).map encode

open DFVSGames.Foundations.Target

theorem countSatisfied_eq {n q : Nat} (C : Nat)
    (edges : List (Constraint n q)) (labeling : Fin n → Fin q) :
    countSatisfied labeling (occurrenceMajor C edges) =
      countSatisfied labeling (copyMajor C edges) :=
  DFVSGames.Integration.InstanceEquivalences.countSatisfied_perm labeling
    (occurrenceMajor_perm_copyMajor C edges)

end DFVSGames.MachineUniformCopyOrder


namespace DFVSGames.Reduction.WeightRounding

def floorMass (D q : Nat) (ps : List Nat) : Nat :=
  (ps.map (fun p => D * p / q)).sum

def roundCounts (D q : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | 0, p :: ps => (D * p / q) :: roundCounts D q 0 ps
  | r + 1, p :: ps => (D * p / q + 1) :: roundCounts D q r ps

def deficit (D q : Nat) (ps : List Nat) : Nat := D - floorMass D q ps

def rounded (D q : Nat) (ps : List Nat) : List Nat :=
  roundCounts D q (deficit D q ps) ps

theorem length_roundCounts (D q r : Nat) (ps : List Nat) :
    (roundCounts D q r ps).length = ps.length := by
  induction ps generalizing r with
  | nil => simp [roundCounts]
  | cons p ps ih => cases r <;> simp [roundCounts, ih]

theorem sum_roundCounts (D q r : Nat) (ps : List Nat) (hr : r ≤ ps.length) :
    (roundCounts D q r ps).sum = floorMass D q ps + r := by
  induction ps generalizing r with
  | nil =>
    have : r = 0 := by simpa using hr
    subst r
    simp [roundCounts, floorMass]
  | cons p ps ih =>
    cases r with
    | zero => simp [roundCounts, floorMass, ih 0 (Nat.zero_le _)]
    | succ r =>
      have hr' : r ≤ ps.length := by simpa using hr
      simp only [roundCounts, List.sum_cons, ih r hr', floorMass,
        List.map_cons, List.sum_cons]
      omega

theorem floorMass_mul_le (D q : Nat) (ps : List Nat) :
    floorMass D q ps * q ≤ D * ps.sum := by
  induction ps with
  | nil => simp [floorMass]
  | cons p ps ih =>
    have hp := Nat.div_mul_le_self (D * p) q
    simp only [floorMass, List.map_cons, List.sum_cons, Nat.add_mul,
      Nat.mul_add] at *
    omega

theorem scaled_sum_lt (D q : Nat) (ps : List Nat) (hq : 0 < q)
    (hne : ps ≠ []) :
    D * ps.sum < (floorMass D q ps + ps.length) * q := by
  induction ps with
  | nil => contradiction
  | cons p ps ih =>
    have hp : D * p < (D * p / q + 1) * q :=
      (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
    cases ps with
    | nil => simpa [floorMass] using hp
    | cons t ts =>
      have ht := ih (by simp)
      simp only [floorMass, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.mul_add, Nat.one_mul] at *
      omega

theorem floorMass_le_target (D q : Nat) (ps : List Nat) (hq : 0 < q)
    (hmass : ps.sum = q) : floorMass D q ps ≤ D := by
  apply Nat.le_of_mul_le_mul_right (c := q) _ hq
  simpa [hmass] using floorMass_mul_le D q ps

theorem deficit_lt_length (D q : Nat) (ps : List Nat) (hq : 0 < q)
    (hmass : ps.sum = q) : deficit D q ps < ps.length := by
  have hne : ps ≠ [] := by intro h; subst ps; simp at hmass; omega
  have hlt := scaled_sum_lt D q ps hq hne
  rw [hmass] at hlt
  have ht := Nat.lt_of_mul_lt_mul_right hlt
  have hlo := floorMass_le_target D q ps hq hmass
  unfold deficit
  omega

theorem sum_rounded (D q : Nat) (ps : List Nat) (hq : 0 < q)
    (hmass : ps.sum = q) : (rounded D q ps).sum = D := by
  have hr := deficit_lt_length D q ps hq hmass
  have hl := floorMass_le_target D q ps hq hmass
  rw [rounded, sum_roundCounts D q _ ps (Nat.le_of_lt hr)]
  unfold deficit
  omega

def selectedSum : List Nat → (Nat → Bool) → Nat
  | [], _ => 0
  | p :: ps, keep => (if keep 0 then p else 0) +
      selectedSum ps (fun i => keep (i + 1))

theorem floor_entry_bounds (D q p : Nat) (hq : 0 < q) (b : Bool) :
    let n := D * p / q + if b then 1 else 0
    n * q ≤ D * p + q ∧ D * p ≤ n * q + q := by
  have hlo := Nat.div_mul_le_self (D * p) q
  have hhi : D * p < (D * p / q + 1) * q :=
    (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero, Nat.add_mul, Nat.one_mul] at * <;> omega

theorem selected_roundCounts_error (D q r : Nat) (ps : List Nat)
    (keep : Nat → Bool) (hq : 0 < q) :
    selectedSum (roundCounts D q r ps) keep * q ≤
        D * selectedSum ps keep + ps.length * q ∧
    D * selectedSum ps keep ≤
        selectedSum (roundCounts D q r ps) keep * q + ps.length * q := by
  induction ps generalizing r keep with
  | nil => simp [roundCounts, selectedSum]
  | cons p ps ih =>
    cases r with
    | zero =>
      have hi := ih 0 (fun i => keep (i + 1))
      have hp := floor_entry_bounds D q p hq false
      cases hk : keep 0 <;>
        simp only [roundCounts, selectedSum, hk, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero, Nat.zero_add, List.length_cons,
          Nat.add_mul, Nat.mul_add, Nat.one_mul] at * <;> omega
    | succ r =>
      have hi := ih r (fun i => keep (i + 1))
      have hp := floor_entry_bounds D q p hq true
      cases hk : keep 0 <;>
        simp only [roundCounts, selectedSum, hk, Bool.false_eq_true, ↓reduceIte,
          Nat.zero_add, List.length_cons,
          Nat.add_mul, Nat.mul_add, Nat.one_mul] at * <;> omega

theorem selected_rounded_error (D q : Nat) (ps : List Nat)
    (keep : Nat → Bool) (hq : 0 < q) :
    selectedSum (rounded D q ps) keep * q ≤
        D * selectedSum ps keep + ps.length * q ∧
    D * selectedSum ps keep ≤
        selectedSum (rounded D q ps) keep * q + ps.length * q :=
  selected_roundCounts_error D q _ ps keep hq

def replicateOccurrences {α : Type} : List (α × Nat) → List α
  | [] => []
  | (e, n) :: rest => List.replicate n e ++ replicateOccurrences rest

theorem length_replicateOccurrences {α : Type} (es : List (α × Nat)) :
    (replicateOccurrences es).length = (es.map Prod.snd).sum := by
  induction es with
  | nil => simp [replicateOccurrences]
  | cons en es ih =>
    rcases en with ⟨e, n⟩
    simp [replicateOccurrences, ih]

def copyIndices : List Nat → List Nat
  | [] => []
  | n :: ns => List.replicate n 0 ++ (copyIndices ns).map Nat.succ

theorem length_copyIndices (ns : List Nat) : (copyIndices ns).length = ns.sum := by
  induction ns with
  | nil => simp [copyIndices]
  | cons n ns ih => simp [copyIndices, ih]

theorem mem_copyIndices_lt (ns : List Nat) (i : Nat) (hi : i ∈ copyIndices ns) :
    i < ns.length := by
  induction ns generalizing i with
  | nil => simp [copyIndices] at hi
  | cons n ns ih =>
    simp only [copyIndices, List.mem_append] at hi
    rcases hi with hi | hi
    · have hz := List.eq_of_mem_replicate hi
      subst i
      simp
    · rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
      have hj' := ih j hj
      simp only [List.length_cons]
      omega

theorem count_copyIndices (ns : List Nat) (keep : Nat → Bool) :
    ((copyIndices ns).filter keep).length = selectedSum ns keep := by
  induction ns generalizing keep with
  | nil => simp [copyIndices, selectedSum]
  | cons n ns ih =>
    simp only [copyIndices, List.filter_append, List.length_append,
      List.filter_map, List.length_map, ih]
    cases hk : keep 0 <;> simp [hk, selectedSum, Function.comp_def]

def uniformSource (D q : Nat) (ps : List Nat) : List Nat := copyIndices (rounded D q ps)

theorem uniformSource_indices_lt (D q : Nat) (ps : List Nat) (i : Nat)
    (hi : i ∈ uniformSource D q ps) : i < ps.length := by
  have h := mem_copyIndices_lt (rounded D q ps) i hi
  simpa only [rounded, length_roundCounts] using h

theorem length_uniformSource (D q : Nat) (ps : List Nat) (hq : 0 < q)
    (hmass : ps.sum = q) : (uniformSource D q ps).length = D := by
  rw [uniformSource, length_copyIndices, sum_rounded D q ps hq hmass]

theorem uniformSource_nonempty (D q : Nat) (ps : List Nat) (hD : 0 < D)
    (hq : 0 < q) (hmass : ps.sum = q) : uniformSource D q ps ≠ [] := by
  intro h
  have hl := length_uniformSource D q ps hq hmass
  rw [h] at hl
  simp at hl
  omega

theorem uniformSource_error (D q : Nat) (ps : List Nat)
    (keep : Nat → Bool) (hq : 0 < q) :
    ((uniformSource D q ps).filter keep).length * q ≤
        D * selectedSum ps keep + ps.length * q ∧
    D * selectedSum ps keep ≤
        ((uniformSource D q ps).filter keep).length * q + ps.length * q := by
  simpa only [uniformSource, count_copyIndices] using selected_rounded_error D q ps keep hq

def ceilQuotient (n a : Nat) : Nat := (n + a - 1) / a

theorem le_ceilQuotient_mul (n a : Nat) (ha : 0 < a) :
    n ≤ ceilQuotient n a * a := by
  have he := Nat.mod_add_div (n + a - 1) a
  have hr := Nat.mod_lt (n + a - 1) ha
  unfold ceilQuotient
  rw [Nat.mul_comm a] at he
  omega

theorem ceilQuotient_le (n a : Nat) (ha : 0 < a) : ceilQuotient n a ≤ n := by
  have hm : n ≤ n * a := by
    simpa using Nat.mul_le_mul_left n ha
  unfold ceilQuotient
  apply (Nat.div_le_iff_le_mul ha).mpr
  omega

def targetDenominator (m a b : Nat) : Nat := ceilQuotient (4 * m * b) a

theorem targetDenominator_error_budget (m a b : Nat) (ha : 0 < a) :
    4 * m * b ≤ targetDenominator m a b * a :=
  le_ceilQuotient_mul _ a ha

theorem targetDenominator_size (m a b : Nat) (ha : 0 < a) :
    targetDenominator m a b ≤ 4 * b * m := by
  have h := ceilQuotient_le (4 * m * b) a ha
  simpa [targetDenominator, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem targetDenominator_positive (m a b : Nat) (hm : 0 < m)
    (ha : 0 < a) (hb : 0 < b) : 0 < targetDenominator m a b := by
  have h := targetDenominator_error_budget m a b ha
  have hp : 0 < 4 * m * b := Nat.mul_pos (Nat.mul_pos (by decide) hm) hb
  by_cases hz : targetDenominator m a b = 0
  · rw [hz] at h
    simp at h
    omega
  · omega

end DFVSGames.Reduction.WeightRounding


namespace DFVSGames.Explicit.Rounding

open scoped BigOperators

abbrev IntegerRounding := DFVSGames.Reduction.WeightRounding.ceilQuotient

def denominator (h a b : Nat) : Nat := IntegerRounding (h * b) a

theorem denominator_budget (h a b : Nat) (ha : 0 < a) :
    h * b ≤ denominator h a b * a :=
  DFVSGames.Reduction.WeightRounding.le_ceilQuotient_mul _ _ ha

theorem denominator_size (h a b : Nat) (ha : 0 < a) :
    denominator h a b ≤ b * h := by
  simpa [denominator, Nat.mul_comm] using
    DFVSGames.Reduction.WeightRounding.ceilQuotient_le (h * b) a ha

theorem denominator_positive (h a b : Nat) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) : 0 < denominator h a b := by
  have hp := Nat.mul_pos hh hb
  have he := denominator_budget h a b ha
  by_contra hn
  have hz : denominator h a b = 0 := by omega
  rw [hz] at he
  simp at he
  omega

variable {h : Nat}

def remainder (Q q : Nat) (p : Fin h → Nat) (i : Fin h) : Nat :=
  (Q * p i) % q

def priority (Q q : Nat) (p : Fin h → Nat) (i j : Fin h) : Prop :=
  remainder Q q p j < remainder Q q p i ∨
    (remainder Q q p i = remainder Q q p j ∧ i ≤ j)

instance priorityDecidable (Q q : Nat) (p : Fin h → Nat) :
    DecidableRel (priority Q q p) := fun _ _ => inferInstanceAs
      (Decidable (_ < _ ∨ (_ = _ ∧ _ ≤ _)))

instance priorityTrans (Q q : Nat) (p : Fin h → Nat) :
    IsTrans (Fin h) (priority Q q p) where
  trans := by
    intro i j k hij hjk
    unfold priority at *
    omega

instance priorityAntisymm (Q q : Nat) (p : Fin h → Nat) :
    Std.Antisymm (priority Q q p) where
  antisymm := by
    intro i j hij hji
    apply Fin.ext
    unfold priority at *
    omega

instance priorityTotal (Q q : Nat) (p : Fin h → Nat) :
    Std.Total (priority Q q p) where
  total := by
    intro i j
    unfold priority
    omega

def remainderOrder (Q q : Nat) (p : Fin h → Nat) : List (Fin h) :=
  Finset.univ.sort (priority Q q p)

theorem remainderOrder_sorted (Q q : Nat) (p : Fin h → Nat) :
    (remainderOrder Q q p).Pairwise (priority Q q p) :=
  Finset.pairwise_sort _ _

@[simp] theorem remainderOrder_length (Q q : Nat) (p : Fin h → Nat) :
    (remainderOrder Q q p).length = h := by
  simp [remainderOrder]

theorem remainderOrder_nodup (Q q : Nat) (p : Fin h → Nat) :
    (remainderOrder Q q p).Nodup := Finset.sort_nodup _ _

def floorCount (Q q : Nat) (p : Fin h → Nat) (i : Fin h) : Nat :=
  Q * p i / q

def deficit (Q q : Nat) (p : Fin h → Nat) : Nat :=
  Q - ∑ i, floorCount Q q p i

theorem floor_sum_le (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : (∑ i, floorCount Q q p i) ≤ Q := by
  have he := DFVSGames.Reduction.WeightRounding.floorMass_le_target
    Q q (List.ofFn p) hq (by simpa [List.sum_ofFn] using hmass)
  simpa [DFVSGames.Reduction.WeightRounding.floorMass, List.map_ofFn,
    List.sum_ofFn, floorCount] using he

theorem deficit_lt (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : deficit Q q p < h := by
  have he := DFVSGames.Reduction.WeightRounding.deficit_lt_length
    Q q (List.ofFn p) hq (by simpa [List.sum_ofFn] using hmass)
  simpa [DFVSGames.Reduction.WeightRounding.deficit,
    DFVSGames.Reduction.WeightRounding.floorMass, List.map_ofFn,
    List.sum_ofFn, floorCount, deficit] using he

def incremented (Q q : Nat) (p : Fin h → Nat) : Finset (Fin h) :=
  ((remainderOrder Q q p).take (deficit Q q p)).toFinset

def count (Q q : Nat) (p : Fin h → Nat) (i : Fin h) : Nat :=
  floorCount Q q p i + if i ∈ incremented Q q p then 1 else 0

theorem incremented_card (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : (incremented Q q p).card = deficit Q q p := by
  rw [incremented, List.toFinset_card_of_nodup
    ((remainderOrder_nodup Q q p).take), List.length_take,
    remainderOrder_length, Nat.min_eq_left (Nat.le_of_lt (deficit_lt Q q p hq hmass))]

theorem sum_count (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : ∑ i, count Q q p i = Q := by
  have hc := incremented_card Q q p hq hmass
  have hf := floor_sum_le Q q p hq hmass
  simp only [count, Finset.sum_add_distrib, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  rw [hc, deficit]
  omega

theorem count_error (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q) (i : Fin h) :
    count Q q p i * q ≤ Q * p i + q ∧
      Q * p i ≤ count Q q p i * q + q := by
  have hlo := Nat.div_mul_le_self (Q * p i) q
  have hhi : Q * p i < (Q * p i / q + 1) * q :=
    (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
  unfold count floorCount
  split <;> simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul] at * <;> omega

theorem incremented_priority (Q q : Nat) (p : Fin h → Nat) (i j : Fin h)
    (hi : i ∈ incremented Q q p) (hj : j ∉ incremented Q q p) :
    priority Q q p i j := by
  have hi' : i ∈ (remainderOrder Q q p).take (deficit Q q p) := by
    simpa [incremented] using hi
  have hj' : j ∉ (remainderOrder Q q p).take (deficit Q q p) := by
    simpa [incremented] using hj
  have hm : j ∈ remainderOrder Q q p := by simp [remainderOrder]
  have hd : j ∈ (remainderOrder Q q p).drop (deficit Q q p) := by
    rw [← List.take_append_drop (deficit Q q p) (remainderOrder Q q p),
      List.mem_append] at hm
    exact hm.resolve_left hj'
  have hs := remainderOrder_sorted Q q p
  rw [← List.take_append_drop (deficit Q q p) (remainderOrder Q q p),
    List.pairwise_append] at hs
  exact hs.2.2 i hi' j hd

theorem selected_count_error (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (s : Finset (Fin h)) :
    (∑ i ∈ s, count Q q p i) * q ≤ Q * (∑ i ∈ s, p i) + s.card * q ∧
    Q * (∑ i ∈ s, p i) ≤ (∑ i ∈ s, count Q q p i) * q + s.card * q := by
  constructor
  · simpa [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib] using
      (Finset.sum_le_sum fun i (_ : i ∈ s) => (count_error Q q p hq i).1)
  · simpa [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib] using
      (Finset.sum_le_sum fun i (_ : i ∈ s) => (count_error Q q p hq i).2)

theorem ratio_error (n p m Q q : Nat) (hQ : 0 < Q) (hq : 0 < q)
    (hu : n * q ≤ Q * p + m * q) (hl : Q * p ≤ n * q + m * q) :
    |(n : ℚ) / Q - (p : ℚ) / q| ≤ (m : ℚ) / Q := by
  have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hu' : (n : ℚ) * q ≤ Q * p + m * q := by exact_mod_cast hu
  have hl' : (Q : ℚ) * p ≤ n * q + m * q := by exact_mod_cast hl
  rw [div_sub_div _ _ hQ'.ne' hq'.ne', abs_div, abs_of_pos (mul_pos hQ' hq')]
  apply (div_le_iff₀ (mul_pos hQ' hq')).mpr
  calc
    |(n : ℚ) * q - (Q : ℚ) * p| ≤ (m : ℚ) * q :=
      abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    _ = ((m : ℚ) / Q) * (Q * q) := by field_simp [hQ'.ne']

theorem count_ratio_error (Q q : Nat) (p : Fin h → Nat)
    (hQ : 0 < Q) (hq : 0 < q) (i : Fin h) :
    |(count Q q p i : ℚ) / Q - (p i : ℚ) / q| ≤ 1 / (Q : ℚ) := by
  have he := count_error Q q p hq i
  simpa using ratio_error (count Q q p i) (p i) 1 Q q hQ hq
    (by simpa using he.1) (by simpa using he.2)

theorem selected_ratio_error (Q q : Nat) (p : Fin h → Nat)
    (hQ : 0 < Q) (hq : 0 < q) (s : Finset (Fin h)) :
    |((∑ i ∈ s, count Q q p i : Nat) : ℚ) / Q -
      ((∑ i ∈ s, p i : Nat) : ℚ) / q| ≤ (h : ℚ) / Q := by
  have he := selected_count_error Q q p hq s
  have hb := ratio_error _ _ _ Q q hQ hq he.1 he.2
  refine hb.trans ?_
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast hQ.le)
  exact_mod_cast (show s.card ≤ h from
    (Finset.card_le_card (Finset.subset_univ s)).trans_eq (by simp))

theorem denominator_ratio_budget (h a b : Nat) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) :
    (h : ℚ) / denominator h a b ≤ (a : ℚ) / b := by
  have hQ : (0 : ℚ) < denominator h a b := by
    exact_mod_cast denominator_positive h a b hh ha hb
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  apply (div_le_div_iff₀ hQ hb').mpr
  have hc : (h : ℚ) * b ≤ denominator h a b * (a : ℚ) := by
    exact_mod_cast denominator_budget h a b ha
  simpa [mul_comm] using hc

theorem denominator_eq_ceil (h a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    denominator h a b = Nat.ceil ((h : ℚ) / ((a : ℚ) / b)) := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hr : (h : ℚ) / ((a : ℚ) / b) = ((h * b : Nat) : ℚ) / a := by
    push_cast
    field_simp [ha'.ne', hb'.ne']
  rw [hr]
  apply le_antisymm
  · unfold denominator IntegerRounding DFVSGames.Reduction.WeightRounding.ceilQuotient
    apply (Nat.div_le_iff_le_mul ha).mpr
    have hc := (div_le_iff₀ ha').mp (Nat.le_ceil (((h * b : Nat) : ℚ) / a))
    have hn : h * b ≤ Nat.ceil (((h * b : Nat) : ℚ) / a) * a := by
      exact_mod_cast hc
    omega
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ ha').mpr
    exact_mod_cast denominator_budget h a b ha

theorem selected_tolerance (a b q : Nat) (p : Fin h → Nat)
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (s : Finset (Fin h)) :
    |((∑ i ∈ s, count (denominator h a b) q p i : Nat) : ℚ) /
          denominator h a b - ((∑ i ∈ s, p i : Nat) : ℚ) / q| ≤
      (a : ℚ) / b :=
  (selected_ratio_error _ q p (denominator_positive h a b hh ha hb) hq s).trans
    (denominator_ratio_budget h a b hh ha hb)

theorem selected_weight_error (Q q : Nat) (p : Fin h → Nat)
    (hQ : 0 < Q) (hq : 0 < q) (keep : Fin h → Bool) :
    |(∑ i, if keep i then (count Q q p i : ℚ) / Q else 0) -
      (∑ i, if keep i then (p i : ℚ) / q else 0)| ≤ (h : ℚ) / Q := by
  have he := selected_ratio_error Q q p hQ hq (Finset.univ.filter fun i => keep i)
  simpa [Nat.cast_sum, Finset.sum_filter, div_eq_mul_inv, Finset.sum_mul, ite_mul] using he

theorem selected_weight_tolerance (a b q : Nat) (p : Fin h → Nat)
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (keep : Fin h → Bool) :
    |(∑ i, if keep i then (count (denominator h a b) q p i : ℚ) /
        denominator h a b else 0) -
      (∑ i, if keep i then (p i : ℚ) / q else 0)| ≤ (a : ℚ) / b :=
  (selected_weight_error _ q p (denominator_positive h a b hh ha hb) hq keep).trans
    (denominator_ratio_budget h a b hh ha hb)

def copies (Q q : Nat) (p : Fin h → Nat) : List (Fin h) :=
  (List.ofFn fun i => List.replicate (count Q q p i) i).flatten

theorem copies_length (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : (copies Q q p).length = Q := by
  simpa [copies, List.map_ofFn, List.sum_ofFn] using sum_count Q q p hq hmass

theorem copies_nonempty (Q q : Nat) (p : Fin h → Nat) (hQ : 0 < Q)
    (hq : 0 < q) (hmass : ∑ i, p i = q) : copies Q q p ≠ [] := by
  intro he
  have hl := copies_length Q q p hq hmass
  rw [he] at hl
  simp at hl
  omega

theorem copies_filter_length (Q q : Nat) (p : Fin h → Nat) (keep : Fin h → Bool) :
    ((copies Q q p).filter keep).length =
      ∑ i, if keep i then count Q q p i else 0 := by
  simp [copies, List.filter_flatten, List.map_ofFn, List.sum_ofFn,
    List.filter_replicate, apply_ite]

theorem count_le (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) (i : Fin h) : count Q q p i ≤ Q := by
  calc
    count Q q p i ≤ ∑ j, count Q q p j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = Q := sum_count Q q p hq hmass

end DFVSGames.Explicit.Rounding


namespace DFVSGames.MachineUniformRounding

open scoped BigOperators
open DFVSGames.Explicit.Rounding

theorem denominator_uniform (h C : Nat) : denominator h 1 C = C * h := by
  simp [denominator, IntegerRounding,
    DFVSGames.Reduction.WeightRounding.ceilQuotient, Nat.mul_comm]

theorem denominator_uniform_eq_ceil (h C : Nat) (hC : 0 < C) :
    C * h = Nat.ceil ((h : ℚ) / (1 / (C : ℚ))) := by
  simpa only [denominator_uniform, Nat.cast_one] using
    denominator_eq_ceil h 1 C (by omega) hC

theorem uniform_mass (h : Nat) : (∑ _ : Fin h, (1 : Nat)) = h := by simp

theorem scaled_quota_uniform (h C : Nat) (hh : 0 < h) :
    (denominator h 1 C : ℚ) * (1 / (h : ℚ)) = C := by
  have hn : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [denominator_uniform]
  push_cast
  field_simp [hn]

theorem floorCount_uniform (h C : Nat) (hh : 0 < h) (i : Fin h) :
    floorCount (C * h) h (fun _ => 1) i = C := by
  simpa [floorCount, Nat.mul_comm] using Nat.mul_div_cancel_left C hh

theorem remainder_uniform (h C : Nat) (i : Fin h) :
    remainder (C * h) h (fun _ => 1) i = 0 := by
  simp [remainder]

theorem deficit_uniform (h C : Nat) (hh : 0 < h) :
    deficit (C * h) h (fun _ : Fin h => 1) = 0 := by
  simp only [deficit, floorCount_uniform h C hh]
  simp [Nat.mul_comm]

theorem incremented_uniform (h C : Nat) (hh : 0 < h) :
    incremented (C * h) h (fun _ : Fin h => 1) = ∅ := by
  simp [incremented, deficit_uniform h C hh]

theorem count_uniform (h C : Nat) (hh : 0 < h) (i : Fin h) :
    count (denominator h 1 C) h (fun _ => 1) i = C := by
  rw [denominator_uniform]
  simp [count, floorCount_uniform h C hh, incremented_uniform h C hh]

theorem copies_uniform (h C : Nat) (hh : 0 < h) :
    copies (denominator h 1 C) h (fun _ : Fin h => 1) =
      (List.ofFn fun i : Fin h => List.replicate C i).flatten := by
  simp only [copies, count_uniform h C hh]

theorem copies_uniform_length (h C : Nat) (hh : 0 < h) :
    (copies (denominator h 1 C) h (fun _ : Fin h => 1)).length = C * h := by
  rw [copies_length _ _ _ hh (uniform_mass h), denominator_uniform]

theorem normalized_count_uniform (h C : Nat) (hh : 0 < h) (hC : 0 < C)
    (i : Fin h) :
    (count (denominator h 1 C) h (fun _ => 1) i : ℚ) /
      denominator h 1 C = 1 / (h : ℚ) := by
  have hn : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hCn : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [count_uniform h C hh, denominator_uniform]
  push_cast
  field_simp [hn, hCn]

theorem selected_weights_exact (h C : Nat) (hh : 0 < h) (hC : 0 < C)
    (keep : Fin h → Bool) :
    (∑ i, if keep i then
      (count (denominator h 1 C) h (fun _ => 1) i : ℚ) / denominator h 1 C else 0) =
      ∑ i, if keep i then 1 / (h : ℚ) else 0 := by
  simp_rw [normalized_count_uniform h C hh hC]

end DFVSGames.MachineUniformRounding


namespace DFVSGames.Integration.DyadicErrors

open DFVSGames.Foundations.Target
open GapSemantics

def dyadicError (n : Nat) : RationalError where
  numerator := 1
  denominator := 2 ^ (n + 2)
  numeratorPositive := by decide
  denominatorPositive := by positivity
  belowHalf := by
    have h : 2 ^ 2 ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at h ⊢
    omega

theorem errorValue_dyadic (n : Nat) :
    errorValue (dyadicError n) = (1 / 2 : ℚ) ^ (n + 2) := by
  simp [errorValue, dyadicError]

theorem exists_dyadic_below_real {ε : ℝ} (hε : 0 < ε) :
    ∃ n : Nat, (errorValue (dyadicError n) : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n, ?_⟩
  have hnat : n + 1 ≤ 2 ^ (n + 2) :=
    le_trans (Nat.succ_le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hden : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 2) := by exact_mod_cast hnat
  have hfrac : (1 : ℝ) / 2 ^ (n + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hden
  simpa [errorValue_dyadic, div_pow] using lt_of_le_of_lt hfrac hn

theorem exists_dyadic_below (e : RationalError) :
    ∃ n : Nat, errorValue (dyadicError n) < errorValue e := by
  have he : (0 : ℝ) < errorValue e := by exact_mod_cast errorValue_pos e
  obtain ⟨n, hn⟩ := exists_dyadic_below_real he
  exact ⟨n, by exact_mod_cast hn⟩

theorem completeAt_real_of_dyadic {q n : Nat} {ε : ℝ} {g : Instance q}
    (hε : (errorValue (dyadicError n) : ℝ) ≤ ε)
    (hg : CompleteAt (dyadicError n) g) :
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length := by
  obtain ⟨labeling, hl⟩ := (completeAt_iff_real (dyadicError n) g).1 hg
  exact ⟨labeling, le_trans (sub_le_sub_left hε 1) hl⟩

theorem soundAt_real_of_dyadic {q n : Nat} {δ : ℝ} {g : Instance q}
    (hδ : (errorValue (dyadicError n) : ℝ) ≤ δ)
    (hg : SoundAt (dyadicError n) g) :
    ∀ labeling, (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ δ := by
  intro labeling
  exact le_trans ((soundAt_iff_real (dyadicError n) g).1 hg labeling) hδ

end DFVSGames.Integration.DyadicErrors

end OAI
