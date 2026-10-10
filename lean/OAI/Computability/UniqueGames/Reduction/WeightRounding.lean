import Std

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.WeightRounding

def floorMass (D q : Nat) (ps : List Nat) : Nat :=
  (ps.map (fun p => D * p / q)).sum

/-- Increment the first `r` floors, in the original occurrence order. -/
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

/-- Equation (4.7), total mass: the output has exactly the chosen denominator. -/
theorem sum_rounded (D q : Nat) (ps : List Nat) (hq : 0 < q)
    (hmass : ps.sum = q) : (rounded D q ps).sum = D := by
  have hr := deficit_lt_length D q ps hq hmass
  have hl := floorMass_le_target D q ps hq hmass
  rw [rounded, sum_roundCounts D q _ ps (Nat.le_of_lt hr)]
  unfold deficit
  omega

/-- Sum only the positions selected by an arbitrary predicate. -/
def selectedSum : List Nat → (Nat → Bool) → Nat
  | [], _ => 0
  | p :: ps, keep => (if keep 0 then p else 0) +
      selectedSum ps (fun i => keep (i + 1))

/-- The two inequalities encode `|nᵢ − D pᵢ/q| ≤ 1`. -/
theorem floor_entry_bounds (D q p : Nat) (hq : 0 < q) (b : Bool) :
    let n := D * p / q + if b then 1 else 0
    n * q ≤ D * p + q ∧ D * p ≤ n * q + q := by
  have hlo := Nat.div_mul_le_self (D * p) q
  have hhi : D * p < (D * p / q + 1) * q :=
    (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero, Nat.add_mul, Nat.one_mul] at * <;> omega

/-- Equation (4.8) for every selection of occurrences, before dividing by `Dq`.
    The selection can be the equations satisfied by any particular assignment. -/
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

/-- Output occurrence indices; each integer count gives that many separate copies. -/
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

/-- Copying occurrences preserves the satisfaction test for every assignment. -/
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

/-- Full occurrence-list form of (4.8), quantified over all satisfaction tests. -/
theorem uniformSource_error (D q : Nat) (ps : List Nat)
    (keep : Nat → Bool) (hq : 0 < q) :
    ((uniformSource D q ps).filter keep).length * q ≤
        D * selectedSum ps keep + ps.length * q ∧
    D * selectedSum ps keep ≤
        ((uniformSource D q ps).filter keep).length * q + ps.length * q := by
  simpa only [uniformSource, count_copyIndices] using selected_rounded_error D q ps keep hq

/-- Integer ceiling; valid for positive `a`. -/
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

/-- Cross-multiplied statement `m / D ≤ γ₀ / 4`. -/
theorem targetDenominator_error_budget (m a b : Nat) (ha : 0 < a) :
    4 * m * b ≤ targetDenominator m a b * a :=
  le_ceilQuotient_mul _ a ha

/-- At fixed rational `γ₀`, the number of output occurrences is linear in `m`.
    This is an output-size bound, not a machine-model complexity theorem. -/
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

end UniqueGamesTheorem.Reduction.WeightRounding

end

end OAI
