import OAI.Combinatorics.EditApproximation.Coarse.CoarseScalarAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayRepresentation

namespace OAI

namespace EditApproximation

/-- The same map trace, allowing a uniform factor two for callback allocation. -/
theorem arithmeticMapAllocation_le_twice_work {α β : Type*} (f : α → β × ℕ)
    (allocation : α → ℕ) (values : List α)
    (h : ∀ a ∈ values, allocation a ≤ 2 * (f a).2) :
    arithmeticMapAllocation allocation values ≤ 2 * (arithmeticMapWithWork f values).2 := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapAllocation, arithmeticMapWithWork]
    omega

namespace BinaryFraction

def coarseGridScanAllocation (two previous : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 1
  | head :: rest =>
    let added := coarseGridAddWithWork previous two
    let next := minWithWork head added.1
    coarseGridAddAllocation previous two + head.ltAllocation added.1 +
      coarseGridScanAllocation two next.1 rest + 1

theorem coarseGridScanAllocation_le_work (two previous : BinaryFraction) (source : List BinaryFraction) :
    coarseGridScanAllocation two previous source ≤ (coarseGridScanWithWork two previous source).2 + 1 := by
  induction source generalizing previous with
  | nil => rfl
  | cons head rest ih =>
    have ha := coarseGridAddAllocation_le_work previous two
    have hm := ltAllocation_le_work head (coarseGridAddWithWork previous two).1
    have ht := ih (minWithWork head (coarseGridAddWithWork previous two).1).1
    simp only [coarseGridScanAllocation, coarseGridScanWithWork]
    simp only [minWithWork] at ht ⊢
    omega

def coarseGridLeftAllocation (two : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 0
  | head :: rest => coarseGridScanAllocation two head rest

theorem coarseGridLeftAllocation_le_work (two : BinaryFraction) (source : List BinaryFraction) :
    coarseGridLeftAllocation two source ≤ (coarseGridLeftWithWork two source).2 + source.length := by
  cases source with
  | nil => simp [coarseGridLeftAllocation, coarseGridLeftWithWork]
  | cons head rest =>
    have h := coarseGridScanAllocation_le_work two head rest
    simp only [coarseGridLeftAllocation, coarseGridLeftWithWork, List.length_cons]
    omega

theorem coarseGridLeftWithWork_length (two : BinaryFraction) (source : List BinaryFraction) :
    (coarseGridLeftWithWork two source).1.length = source.length := by
  have scan (previous : BinaryFraction) (values : List BinaryFraction) :
      (coarseGridScanWithWork two previous values).1.length = values.length + 1 := by
    induction values generalizing previous with
    | nil => rfl
    | cons head rest ih => simp only [coarseGridScanWithWork, List.length_cons, ih]
  cases source with
  | nil => rfl
  | cons head rest => exact scan head rest

def coarseGridZipMinimumAllocation : List BinaryFraction → List BinaryFraction → ℕ
  | a :: left, b :: right => a.ltAllocation b + coarseGridZipMinimumAllocation left right + 1
  | _, _ => 0

theorem coarseGridZipMinimumAllocation_le_work (left right : List BinaryFraction) :
    coarseGridZipMinimumAllocation left right ≤ (coarseGridZipMinimumWithWork left right).2 := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => exact Nat.le_refl 0
    | cons b right =>
      have hh := ltAllocation_le_work a b
      have ht := ih right
      simp only [coarseGridZipMinimumAllocation, coarseGridZipMinimumWithWork, minWithWork]
      omega

/-- Both reverse operations allocate their list spines; the element words
are shared. Includes both sweeps, their discarded arrays and the final zip. -/
def coarseGridPenaltyAllocation (two : BinaryFraction) (source : List BinaryFraction) : ℕ :=
  let left := coarseGridLeftWithWork two source
  let right := coarseGridLeftWithWork two source.reverse
  coarseGridLeftAllocation two source + coarseGridLeftAllocation two source.reverse +
    source.length + right.1.length + coarseGridZipMinimumAllocation left.1 right.1.reverse

theorem coarseGridPenaltyAllocation_le_work (two : BinaryFraction) (source : List BinaryFraction) :
    coarseGridPenaltyAllocation two source ≤ 2 * (coarseGridPenaltyWithWork two source).2 := by
  have hl := coarseGridLeftAllocation_le_work two source
  have hr := coarseGridLeftAllocation_le_work two source.reverse
  have hz := coarseGridZipMinimumAllocation_le_work
    (coarseGridLeftWithWork two source).1 (coarseGridLeftWithWork two source.reverse).1.reverse
  have hlen := coarseGridLeftWithWork_length two source.reverse
  simp only [List.length_reverse] at hr hlen
  unfold coarseGridPenaltyAllocation coarseGridPenaltyWithWork
  dsimp only
  rw [hlen]
  omega

def coarseGridZipAddAllocation : List BinaryFraction → List BinaryFraction → ℕ
  | a :: left, b :: right => coarseGridAddAllocation a b + coarseGridZipAddAllocation left right + 1
  | _, _ => 0

theorem coarseGridZipAddAllocation_le_work (left right : List BinaryFraction) :
    coarseGridZipAddAllocation left right ≤ (coarseGridZipAddWithWork left right).2 := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => exact Nat.le_refl 0
    | cons b right =>
      have hh := coarseGridAddAllocation_le_work a b
      have ht := ih right
      simp only [coarseGridZipAddAllocation, coarseGridZipAddWithWork]
      omega

def coarseBinaryAddAllocation : CoarseBinaryArray → CoarseBinaryArray → ℕ
  | some left, some right => coarseGridZipAddAllocation left right
  | _, _ => 0

theorem coarseBinaryAddAllocation_le_work (left right : CoarseBinaryArray) :
    coarseBinaryAddAllocation left right ≤ (coarseBinaryAddWithWork left right).2 := by
  cases left <;> cases right
  all_goals first | exact Nat.le_refl 0 | exact coarseGridZipAddAllocation_le_work _ _

def coarseBinaryPenaltyAllocation (two : BinaryFraction) : CoarseBinaryArray → ℕ
  | none => 0
  | some values => coarseGridPenaltyAllocation two values

theorem coarseBinaryPenaltyAllocation_le_work (two : BinaryFraction) (array : CoarseBinaryArray) :
    coarseBinaryPenaltyAllocation two array ≤ 2 * (coarseBinaryPenaltyWithWork two array).2 := by
  cases array with
  | none => exact Nat.le_refl 0
  | some values => exact coarseGridPenaltyAllocation_le_work two values

def coarseBinaryMapAllocation (allocation : BinaryFraction → ℕ) : CoarseBinaryArray → ℕ
  | none => 0
  | some values => arithmeticMapAllocation allocation values

theorem coarseBinaryMapAllocation_le_work (f : BinaryFraction → BinaryFraction × ℕ)
    (allocation : BinaryFraction → ℕ) (h : ∀ a, allocation a ≤ (f a).2) (array : CoarseBinaryArray) :
    coarseBinaryMapAllocation allocation array ≤ (coarseBinaryMapWithWork f array).2 := by
  cases array with
  | none => exact Nat.le_refl 0
  | some values => exact arithmeticMapAllocation_le_work f allocation values (fun a _ => h a)

end BinaryFraction
end EditApproximation

end OAI
