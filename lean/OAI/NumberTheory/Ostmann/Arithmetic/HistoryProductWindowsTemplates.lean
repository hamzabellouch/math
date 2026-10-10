import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateIndex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction

def pruned (seed : List SourceSlot) : ℕ → List SourceSlot
  | 0 => seed
  | l+1 => Template.remainder (l+1) (pruned seed l)

def sourceSum (F : SourceSlot → ℝ) (T : List SourceSlot) : ℝ := (T.map F).sum

@[simp] theorem sourceSum_append (F : SourceSlot → ℝ) (T U : List SourceSlot) :
    sourceSum F (T++U) = sourceSum F T + sourceSum F U := by simp [sourceSum]

theorem sourceSum_filter (F : SourceSlot → ℝ) (P : SourceSlot → Bool) (T : List SourceSlot) :
    sourceSum F (T.filter P) = sourceSum (fun q => if P q then F q else 0) T := by
  induction T with
  | nil => simp [sourceSum]
  | cons q T ih => cases hq : P q <;> simp [sourceSum, hq, sourceSum] at ih ⊢ <;> exact ih

theorem sourceSum_current (F : SourceSlot → ℝ) (seed : List SourceSlot) (l : ℕ) :
    sourceSum F (Template.current seed l) = (2:ℝ)^l * sourceSum F (pruned seed l) := by
  induction l generalizing F with
  | zero => simp [Template.current, pruned]
  | succ l ih =>
    simp only [Template.current, sourceSum_append, Template.remainder, sourceSum_filter,
      ih, pruned, pow_succ]
    ring

theorem sourceSum_current_filter (F : SourceSlot → ℝ) (P : SourceSlot → Bool)
    (seed : List SourceSlot) (l : ℕ) :
    sourceSum F ((Template.current seed l).filter P) =
      (2:ℝ)^l * sourceSum F ((pruned seed l).filter P) := by
  simp only [sourceSum_filter, sourceSum_current]

def fixedCenter (center : ℕ → ℝ) (q : SourceSlot) : ℝ :=
  if q.role = .bulk then 0 else center q.origin

def fixedCount (q : SourceSlot) : ℝ := if q.role = .bulk then 0 else 1

theorem sourceSum_filter_le (F : SourceSlot → ℝ) (hF : ∀q,0 ≤ F q)
    (P : SourceSlot → Bool) (T : List SourceSlot) : sourceSum F (T.filter P) ≤ sourceSum F T := by
  induction T with
  | nil => simp [sourceSum]
  | cons q T ih =>
    cases hq : P q
    · simpa [sourceSum,hq] using ih.trans (le_add_of_nonneg_left (hF q))
    · simpa [sourceSum,hq] using add_le_add_left ih (F q)

theorem sourceSum_pruned_le (F : SourceSlot → ℝ) (hF : ∀q,0 ≤ F q)
    (seed : List SourceSlot) (l : ℕ) : sourceSum F (pruned seed l) ≤ sourceSum F seed := by
  induction l with
  | zero => exact le_rfl
  | succ l ih => exact (sourceSum_filter_le F hF _ _).trans ih

theorem fixedCount_nonneg (q : SourceSlot) : 0 ≤ fixedCount q := by
  unfold fixedCount
  split_ifs <;> norm_num

theorem sourceSum_fixedCount_initial (m k : ℕ) :
    sourceSum fixedCount (Template.initial m k) = 6+4*(k:ℝ) := by
  have hr : (Template.initial m k).map SourceSlot.role = Template.initialRoles m k := by
    simp only [Template.initial, List.map_ofFn, Function.comp_def]
    exact List.ofFn_getElem
  have hc := congrArg (fun T : List SlotRole => (T.map (fun r => if r = .bulk then (0:ℝ) else 1)).sum) hr
  simp only [List.map_map, Function.comp_def] at hc
  change sourceSum fixedCount (Template.initial m k) = _ at hc
  rw [hc]
  simp [Template.initialRoles, List.flatMap_def, List.sum_flatten, List.map_const', Function.comp_def]
  ring

theorem fixedCount_current_filter_le (P : SourceSlot → Bool) (m k l : ℕ) :
    sourceSum fixedCount ((Template.current (Template.initial m k) l).filter P) ≤
      (2:ℝ)^l * (6+4*(k:ℝ)) := by
  rw [sourceSum_current_filter]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ((sourceSum_filter_le fixedCount fixedCount_nonneg _ _).trans
    (sourceSum_pruned_le fixedCount fixedCount_nonneg _ _)).trans_eq (sourceSum_fixedCount_initial m k)

theorem matches_metadata_sum {T : List SourceSlot} {xs : List SmallSlot}
    (h : Template.Matches T xs) (F : SlotRole → ℕ → ℝ) :
    (xs.map (fun q => F q.role q.origin)).sum = sourceSum (fun q => F q.role q.origin) T := by
  have he := congrArg (fun l : List (SlotRole × ℕ) => (l.map (fun q => F q.1 q.2)).sum) h
  simpa only [sourceSum,List.map_map,Function.comp_def] using he

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
