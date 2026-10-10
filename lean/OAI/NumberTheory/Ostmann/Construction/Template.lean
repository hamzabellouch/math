import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
namespace Ostmann.Construction

structure SourceSlot where
  role : SlotRole
  origin : ℕ
  deriving DecidableEq

namespace Template

def initialRoles (m k : ℕ) : List SlotRole :=
  List.replicate m .bulk ++ List.replicate 6 .top ++
    (List.range k).flatMap (fun j => List.replicate 4 (.compensation (j+1)))

def initial (m k : ℕ) : List SourceSlot :=
  List.ofFn fun i : Fin (initialRoles m k).length => ⟨(initialRoles m k)[i], i.val⟩

def remainder (j : ℕ) (T : List SourceSlot) : List SourceSlot :=
  T.filter (fun q => decide (q.role ≠ .compensation j))

def current (seed : List SourceSlot) : ℕ → List SourceSlot
  | 0 => seed
  | l+1 => remainder (l+1) (current seed l) ++ remainder (l+1) (current seed l)

def countRole (T : List SourceSlot) (r : SlotRole) : ℕ :=
  (T.filter (fun q => decide (q.role = r))).length

@[simp] theorem countRole_append (T U : List SourceSlot) (r : SlotRole) :
    countRole (T ++ U) r = countRole T r + countRole U r := by
  simp only [countRole, List.filter_append, List.length_append]

theorem countRole_remainder (j : ℕ) (T : List SourceSlot) (r : SlotRole)
    (hr : r ≠ .compensation j) : countRole (remainder j T) r = countRole T r := by
  have hpred : (fun q : SourceSlot => decide (q.role = r) &&
      decide (q.role ≠ .compensation j)) = (fun q => decide (q.role = r)) := by
    funext q
    by_cases hq : q.role = r
    · simp only [hq, decide_true, Bool.true_and]
      exact decide_eq_true hr
    · simp only [hq, decide_false, Bool.false_and]
  simp only [countRole, remainder, List.filter_filter, hpred]

theorem countRole_current (seed : List SourceSlot) (l : ℕ) (r : SlotRole)
    (hr : ∀ j, 1 ≤ j → j ≤ l → r ≠ .compensation j) :
    countRole (current seed l) r = 2^l * countRole seed r := by
  induction l with
  | zero => simp [current]
  | succ l ih =>
    have hprev : ∀ j, 1 ≤ j → j ≤ l → r ≠ .compensation j :=
      fun j hj hjl => hr j hj (by omega)
    simp only [current, countRole_append, countRole_remainder (l+1) _ r
      (hr (l+1) (by omega) (by omega)), ih hprev, pow_succ]
    ring

theorem current_types_gt (seed : List SourceSlot)
    (hseed : ∀ q ∈ seed, ∀ j, q.role = .compensation j → 0 < j)
    (l : ℕ) : ∀ q ∈ current seed l, ∀ j, q.role = .compensation j → l < j := by
  induction l with
  | zero => exact hseed
  | succ l ih =>
    intro q hq j hrole
    have hmem : q ∈ remainder (l+1) (current seed l) := by
      simpa only [current, List.mem_append, or_self] using hq
    have hp := List.mem_filter.mp hmem
    have hneq : q.role ≠ .compensation (l+1) := of_decide_eq_true hp.2
    have hj := ih q hp.1 j hrole
    have hjne : j ≠ l+1 := by intro he; apply hneq; simpa [he] using hrole
    omega

def sample (T : List SourceSlot) (value : Fin T.length → ℕ) : List SmallSlot :=
  List.ofFn (fun i => {role := T[i].role, value := value i, origin := T[i].origin})

@[simp] theorem sample_length (T : List SourceSlot) (value : Fin T.length → ℕ) :
    (sample T value).length = T.length := by simp [sample]

end Template
end Ostmann.Construction

end

end OAI
