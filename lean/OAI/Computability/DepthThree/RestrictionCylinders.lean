import OAI.Computability.DepthThree.RestrictionClause
import OAI.Computability.DepthThree.RestrictionExpansion

namespace OAI

universe uDepth1 uDepth2

noncomputable section

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instDecidableEqV : DecidableEq V] [instDecidableEqI : DecidableEq I] [instFintypeI : Fintype I]

theorem Clause.eval_eq_of_scope_agree
    {V : Type uDepth1}
    [DecidableEq V]
    (C : Clause V) (x y : Cube V)
    (h : ∀ v ∈ C.scope, x v = y v) : C.eval x = C.eval y := by
  classical
  let : DecidableEq V := Classical.decEq _
  apply Bool.eq_iff_iff.mpr
  rw [Clause.eval_eq_true, Clause.eval_eq_true]
  constructor
  · rintro ⟨l, hl, hx⟩
    exact ⟨l, hl, (h l.1 (Finset.mem_image_of_mem Prod.fst hl)).symm.trans hx⟩
  · rintro ⟨l, hl, hy⟩
    exact ⟨l, hl, (h l.1 (Finset.mem_image_of_mem Prod.fst hl)).trans hy⟩

theorem Clause.violation_eq_of_scope_agree (C : Clause V) (x y : Cube V)
    (h : ∀ v ∈ C.scope, x v = y v) : C.violation x = C.violation y := by
  unfold Clause.violation
  rw [Clause.eval_eq_of_scope_agree C x y h]

theorem simultaneous_violation_iff_cylinder
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (C : I → Clause V) (T : Finset V) (P : List I) (x y : Cube V)
    (hn : ∀ i ∈ P, (C i).Normalized)
    (hy : ∀ i ∈ P, (C i).violation y = true)
    (hout : ∀ v ∉ T, x v = y v) :
    (∀ i ∈ P, (C i).violation x = true) ↔
      ∀ v ∈ revealed (fun i => (C i).scope) T P, x v = y v := by
  constructor
  · intro hx v hv
    obtain ⟨i, hi, hvi, hvt⟩ := (mem_revealed (fun i => (C i).scope) T P v).mp hv
    have hxv := (Clause.violation_eq_true_iff_forbidden (hn i hi) x).mp
      (hx i hi) v hvi
    have hyv := (Clause.violation_eq_true_iff_forbidden (hn i hi) y).mp
      (hy i hi) v hvi
    exact hxv.trans hyv.symm
  · intro hxy i hi
    apply (Clause.violation_eq_true_iff_forbidden (hn i hi) x).mpr
    intro v hv
    have hsame : x v = y v := by
      by_cases ht : v ∈ T
      · exact hxy v ((mem_revealed (fun i => (C i).scope) T P v).mpr
          ⟨i, hi, hv, ht⟩)
      · exact hout v ht
    exact hsame.trans ((Clause.violation_eq_true_iff_forbidden (hn i hi) y).mp
      (hy i hi) v hv)

theorem violation_eq_of_covered
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (C : I → Clause V) (T U : Finset V) (x y : Cube V) (i : I)
    (hc : residual (fun i => (C i).scope) T U i = ∅)
    (hU : ∀ v ∈ U, x v = y v) (hout : ∀ v ∉ T, x v = y v) :
    (C i).violation x = (C i).violation y := by
  apply Clause.violation_eq_of_scope_agree
  intro v hv
  by_cases ht : v ∈ T
  · have hu : v ∈ U := by
      by_contra hu
      have hm : v ∈ residual (fun i => (C i).scope) T U i := by
        simp [residual, hv, ht, hu]
      rw [hc] at hm
      exact Finset.notMem_empty v hm
    exact hU v hu
  · exact hout v ht

theorem coveredCount_eq_of_agree
    (C : I → Clause V) (T U : Finset V) (x y : Cube V)
    (hU : ∀ v ∈ U, x v = y v) (hout : ∀ v ∉ T, x v = y v) :
    coveredCount (fun i => (C i).scope) T (fun i => (C i).violation x) U =
      coveredCount (fun i => (C i).scope) T (fun i => (C i).violation y) U := by
  unfold coveredCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hv⟩
    exact ⟨hc, (violation_eq_of_covered C T U x y i hc hU hout).symm.trans hv⟩
  · rintro ⟨hc, hv⟩
    exact ⟨hc, (violation_eq_of_covered C T U x y i hc hU hout).trans hv⟩

theorem coveredCount_eq_on_larger_cylinder
    (C : I → Clause V) (T U Z : Finset V) (x y : Cube V) (hUZ : U ⊆ Z)
    (hZ : ∀ v ∈ Z, x v = y v) (hout : ∀ v ∉ T, x v = y v) :
    coveredCount (fun i => (C i).scope) T (fun i => (C i).violation x) U =
      coveredCount (fun i => (C i).scope) T (fun i => (C i).violation y) U :=
  coveredCount_eq_of_agree C T U x y (fun v hv => hZ v (hUZ hv)) hout

def cylinderCNF (U : Finset V) (pattern : Cube V) : CNF V :=
  U.toList.map fun v => ({(v, pattern v)} : Clause V)

@[simp] theorem cylinderCNF_eval_eq_true
    {V : Type uDepth1}
    [DecidableEq V]
    (U : Finset V) (pattern x : Cube V) :
    (cylinderCNF U pattern).eval x = true ↔ ∀ v ∈ U, x v = pattern v := by
  classical
  simp [cylinderCNF, CNF.eval_eq_true]

theorem cylinderCNF_eval (U : Finset V) (pattern x : Cube V) :
    (cylinderCNF U pattern).eval x = decide (∀ v ∈ U, x v = pattern v) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [cylinderCNF_eval_eq_true, decide_eq_true_eq]

theorem cylinderCNF_widthAtMost
    {V : Type uDepth1}
    [DecidableEq V]
    (U : Finset V) (pattern : Cube V)
    {b : ℕ} (hb : 1 ≤ b) : (cylinderCNF U pattern).WidthAtMost b := by
  intro C hC
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hC
  simpa [Clause.width, Clause.scope] using hb

theorem cylinderCNF_normalized
    {V : Type uDepth1}
    [DecidableEq V]
    (U : Finset V) (pattern : Cube V) :
    (cylinderCNF U pattern).Normalized := by
  intro C hC
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hC
  intro w hf ht
  have hf' : (w, false) = (v, pattern v) := Finset.mem_singleton.mp hf
  have ht' : (w, true) = (v, pattern v) := Finset.mem_singleton.mp ht
  have : (false : Bool) = true := congrArg Prod.snd (hf'.trans ht'.symm)
  cases this

section ActualRestriction

variable [instFintypeV : Fintype V]

theorem fill_agree_outside_live
    {V : Type uDepth1}
    [DecidableEq V]
    [Fintype V]
    (σ : Restriction V) (x y : Cube (Live σ))
    (v : V) (hv : σ v ≠ none) : fill σ x v = fill σ y v := by
  simp [fill, hv]

theorem simultaneous_restricted_violation_iff
    (C : I → Clause V) (σ : Restriction V) (T : Finset V)
    (hT : ∀ v, v ∈ T ↔ σ v = none) (P : List I)
    (x y : Cube (Live σ)) (hn : ∀ i ∈ P, (C i).Normalized)
    (hy : ∀ i ∈ P, (C i).violation (fill σ y) = true) :
    (∀ i ∈ P, (C i).violation (fill σ x) = true) ↔
      ∀ v ∈ revealed (fun i => (C i).scope) T P, fill σ x v = fill σ y v := by
  apply simultaneous_violation_iff_cylinder C T P (fill σ x) (fill σ y) hn hy
  intro v hv
  apply fill_agree_outside_live
  intro he
  exact hv ((hT v).mpr he)

end ActualRestriction

end DepthThreeLowerBound

end

end OAI
