import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateIndex
import OAI.NumberTheory.Ostmann.Construction.PrimeSources
import OAI.NumberTheory.Ostmann.Construction.TemplateReinsert

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem assignmentPrior_component_mass_ne_zero (sources : SourceFamily)
    (T : List SourceSlot) (x : SourceAssignment sources T)
    (hx : (assignmentPrior sources T).mass x ≠ 0) (i : Fin T.length) :
    (sources T[i].origin).law.mass (x i) ≠ 0 := by
  change (∏j,(sources T[j].origin).law.mass (x j)) ≠ 0 at hx
  exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)

theorem assignedSlots_source_mass_ne_zero (sources : SourceFamily)
    (T : List SourceSlot) (x : SourceAssignment sources T)
    (hx : (assignmentPrior sources T).mass x ≠ 0)
    (z : SmallSlot) (hz : z ∈ assignedSlots sources T x) :
    sourceMass sources z ≠ 0 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  simpa [sourceMass] using assignmentPrior_component_mass_ne_zero sources T x hx i

namespace Template

theorem mem_current_mem_seed {seed : List SourceSlot} {l : ℕ} {q : SourceSlot}
    (hq : q ∈ current seed l) : q ∈ seed := by
  induction l with
  | zero => exact hq
  | succ l ih =>
    have hrem : q ∈ remainder (l+1) (current seed l) := by
      simpa only [current,List.mem_append,or_self] using hq
    exact ih (List.mem_filter.mp hrem).1

theorem mem_extracted_current_mem_seed {seed : List SourceSlot} {j l : ℕ}
    {q : SourceSlot} (hq : q ∈ extracted j (current seed l)) : q ∈ seed :=
  mem_current_mem_seed (List.mem_filter.mp hq).1

theorem mem_remainder_current_mem_seed {seed : List SourceSlot} {j l : ℕ}
    {q : SourceSlot} (hq : q ∈ remainder j (current seed l)) : q ∈ seed :=
  mem_current_mem_seed (List.mem_filter.mp hq).1

theorem initial_nonbulk_origin_bounds {m k : ℕ} {q : SourceSlot}
    (hq : q ∈ initial m k) (hr : q.role ≠ .bulk) :
    m ≤ q.origin ∧ q.origin < m+6+4*k := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  dsimp only at hr ⊢
  have hrole := InitialCoordinatesTemplate.initialRoles_bulk_iff m k i
  have hi := i.isLt
  simp only [InitialCoordinatesTemplate.initialRoles_length] at hi
  constructor
  · by_contra h
    apply hr
    exact hrole.mpr (by omega)
  · exact hi

end Template
end Ostmann.Construction

end

end OAI
