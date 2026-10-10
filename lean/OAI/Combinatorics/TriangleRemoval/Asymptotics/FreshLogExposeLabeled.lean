import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.MapOutput

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
variable {K V O R A : Type*}

theorem freshLog_exposeLabeled_support (ν : K → PMF V) (key : A → K) (as : List A)
    {z : List (A × V) × List K}
    (hz : z ∈ (freshLog ν (exposeLabeled key as)).support) :
    z.1.map Prod.fst = as ∧ z.2 = as.map key := by
  induction as generalizing z with
  | nil =>
    have heq : z = ([],[]) := by simpa [exposeLabeled, freshLog] using hz
    simp [heq]
  | cons a as ih =>
    simp only [exposeLabeled, freshLog, PMF.mem_support_bind_iff] at hz
    obtain ⟨v,_,hv⟩ := hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    rw [freshLog_bind] at hy
    obtain ⟨w,hw,hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    have heq : y = ((a,v)::w.1,w.2) := by
      simpa [freshLog, PMF.pure_map, List.append_nil] using hy
    obtain ⟨hvals,hkeys⟩ := ih hw
    simp [heq,hvals,hkeys]

theorem freshLog_checkNoneTrace_support (ν : K → PMF V) (keys : R → List K)
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, z.2 = z.1.2.flatMap keys)
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) :
    z.2 = z.1.2.flatMap keys := by
  induction as generalizing z with
  | nil =>
    have heq : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simp [heq]
  | cons A as ih =>
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxlog := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      simp only [List.flatMap_append, hxlog, ih has hw]
    · simp only [hb, ↓reduceIte, freshLog, PMF.mem_support_pure_iff] at hy
      subst y
      simp [hxlog]

end SharpTerminalLeave.ExposureTree

end

end OAI
