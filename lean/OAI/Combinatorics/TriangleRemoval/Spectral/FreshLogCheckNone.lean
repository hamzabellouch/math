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
variable {K V R : Type*}

theorem freshLog_checkNoneTrace_forall (ν : K → PMF V) (P : R → Prop)
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, ∀ c ∈ z.1.2, P c)
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) :
    ∀ c ∈ z.1.2, P c := by
  induction as generalizing z with
  | nil =>
    have heq : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simp [heq]
  | cons A as ih =>
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxP := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hxP c hc
      · exact ih has hw c hc
    · simp only [hb, ↓reduceIte, freshLog, PMF.mem_support_pure_iff] at hy
      subst y
      exact hxP

end SharpTerminalLeave.ExposureTree

end

end OAI
