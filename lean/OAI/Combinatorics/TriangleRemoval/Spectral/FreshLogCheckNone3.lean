import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.MapOutput

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

theorem freshLog_checkNoneTrace_append (ν : K → PMF V)
    (P : List R → Prop) (h0 : P [])
    (happend : ∀ a b, P a → P b → P (a ++ b))
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, P z.1.2)
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) : P z.1.2 := by
  induction as generalizing z with
  | nil =>
    have he : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simpa only [he] using h0
  | cons A as ih =>
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxa := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb,Bool.false_eq_true,↓reduceIte,freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      exact happend _ _ hxa (ih has hw)
    · simp only [hb,↓reduceIte,freshLog,PMF.mem_support_pure_iff] at hy
      subst y
      exact hxa

end SharpTerminalLeave.ExposureTree

end

end OAI
