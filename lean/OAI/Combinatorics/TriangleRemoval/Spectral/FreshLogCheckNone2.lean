import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.FreshLogCheckNone

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

theorem freshLog_checkNoneTrace_pairwise (ν : K → PMF V) (rel : R → R → Prop)
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, z.1.2.Pairwise rel)
    (hab : as.Pairwise (fun A B =>
      ∀ x ∈ (freshLog ν A).support, ∀ y ∈ (freshLog ν B).support,
        ∀ c ∈ x.1.2, ∀ d ∈ y.1.2, rel c d))
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) :
    z.1.2.Pairwise rel := by
  induction as generalizing z with
  | nil =>
    have heq : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simp [heq]
  | cons A as ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hab
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxR := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      apply List.pairwise_append.mpr
      refine ⟨hxR, ih has htail hw, ?_⟩
      intro c hc
      exact freshLog_checkNoneTrace_forall ν (rel c) as
        (fun B hB y hy' d hd => hhead B hB x hx y hy' c hc d hd) hw
    · simp only [hb, ↓reduceIte, freshLog, PMF.mem_support_pure_iff] at hy
      subst y
      exact hxR

end SharpTerminalLeave.ExposureTree

end

end OAI
