import Mathlib
import OAI.Analysis.PathSelection.RecursiveClocks
import OAI.Analysis.PathSelection.SectorInduction

namespace OAI

/-! Eventual monotonicity of clock representations of admissible functions. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace PathSelection.Statement

open Set Filter Topology DegeneratingTrees.Clock

lemma eventuallyMonotoneOrConstant_of_clock {xs : List (ℝ → ℝ)}
    (hxs : ValidClocks xs) {f : ℝ → ℝ}
    (hf : ClockGerm xs (fun u => (f u : ℂ))) :
    EventuallyMonotoneOrConstant f := by
  obtain ⟨U, hconst | hmono | hanti⟩ := hf.eventually_monotone hxs
  · exact ⟨U, Or.inr (Or.inr hconst)⟩
  · exact ⟨U, Or.inl hmono.monotoneOn⟩
  · exact ⟨U, Or.inr (Or.inl hanti.antitoneOn)⟩

 

lemma Admissible.monotone_realValue_of_clock {m n : ℕ}
    {P : ComplexPoint m n → ℂ} {z₀ : Fin n → ℝ} (hP : Admissible P z₀)
    {γ : ℝ → RealPoint m n}
    (hL : ∀ i : Fin m, Tendsto (fun u => (γ u).1 i) atTop atTop)
    (hz : Tendsto (fun u => (γ u).2) atTop (𝓝 z₀))
    {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    (hclock : ClockGerm xs (fun u => P (complexify (γ u)))) :
    EventuallyMonotoneOrConstant (fun u => realValue P (γ u)) := by
  apply eventuallyMonotoneOrConstant_of_clock hxs
  apply hclock.congr
  filter_upwards [hP.eventually_realValue_eq hL hz] with u hu
  exact hu.symm

end PathSelection.Statement
end

end OAI
