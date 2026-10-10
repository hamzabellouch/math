import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.FineCoherentRegions

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def supportCellRoot {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) : SupportCellDescendant μ R hR k z where
  depth := 0
  center := z
  mem_net := by simpa only [Nat.add_zero] using! z.property
  ancestor := by simp only [supportLatticeAncestor, supportLatticeCenter, netAncestor_zero]

theorem SupportCellDescendant.eq_root_of_zero_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    i = supportCellRoot μ R hR k z := by
  have hc := (i.zero_depth_geometry hi).1
  rcases i with ⟨t, x, hx, ha⟩
  change t = 0 at hi
  subst t
  change x = (z : Ambient d) at hc
  subst x
  rfl

end

end RieszRectifiability

end OAI
