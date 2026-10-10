import OAI.Combinatorics.Crossing.MovingSegmentStability
import OAI.Combinatorics.Crossing.FiniteSeparation

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem finite_moving_points_separation {ι : Type*} [Fintype ι]
    (point : ι → ℝ → Plane) (hc : ∀ i, Continuous (point i))
    (hinj : Function.Injective (fun i => point i 0)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ i j : ι, i ≠ j →
      point i 0 ≠ point j ε ∧ point i ε ≠ point j ε := by
  classical
  let Pair := {ij : ι × ι // ij.1 ≠ ij.2}
  have hevent (p : Pair) : ∀ᶠ ε : ℝ in 𝓝 0,
      point p.val.1 0 ≠ point p.val.2 ε ∧ point p.val.1 ε ≠ point p.val.2 ε := by
    have hne := hinj.ne p.property
    have h₁ := (hc p.val.2).continuousAt.eventually_ne hne.symm
    have hd : Continuous (fun ε : ℝ => point p.val.1 ε-point p.val.2 ε) := (hc _).sub (hc _)
    have h₂ := hd.continuousAt.eventually_ne (sub_ne_zero.mpr hne)
    filter_upwards [h₁,h₂] with ε h₁ h₂
    exact ⟨h₁.symm,sub_ne_zero.mp h₂⟩
  have hex (p : Pair) := Metric.eventually_nhds_iff.mp (hevent p)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun p _ => hpos p)
  refine ⟨δ,hδ,?_⟩
  intro ε hε i j hij
  exact hprop ⟨(i,j),hij⟩ (by
    simpa [Real.dist_eq] using hε.trans (hbound ⟨(i,j),hij⟩ (Finset.mem_univ _)))

end Zarankiewicz

end

end OAI
