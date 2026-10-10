import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace OAI

/-! An injective continuous real function on an interval has no interior
minimum or maximum. This excludes identifying the two local branches of
a curve vertex with a single endpoint of an embedded interval. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem injective_interval_no_minimum {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b)) (hi : InjOn f (Ioo a b))
    (hm : ∀ y ∈ Ioo a b, f x ≤ f y) : False := by
  rcases hf.strictMonoOn_of_injOn_Ioo (hx.1.trans hx.2) hi with hmono | hanti
  · let y := (a+x)/2
    have hy : y ∈ Ioo a b := by constructor <;> dsimp [y] <;> linarith [hx.1,hx.2]
    have hyx : y < x := by dsimp [y]; linarith [hx.1]
    exact (not_lt_of_ge (hm y hy)) (hmono hy hx hyx)
  · let y := (x+b)/2
    have hy : y ∈ Ioo a b := by constructor <;> dsimp [y] <;> linarith [hx.1,hx.2]
    have hxy : x < y := by dsimp [y]; linarith [hx.2]
    exact (not_lt_of_ge (hm y hy)) (hanti hx hy hxy)

theorem injective_interval_no_maximum {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b)) (hi : InjOn f (Ioo a b))
    (hm : ∀ y ∈ Ioo a b, f y ≤ f x) : False := by
  apply injective_interval_no_minimum (f := -f) hx hf.neg
  · intro y hy z hz he
    exact hi hy hz (neg_injective he)
  · intro y hy
    exact neg_le_neg (hm y hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
