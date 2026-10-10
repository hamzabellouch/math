import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace OAI

open Filter
open scoped Topology

namespace Balanced.ProfileMarkLimit

variable {I : Type*} {l : Filter I}

theorem eventually_lt_of_detection_liminfs
    {d c m err : I → ℝ} {a b t : ℝ}
    (hd0 : ∀ᶠ i in l, 0 ≤ d i) (hc0 : ∀ᶠ i in l, 0 ≤ c i)
    (hd : a ≤ l.liminf d) (hc : b ≤ l.liminf c)
    (herr : Tendsto err l (𝓝 0))
    (hcompare : ∀ᶠ i in l, d i + c i ≤ m i + err i)
    (ht : t < a + b) : ∀ᶠ i in l, t < m i := by
  let δ : ℝ := (a + b - t) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hd' : a - δ < l.liminf d := by linarith
  have hc' : b - δ < l.liminf c := by linarith
  have hde := eventually_lt_of_lt_liminf hd'
    (show l.IsBoundedUnder (· ≥ ·) d from ⟨0, hd0⟩)
  have hce := eventually_lt_of_lt_liminf hc'
    (show l.IsBoundedUnder (· ≥ ·) c from ⟨0, hc0⟩)
  have he : ∀ᶠ i in l, err i < δ := (tendsto_order.1 herr).2 δ hδ
  filter_upwards [hde, hce, he, hcompare] with i hiD hiC hiE hi
  dsimp [δ] at hiD hiC hiE
  linarith

theorem le_liminf_of_detection_liminfs [l.NeBot]
    {d c m err : I → ℝ} {a b : ℝ}
    (hd0 : ∀ᶠ i in l, 0 ≤ d i) (hc0 : ∀ᶠ i in l, 0 ≤ c i)
    (hm0 : ∀ᶠ i in l, 0 ≤ m i) (hmB : l.IsBoundedUnder (· ≤ ·) m)
    (hd : a ≤ l.liminf d) (hc : b ≤ l.liminf c)
    (herr : Tendsto err l (𝓝 0))
    (hcompare : ∀ᶠ i in l, d i + c i ≤ m i + err i) :
    a + b ≤ l.liminf m := by
  apply (le_liminf_iff hmB.isCobounded_ge ⟨0, hm0⟩).2
  intro t ht
  exact eventually_lt_of_detection_liminfs hd0 hc0 hd hc herr hcompare ht

end Balanced.ProfileMarkLimit

end OAI
