import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! # Extended distances on a connected space are finite -/

namespace PolycyclicRecognition

theorem edist_ne_top_of_connected {X : Type*} [EMetricSpace X] [ConnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have h : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hu : Metric.eball x ⊤ = Set.univ :=
    h.eq_univ ⟨x, by simp only [Metric.mem_eball, edist_self]; exact bot_lt_top⟩
  have hy : y ∈ Metric.eball x ⊤ := hu.symm ▸ Set.mem_univ y
  exact (show edist y x < ⊤ from hy).ne ∘ (edist_comm x y ▸ ·)

end PolycyclicRecognition

end OAI
