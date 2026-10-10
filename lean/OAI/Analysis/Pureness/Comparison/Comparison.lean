import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Sequences

namespace OAI
open Filter Topology

namespace CuntzComparison

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A]

def CuntzSubequiv (a b : A) : Prop :=
  a ∈ closure (Set.range fun x : A => star x * b * x)

theorem cuntzSubequiv_iff_sequence {a b : A} :
    CuntzSubequiv a b ↔
      ∃ x : ℕ → A, Tendsto (fun n => star (x n) * b * x n) atTop (𝓝 a) := by
  constructor
  · intro h
    obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp h
    choose x hx using hy
    exact ⟨x, by simpa only [hx] using ht⟩
  · rintro ⟨x, hx⟩
    exact mem_closure_of_tendsto hx (Filter.Eventually.of_forall fun n => ⟨x n, rfl⟩)

theorem cuntzSubequiv_iff_norm {a b : A} :
    CuntzSubequiv a b ↔
      ∀ ε : ℝ, 0 < ε → ∃ x : A, ‖star x * b * x - a‖ < ε := by
  simp only [CuntzSubequiv, Metric.mem_closure_iff, Set.exists_range_iff,
    dist_eq_norm, norm_sub_rev]

theorem cuntzSubequiv_of_exact {a b x : A} (h : star x * b * x = a) :
    CuntzSubequiv a b :=
  subset_closure ⟨x, h⟩

theorem zero_cuntzSubequiv (b : A) : CuntzSubequiv 0 b :=
  cuntzSubequiv_of_exact (x := 0) (by simp)

@[simp] theorem cuntzSubequiv_zero_iff (a : A) : CuntzSubequiv a 0 ↔ a = 0 := by
  simp [CuntzSubequiv, Set.range_const]

theorem CuntzSubequiv.of_tendsto {a b : A} {u : ℕ → A}
    (h : ∀ n, CuntzSubequiv (u n) b) (hu : Tendsto u atTop (𝓝 a)) :
    CuntzSubequiv a b :=
  isClosed_closure.mem_of_tendsto hu (Filter.Eventually.of_forall h)

theorem CuntzSubequiv.compress {b c : A} (h : CuntzSubequiv b c) (x : A) :
    CuntzSubequiv (star x * b * x) c := by
  obtain ⟨y, hy⟩ := cuntzSubequiv_iff_sequence.mp h
  apply cuntzSubequiv_iff_sequence.mpr
  refine ⟨fun n => y n * x, ?_⟩
  have ht := (hy.const_mul (star x)).mul_const x
  simpa only [star_mul, mul_assoc] using ht

theorem CuntzSubequiv.trans {a b c : A}
    (hab : CuntzSubequiv a b) (hbc : CuntzSubequiv b c) :
    CuntzSubequiv a c := by
  obtain ⟨x, hx⟩ := cuntzSubequiv_iff_sequence.mp hab
  exact CuntzSubequiv.of_tendsto (fun n => hbc.compress (x n)) hx

end CuntzComparison

end OAI
