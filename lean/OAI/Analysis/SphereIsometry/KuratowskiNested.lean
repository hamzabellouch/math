import OAI.Analysis.SphereIsometry.KuratowskiTotalBounded
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Order.Basic

namespace OAI

/-!
# Nested sets with vanishing Kuratowski measure

Small finite diameter covers make the range of a selected sequence totally
bounded. Its compact closure supplies a point in all the nested closed sets.
The whole intersection is compact by its own arbitrarily fine finite covers.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Tingley

section Pseudometric

variable {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]

/-- A nested sequence with arbitrarily fine finite diameter covers has a
nonempty compact intersection. No original member is assumed compact. -/
theorem nonempty_isCompact_iInter_of_finiteDiameterCover
    (C : ℕ → Set E) (hanti : Antitone C)
    (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, FiniteDiameterCover (C N) ε) :
    (⋂ n, C n).Nonempty ∧ IsCompact (⋂ n, C n) := by
  classical
  let x : ℕ → E := fun n => Classical.choose (hne n)
  have hx : ∀ n, x n ∈ C n := fun n => Classical.choose_spec (hne n)
  have htotal : TotallyBounded (range x) :=
    totallyBounded_range_of_nested_finiteDiameterCover C hanti x hx hsmall
  let K : Set E := closure (range x)
  have hKclosed : IsClosed K := isClosed_closure
  have hKcompact : IsCompact K :=
    TotallyBounded.isCompact_of_isClosed htotal.closure hKclosed
  let D : ℕ → Set E := fun n => K ∩ C n
  have hDanti : ∀ n, D (n + 1) ⊆ D n := by
    intro n z hz
    exact ⟨hz.1, hanti (Nat.le_succ n) hz.2⟩
  have hDnonempty : ∀ n, (D n).Nonempty := by
    intro n
    exact ⟨x n, subset_closure (mem_range_self n), hx n⟩
  have hDclosed : ∀ n, IsClosed (D n) :=
    fun n => hKclosed.inter (hclosed n)
  have hDcompact : IsCompact (D 0) := hKcompact.inter_right (hclosed 0)
  have hnonempty : (⋂ n, C n).Nonempty := by
    obtain ⟨z, hz⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        D hDanti hDnonempty hDcompact hDclosed
    refine ⟨z, mem_iInter.mpr ?_⟩
    intro n
    exact (mem_iInter.mp hz n).2
  have hinter : TotallyBounded (⋂ n, C n) := by
    apply totallyBounded_iff_finiteDiameterCover.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    exact hN.mono_set (fun z hz => mem_iInter.mp hz N)
  exact ⟨hnonempty,
    TotallyBounded.isCompact_of_isClosed hinter (isClosed_iInter hclosed)⟩

end Pseudometric

section Metric

variable {E : Type*} [MetricSpace E] [CompleteSpace E]

/-- A decreasing sequence of nonempty closed sets in a complete metric space
has a nonempty compact intersection when its Kuratowski measures tend to zero.
Boundedness of the first set supplies boundedness at every later index. -/
theorem nonempty_isCompact_iInter_of_chi_tendsto_zero
    (C : ℕ → Set E)
    (hanti : Antitone C)
    (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n))
    (hbound : Bornology.IsBounded (C 0))
    (hchi : Tendsto (fun n => chi (C n)) atTop (𝓝 0)) :
    (⋂ n, C n).Nonempty ∧ IsCompact (⋂ n, C n) := by
  have hbounded : ∀ n, Bornology.IsBounded (C n) :=
    fun n => hbound.subset (hanti (Nat.zero_le n))
  apply nonempty_isCompact_iInter_of_finiteDiameterCover C hanti hne hclosed
  intro ε hε
  obtain ⟨N, hN⟩ := (hchi.eventually (gt_mem_nhds hε)).exists
  obtain ⟨δ, _hδ, hδε, hcover⟩ := exists_cover_of_chi_lt (hbounded N) hN
  exact ⟨N, hcover.mono_radius hδε.le⟩

end Metric

end Tingley

end

end OAI
