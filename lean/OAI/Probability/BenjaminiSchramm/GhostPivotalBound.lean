import OAI.Probability.BenjaminiSchramm.GhostAvoidance
import OAI.Probability.BenjaminiSchramm.GhostFanBK

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma finiteGhostConnection_mono_marks (G : BondGraph V E) (x : V)
    {m n : Set V} (hmn : m ⊆ n) :
    finiteGhostConnection G x id m ⊆ finiteGhostConnection G x id n := by
  rintro ω ⟨v,hv,hconn⟩
  exact ⟨v,hmn hv,hconn⟩

theorem ghost_avoidance_bk (G : BondGraph V E) (p : unitInterval) (x : V)
    (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    (∫⁻ m, ∫⁻ n, if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n then
      law p (DisjointOccurrence (finiteGhostConnection G x id m)
        (finiteGhostConnection G x id n)) else 0 ∂ghostFieldLaw h w ∂ghostFieldLaw h w) ≤
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) ^ 2 *
        (∫⁻ m, law p (finiteGhostConnection G x id m) ∂ghostFieldLaw h w) ^ 2 := by
  let F := fun z : Set V × Set V => law p
    (DisjointOccurrence (finiteGhostConnection G x id z.1) (finiteGhostConnection G x id z.2))
  have hF : Measurable F := measurable_measure_prodMk_left (ν := law p)
    (measurableSet_ghostDisjointOccurrence G x id)
  have hmono : ∀ m m', m ⊆ m' → ∀ n n', n ⊆ n' → F (m,n) ≤ F (m',n') := by
    intro m m' hmm n n' hnn
    exact measure_mono (disjointOccurrence_mono
      (finiteGhostConnection_mono_marks G x hmm) (finiteGhostConnection_mono_marks G x hnn))
  exact (two_ghost_avoidance_upper h w S F hF hmono).trans
    (mul_le_mul' le_rfl (averaged_ghostConnection_bk G x id p (ghostFieldLaw h w)))

end Percolation.BenjaminiSchramm

end

end OAI
