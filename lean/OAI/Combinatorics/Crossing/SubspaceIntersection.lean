import OAI.Combinatorics.Crossing.StageDegreeBound
import OAI.Combinatorics.Crossing.DegreeCounting

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem subspace_intersection_bound (m : ℕ) (U V : Fin m → Submodule ℝ W)
    (hUV : ∀ i, Disjoint (U i) (V i)) :
    (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) ≤ (m*m/4) * finrank ℝ W := by
  let node : Fin m → ℝ := fun i => (i.val : ℝ)
  have hn : Function.Injective node := by
    intro i j hij
    apply Fin.ext
    dsimp only [node] at hij
    exact_mod_cast hij
  have ht : ∀ i, node i ≠ (-1 : ℝ) := by
    intro i
    have hnonneg : (0 : ℝ) ≤ node i := Nat.cast_nonneg i.val
    linarith
  let ell := columnIncrement U node ⊤ (-1)
  have hsum : (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) =
      ∑ h ∈ Finset.range m, ∑ j, rankIncrement U node (V j) h := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, finrank ℝ ↥(U i ⊓ V j)) =
          ∑ j, ∑ h ∈ Finset.range m, rankIncrement U node (V j) h := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Fintype.card_fin] using (interpolation_identity U node (V j) hn).symm
      _ = _ := Finset.sum_comm
  have hell : (∑ e ∈ Finset.range m, ell e) ≤ finrank ℝ W := by
    change (∑ e ∈ Finset.range m, columnIncrement U node ⊤ (-1) e) ≤ _
    rw [sum_columnIncrement]
    have he := Submodule.finrank_le (evaluationFiltration U node ⊤ (-1) m)
    simpa using he
  rw [hsum]
  calc
    (∑ h ∈ Finset.range m, ∑ j, rankIncrement U node (V j) h) ≤
        ∑ h ∈ Finset.range m, ∑ e ∈ Finset.range (h+1), e * ell e := by
      apply Finset.sum_le_sum
      intro h hh
      exact stage_degree_bound U V node hn hUV (-1) ht h
    _ ≤ (m*m/4) * finrank ℝ W := total_degree_cost_le ell m (finrank ℝ W) hell

theorem lemma2_1 (m N : ℕ) (U V : Fin m → Submodule ℝ W)
    (hN : finrank ℝ W = N) (hUV : ∀ i, U i ⊓ V i = ⊥) :
    (∑ i, ∑ j, finrank ℝ ↥(U i ⊓ V j)) ≤ (m*m/4) * N := by
  rw [← hN]
  exact subspace_intersection_bound m U V (fun i => disjoint_iff.mpr (hUV i))

end Zarankiewicz

end

end OAI
