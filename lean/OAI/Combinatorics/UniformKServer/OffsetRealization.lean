import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteTable
import OAI.Combinatorics.UniformKServer.OffsetLP

namespace OAI

noncomputable section
                                        
section

/-! Exact conditional rows for an additive-offset rational LP. -/
namespace UniformKServer.OffsetRealization
open EffectiveLP FiniteTable
theorem global_valid {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ) (A : ℚ)
    (hF : OffsetLP.Valid d u A F a) :
    FiniteFlow.Valid (globalFlow F) FiniteTable.next (fun c r j => j ∈ labels c r) u H := by
  rcases hF with ⟨ha,hn,ht,hi,hfn,ho,hii,hcost⟩
  constructor
  · intro w hw c
    simpa only [globalFlow, dite_eq_left hw] using hn ⟨w,(mem_words w).mpr hw⟩ c
  · intro w hw
    simpa only [globalFlow, dite_eq_left hw] using ht ⟨w,(mem_words w).mpr hw⟩
  · intro c
    change (if h : [].length ≤ H then F.mass ⟨[], (mem_words []).mpr h⟩ c else 0) = _
    split
    · exact hi c
    · rename_i h
      exact (h (Nat.zero_le H)).elim
  · intro w hw r c j
    simp only [globalFlow, dite_eq_left hw]
    split_ifs with hj
    · exact hfn ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c ⟨j,hj⟩
    · exact le_refl _
  · intro w hw r c j hj
    simp only [globalFlow, dite_eq_left hw, dite_eq_right hj]
  · intro w hw r c
    simp only [globalFlow, dite_eq_left hw, dite_eq_left hw.le, sum_labels]
    exact ho ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c
  · intro w hw r c'
    have hext : (w++[r]).length ≤ H := by simp only [List.length_append, List.length_singleton]; omega
    simp only [globalFlow, dite_eq_left hw, dite_eq_left hext]
    have hs (c : Config n k) :
        (∑ j, if FiniteTable.next c r j = c' then
          (if hj : j ∈ labels c r then F.flow ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c ⟨j,hj⟩ else 0)
          else 0) =
        ∑ j : Label c r, if EffectiveLP.step c r j = c' then
          F.flow ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c j else 0 := by
      rw [← sum_labels c r]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ labels c r
      · simp only [FiniteTable.next, dite_eq_left hj]
      · simp only [dite_eq_right hj, ite_self]
    simp only [hs]
    exact hii ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c'

theorem realize_proof {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ) (A : ℚ)
    (hF : OffsetLP.Valid d u A F a) :
    (∀ w r c j, 0 ≤ row F w r c j) ∧
    (∀ w r c, ∑ j, row F w r c j = 1) ∧
    (∀ w r c j, j ∉ labels c r → row F w r c j = 0) ∧
    (∀ w, w.length ≤ H →
      FiniteFlow.cost (row F) FiniteTable.next (FiniteTable.charge d) [] u w ≤
        A * OfflineDynamic.optRat d u.val w+a) := by
  have hv := global_valid d u F a A hF
  obtain ⟨hn,hs,hp,hc⟩ := FiniteFlow.realization (globalFlow F) next
    (fun c r j => j ∈ labels c r) u H fallback fallback_mem hv
  refine ⟨hn,hs,hp,?_⟩
  intro w hw
  let w' : Word n H := ⟨w,(mem_words w).mpr hw⟩
  calc
    FiniteFlow.cost (row F) FiniteTable.next (FiniteTable.charge d) [] u w =
        FiniteFlow.flowCost (globalFlow F) (FiniteTable.charge d) [] w := hc (FiniteTable.charge d) w hw
    _ = _ := flowCost_exact d F w'
    _ ≤ _ := hF.2.2.2.2.2.2.2 w'



end UniformKServer.OffsetRealization

end


end

end OAI
