import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.Words

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonVariation

open Set Metric Filter Topology

lemma exists_interval_avoiding {u v : ℝ} (huv : u < v) (z : ℝ) :
    ∃ a d ε : ℝ, u < a ∧ a < d ∧ d < v ∧ 0 < ε ∧
      ∀ t ∈ Icc a d, ε ≤ |t-z| := by
  by_cases hz : z ≤ (u+v)/2
  · refine ⟨(u+3*v)/4,(u+7*v)/8,(v-u)/4,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.1]
  · have hz' : (u+v)/2 ≤ z := (lt_of_not_ge hz).le
    refine ⟨(7*u+v)/8,(3*u+v)/4,(v-u)/4,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.2]

theorem variation_region_avoiding {X : Type*} [MetricSpace X]
    (W : X → ℝ) (b c : X) (hW : ContinuousOn W ({b}ᶜ : Set X))
    {v w : X} (q : Path v w) (hqb : b ∉ range q) (hvar : W v < W w) :
    ∃ O P : Set X, IsOpen O ∧ Oᶜ.Nonempty ∧ IsCompact P ∧ IsConnected P ∧
      P ⊆ O ∧ closure O ⊆ ({b}ᶜ : Set X) ∧ c ∉ closure O ∧
      (∃ u ∈ P, ∃ v ∈ P, W u ≠ W v) ∧
      ∃ d : ℝ, 0 < d ∧ ∀ x ∈ O, d ≤ dist x b := by
  obtain ⟨a,d,ε,hva,had,hdw,hε,havoid⟩ := exists_interval_avoiding hvar (W c)
  have hWr : ContinuousOn W (range q) := hW.mono (by
    intro x hx hxb
    exact hqb (hxb ▸ hx))
  obtain ⟨u,z,p,hpq,hu,hz,hslab⟩ := value_subpath W q hWr a d had hva.le hdw.le
  let P := range p
  have hP : IsCompact P := isCompact_range p.continuous
  have hbP : b ∉ P := fun h => hqb (hpq h)
  have hcP : c ∉ P := by
    intro hc
    have he := havoid (W c) (hslab c hc)
    simp only [sub_self,abs_zero] at he
    linarith
  let U : Set X := {b}ᶜ ∩ {c}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.inter isClosed_singleton.isOpen_compl
  have hPU : P ⊆ U := by
    intro x hx
    exact ⟨fun h => hbP (h ▸ hx),fun h => hcP (h ▸ hx)⟩
  obtain ⟨O,hO,hPO,hOU⟩ := hP.exists_isOpen_closure_subset
    (hU.mem_nhdsSet.mpr hPU)
  have hbO : b ∉ closure O := fun h => (hOU h).1 rfl
  have hOne : (closure O).Nonempty := ⟨u,subset_closure (hPO p.source_mem_range)⟩
  have hdpos : 0 < infDist b (closure O) :=
    isClosed_closure.notMem_iff_infDist_pos hOne |>.mp hbO
  refine ⟨O,P,hO,⟨b,fun h => hbO (subset_closure h)⟩,hP,
    (isConnected_range p.continuous),hPO,(fun x hx => (hOU hx).1),
    (fun h => (hOU h).2 rfl),⟨u,p.source_mem_range,z,p.target_mem_range,?_⟩,
    infDist b (closure O),hdpos,?_⟩
  · rw [hu,hz]
    exact had.ne
  · intro x hx
    exact (infDist_le_dist_of_mem (subset_closure hx)).trans_eq (dist_comm b x)

end CannonVariation

end
end
end
end
end
end
end
end
end
end

end OAI
