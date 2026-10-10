import OAI.Analysis.CircleDomains.Topology.PathImageCount

namespace OAI

/-! Injective coordinate changes preserve the distinct intersection
bound used by the physical slice estimate. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

 theorem pathImageCount_map_le (F : C(X, Y)) (γ : C(PathTime, X)) (H : Set X)
    (hF : InjOn F (range γ ∪ H)) :
    pathImageCount (F '' H) (F.comp γ) ≤ pathImageCount H γ := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    have hti : Injective (γ ∘ t) := by
      intro i j hij
      exact ht (congrArg F hij)
    have hm (i : Fin n) : γ (t i) ∈ H := by
      obtain ⟨x, hx, heq⟩ := hH i
      have he : x = γ (t i) := hF (Or.inr hx) (Or.inl (mem_range_self _)) heq
      exact he ▸ hx
    rw [pathImageCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ imageHitAtLeast H n from ⟨t, hti, hm⟩)).symm.le.trans
      (le_iSup (fun k => if γ ∈ imageHitAtLeast H k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

end CircleDomainRigidity

end

end OAI
