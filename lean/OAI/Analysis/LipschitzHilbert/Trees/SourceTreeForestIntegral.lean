import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedTopEstimate
import OAI.Analysis.LipschitzHilbert.Trees.SourceDeletionForest

namespace OAI

/-! Integration of the actual finite forest sums. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem tree_list_integral_bound {ι V : Type*} [NormedAddCommGroup V]
    (r : List ι) (F : ι → ℝ×ℝ → V) (B : ι → ℝ) (E : Set (ℝ×ℝ))
    (h : ∀ i∈r, IntegrableOn (F i) E (volume.prod volume) ∧
      (∫ z in E, ‖F i z‖ ∂volume.prod volume)≤B i) :
    IntegrableOn (fun z => (r.map (fun i => F i z)).sum) E (volume.prod volume) ∧
      (∫ z in E, ‖(r.map (fun i => F i z)).sum‖ ∂volume.prod volume)≤(r.map B).sum := by
  induction r with
  | nil =>
    simp only [List.map_nil,List.sum_nil,norm_zero,integral_zero,le_refl,and_true]
    exact integrableOn_zero
  | cons a r ih =>
    have ha := h a (List.mem_cons_self)
    have hr := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    simp only [List.map_cons,List.sum_cons]
    refine ⟨ha.1.add hr.1,?_⟩
    calc
      _ ≤ ∫ z in E, ‖F a z‖+‖(r.map (fun i => F i z)).sum‖ ∂volume.prod volume :=
        integral_mono (ha.1.add hr.1).norm (ha.1.norm.add hr.1.norm) (fun z => norm_add_le _ _)
      _ = (∫ z in E, ‖F a z‖ ∂volume.prod volume)+
          (∫ z in E, ‖(r.map (fun i => F i z)).sum‖ ∂volume.prod volume) :=
        integral_add ha.1.norm hr.1.norm
      _ ≤ _ := add_le_add ha.2 hr.2

end LipschitzHilbert

end

end OAI
