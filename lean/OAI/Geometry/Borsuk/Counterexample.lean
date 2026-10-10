import Mathlib
import OAI.Geometry.Borsuk.Projectors.Within
import OAI.Geometry.Borsuk.FiniteCases.Cases145

namespace OAI

open Set MeasureTheory
namespace BorsukNine
attribute [local instance] Classical.propDecidable

theorem Admissible.support_ten_system {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f) :
    FiniteObstruction.TenSystem (fun U => U.card = 3 ∧ SupportFace f U)
      (fun S => S.card = 4 ∧ SupportFace f S) := by
  classical
  constructor
  · intro S hS
    exact hS.1
  · intro S U hS hUS hUc
    exact ⟨hUc,hS.2.mono hUS⟩
  · intro U hU
    obtain ⟨S,hSc,hSf,hUS⟩ := hf.face_extends_four hU.2
    exact ⟨S,⟨hSc,hSf⟩,hUS⟩
  · intro S U hS hUS hUc
    obtain ⟨S',hS'c,hS'f,hUS',hne⟩ := hf.tetra_no_free_triangle hS.1 hS.2 hUS hUc
    exact ⟨S',⟨hS'c,hS'f⟩,hUS',hne⟩
  · intro S U hS hUC hUc
    have hCc : (Sᶜ \ U).card = 3 := by
      rw [Finset.card_sdiff_of_subset hUC,Finset.card_compl,Fintype.card_fin,hS.1,hUc]
    simpa only [hUc,hCc,true_and] using (hf.facet_six_properties hS.1 hS.2).1 U hUC hUc
  · intro S P hS hPC hPc
    trans ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card
    · apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro support_mem
        exact ⟨support_mem.1, support_mem.2.2⟩
      · intro support_mem
        refine ⟨support_mem.1, ⟨?_, support_mem.2⟩⟩
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp support_mem.1).2, hPc]
    · exact (hf.facet_six_properties hS.1 hS.2).2 P hPC hPc

theorem no_admissible_ten : ¬ ∃ f : Vector4 → Fin 10 → ℝ, Admissible f := by
  rintro ⟨f,hf⟩
  have hempty : SupportFace f ∅ := ⟨EuclideanSpace.single 0 1,by simp,Finset.empty_subset _⟩
  obtain ⟨S,hSc,hSf,_⟩ := hf.face_extends_four hempty
  exact FiniteObstruction.no_ten_system hf.support_ten_system ⟨S,hSc,hSf⟩

theorem main_theorem :
    IsCompact projectorSet ∧
    projectorSet ⊆ traceOneSymmetric ∧
    Metric.diam projectorSet = Real.sqrt 2 ∧
    ¬ HasTenSmallCover := by
  refine ⟨isCompact_projectorSet,projectorSet_subset_traceOneSymmetric,diam_projectorSet,?_⟩
  intro h
  exact no_admissible_ten (cover_to_admissible h)

end BorsukNine

end OAI
