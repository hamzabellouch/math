import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceBoundaryCollar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

namespace OAI

noncomputable section
namespace ClosedSurfaceR4

lemma finite_positive_lower {ι : Type*} [Finite ι] {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i by
    obtain ⟨δ,hδ,h⟩ := this Finset.univ
    exact ⟨δ,hδ,fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ,hδ,h⟩ := ih
    refine ⟨min (f i) δ,lt_min (hf i) hδ,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (h j hj)

lemma finite_positive_upper {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ i, f i ≤ H := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ H : ℝ, 0 < H ∧ ∀ i ∈ s, f i ≤ H by
    obtain ⟨H,hH,h⟩ := this Finset.univ
    exact ⟨H,hH,fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨H,hH,h⟩ := ih
    refine ⟨max (f i) H,hH.trans_le (le_max_right _ _),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_max_left _ _
    · exact (h j hj).trans (le_max_right _ _)

end ClosedSurfaceR4

end

end OAI
