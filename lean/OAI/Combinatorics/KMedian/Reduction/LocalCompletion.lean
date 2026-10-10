import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost
import OAI.Combinatorics.KMedian.Reduction.CompletionGeometry

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance localCompletionPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

noncomputable def region (C : CloseCenters I G O δ) (t : ↥G) : Finset (Fin I.n) :=
  I.clients.filter (fun j => dist j t.val ≤ C.radius t/3)

noncomputable def matched (C : CloseCenters I G O δ) : Finset (Fin I.n) :=
  univ.image C.matchTo

noncomputable def backup (C : CloseCenters I G O δ) : Finset (Fin I.n) :=
  O \ C.matched

theorem matched_sub (C : CloseCenters I G O δ) : C.matched ⊆ O := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact C.match_mem t

theorem optimal_mem (C : CloseCenters I G O δ) {i : Fin I.n} (hi : i ∈ O) :
    i ∈ C.backup ∨ ∃ t, C.matchTo t=i := by
  by_cases hm : i ∈ C.matched
  · right
    obtain ⟨t,_,he⟩ := mem_image.mp hm
    exact ⟨t,he⟩
  · exact Or.inl (mem_sdiff.mpr ⟨hi,hm⟩)

theorem region_disjoint (C : CloseCenters I G O δ) {t u : ↥G} (htu : t ≠ u) :
    Disjoint (C.region t) (C.region u) := by
  apply disjoint_left.mpr
  intro j hjt hju
  exact htu (C.near_unique (mem_filter.mp hjt).2 (mem_filter.mp hju).2)

theorem region_reference (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (hO : O.Nonempty) (t : ↥G) {j : Fin I.n} (hj : j ∈ C.region t) :
    nearest I j (insert (C.matchTo t) C.backup) ≤ nearest I j O := by
  obtain ⟨i,hi,he⟩ := I.nearest_attained j O hO
  rw [he]
  obtain hb | ⟨u,rfl⟩ := C.optimal_mem hi
  · exact I.nearest_le j (mem_insert_of_mem hb)
  · exact (I.nearest_le j (mem_insert_self _ _)).trans
      (C.near_match_best hδ hsmall (mem_filter.mp hj).2)

theorem choose_local (C : CloseCenters I G O δ) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
    (t : ↥G) : ∃ a ∈ F, dist t.val a ≤ δ*C.radius t ∧
      (∑ j ∈ C.region t, nearest I j (insert a C.backup)) ≤
      ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup) := by
  classical
  let K := F.filter (fun a => dist t.val a ≤ δ*C.radius t)
  have hm : C.matchTo t ∈ K := mem_filter.mpr ⟨hOF (C.match_mem t),(C.close t).le⟩
  let v (a : Fin I.n) := ∑ j ∈ C.region t, rationalNearest I j (insert a C.backup)
  obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (K.image v) ((show K.Nonempty from ⟨_,hm⟩).image _))
  refine ⟨a,(mem_filter.mp ha).1,(mem_filter.mp ha).2,?_⟩
  have hmin : v a ≤ v (C.matchTo t) := by
    rw [he]
    exact min'_le _ _ (mem_image_of_mem v hm)
  have hcast : ∀ b, (v b:ℝ)=∑ j ∈ C.region t, nearest I j (insert b C.backup) := by
    intro b
    simp only [v,Rat.cast_sum,I.cast_rationalNearest]
  rw [← hcast a,← hcast (C.matchTo t)]
  exact_mod_cast hmin

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
