import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeGraph
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BitWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

def Directed (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) (u v : ℤ) : Prop :=
  ∃ e ∈ E, u = w.offset e.castSucc ∧ v = w.offset e.succ

lemma min_origin_not_destination (w : ClosedLine h ℓ) {E : Finset (Fin ℓ)}
    (hE : E ⊆ w.treeSteps) (hne : E.Nonempty) :
    w.offset (E.min' hne).castSucc ∉ E.image (fun e => w.offset e.succ) := by
  rintro hv
  obtain ⟨e,he,hev⟩ := mem_image.mp hv
  have hnew := (mem_filter.mp (hE he)).2
  exact hnew (E.min' hne).castSucc (min'_le E e he) hev.symm

lemma incoming_earlier (w : ClosedLine h ℓ) {j e : Fin ℓ}
    (hj : j ∈ w.treeSteps) (hv : w.offset j.succ = w.offset e.castSucc) : j < e := by
  by_contra hn
  have he : e.val ≤ j.val := by exact le_of_not_gt hn
  exact (mem_filter.mp hj).2 e.castSucc he hv.symm

lemma directed_reach_adj (w : ClosedLine h ℓ) (hh : 0 < h) {E : Finset (Fin ℓ)}
    (hE : E ⊆ w.treeSteps) {t u v : ℤ}
    (ht : t ∉ E.image (fun e => w.offset e.succ))
    (hu : Relation.ReflTransGen (Directed w E) t u)
    (huv : (edgeGraph w hh E).Adj u v) :
    Relation.ReflTransGen (Directed w E) t v := by
  obtain ⟨e,he,huv | huv⟩ := huv
  · exact hu.tail ⟨e,he,huv⟩
  · rcases hu.cases_tail with hut | ⟨z,hz,⟨j,hj,hzu,hju⟩⟩
    · exact False.elim (ht (mem_image.mpr ⟨e,he,huv.2.symm.trans hut⟩))
    · have hje : j=e := tree_destination_injective w (hE hj) (hE he)
        (hju.symm.trans huv.2)
      subst j
      rw [hzu,← huv.1] at hz
      exact hz

lemma reachable_directed (w : ClosedLine h ℓ) (hh : 0 < h) {E : Finset (Fin ℓ)}
    (hE : E ⊆ w.treeSteps) {t v : ℤ}
    (ht : t ∉ E.image (fun e => w.offset e.succ))
    (hv : (edgeGraph w hh E).Reachable t v) :
    Relation.ReflTransGen (Directed w E) t v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact .refl
  | tail huv hadj ih => exact directed_reach_adj w hh hE ht ih hadj

lemma component_adj (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (c : (edgeGraph w hh E).ConnectedComponent) {u v : ℤ}
    (hu : (edgeGraph w hh E).connectedComponentMk u = c)
    (ha : (edgeGraph w hh E).Adj u v) :
    (edgeGraph w hh (componentEdges w hh E c)).Adj u v := by
  obtain ⟨e,he,huv | huv⟩ := ha
  · exact ⟨e,mem_filter.mpr ⟨he,by rwa [huv.1] at hu⟩,Or.inl huv⟩
  · have hec : (edgeGraph w hh E).connectedComponentMk (w.offset e.castSucc) = c := by
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (edgeGraph_adj w hh E e he)).trans (by rwa [← huv.2])
    exact ⟨e,mem_filter.mpr ⟨he,hec⟩,Or.inr huv⟩

lemma reachable_component (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (c : (edgeGraph w hh E).ConnectedComponent) {t v : ℤ}
    (ht : (edgeGraph w hh E).connectedComponentMk t = c)
    (hv : (edgeGraph w hh E).Reachable t v) :
    (edgeGraph w hh (componentEdges w hh E c)).Reachable t v := by
  have hrt := (SimpleGraph.reachable_iff_reflTransGen t v).mp hv
  clear hv
  apply (SimpleGraph.reachable_iff_reflTransGen t v).mpr
  induction hrt with
  | refl => exact .refl
  | @tail u v htu huv ih =>
    have hu : (edgeGraph w hh E).connectedComponentMk u = c :=
      (SimpleGraph.ConnectedComponent.eq.mpr
        ((SimpleGraph.reachable_iff_reflTransGen t u).mpr htu)).symm.trans ht
    exact ih.tail (component_adj w hh E c hu huv)

theorem component_grows (w : ClosedLine h ℓ) (hh : 0 < h) {E : Finset (Fin ℓ)}
    (hE : E ⊆ w.treeSteps) (c : (edgeGraph w hh E).ConnectedComponent)
    (hc : c ∈ edgeComponents w hh E) :
    Grows w (w.offset ((componentEdges w hh E c).min'
      (componentEdges_nonempty w hh E c hc)).castSucc) (componentEdges w hh E c) := by
  let F := componentEdges w hh E c
  have hF : F ⊆ w.treeSteps := (componentEdges_subset w hh E c).trans hE
  have hne : F.Nonempty := componentEdges_nonempty w hh E c hc
  let t := w.offset (F.min' hne).castSucc
  have ht : (edgeGraph w hh E).connectedComponentMk t = c :=
    (mem_filter.mp (min'_mem F hne)).2
  have hnodest : t ∉ F.image (fun e => w.offset e.succ) := min_origin_not_destination w hF hne
  refine ⟨hF,?_⟩
  intro e he
  have hec : (edgeGraph w hh E).connectedComponentMk (w.offset e.castSucc) = c :=
    (mem_filter.mp he).2
  have hre : (edgeGraph w hh E).Reachable t (w.offset e.castSucc) :=
    SimpleGraph.ConnectedComponent.eq.mp (ht.trans hec.symm)
  have hr := reachable_directed w hh hF hnodest (reachable_component w hh E c ht hre)
  rcases hr.cases_tail with het | ⟨z,hz,⟨j,hj,hjz,hje⟩⟩
  · exact Or.inl het
  · exact Or.inr ⟨j,hj,incoming_earlier w (hF hj) hje.symm,hje.symm⟩

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
