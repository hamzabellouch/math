import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def commonNeighbors {n : ℕ} (G : Graph n) (u v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => {u,w} ∈ G ∧ {v,w} ∈ G)

def currentCodegree {n : ℕ} (G : Graph n) (u v : Fin n) : ℕ :=
  (commonNeighbors G u v).card

def wedgeEdges {n : ℕ} (u v w : Fin n) : Graph n := {{u,w},{v,w}}

@[simp] theorem mem_commonNeighbors {n : ℕ} (G : Graph n) (u v w : Fin n) :
    w ∈ commonNeighbors G u v ↔ {u,w} ∈ G ∧ {v,w} ∈ G := by
  simp [commonNeighbors]

@[simp] theorem wedgeEdges_subset {n : ℕ} (G : Graph n) (u v w : Fin n) :
    wedgeEdges u v w ⊆ G ↔ w ∈ commonNeighbors G u v := by
  simp [wedgeEdges, Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem commonNeighbors_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (hw : w ∈ commonNeighbors G u v) : u ≠ w ∧ v ≠ w := by
  obtain ⟨hu,hv⟩ := (mem_commonNeighbors G u v w).mp hw
  constructor
  · intro h
    have hc := mem_completeGraph.mp (hG hu)
    simp [h] at hc
  · intro h
    have hc := mem_completeGraph.mp (hG hv)
    simp [h] at hc

theorem currentCodegree_copyCount {n : ℕ} (G : Graph n) (u v : Fin n) :
    (currentCodegree G u v : ℝ) = copyCount (wedgeEdges u v) G := by
  simp only [copyCount, intact, wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [currentCodegree, commonNeighbors]

theorem wedgeEdges_card {n : ℕ} {u v w : Fin n} (huv : u ≠ v)
    (huw : u ≠ w) : (wedgeEdges u v w).card = 2 := by
  have he : ({u,w} : Finset (Fin n)) ≠ {v,w} := by
    intro heq
    have hu : u ∈ ({v,w} : Finset (Fin n)) := heq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    exact hu.elim huv huw
  simp [wedgeEdges, he]

theorem step_mean_codegree_hazard {n : ℕ} (G : Graph n) (u v : Fin n)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)) =
      (currentCodegree G u v : ℝ) -
      (∑ w ∈ commonNeighbors G u v,
        ((hittingTriangles G (wedgeEdges u v w)).card : ℝ)) / (triangles G).card := by
  simp_rw [currentCodegree_copyCount]
  rw [step_mean_copyCount _ G hG]
  congr 2
  simp only [wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [commonNeighbors]

theorem hittingTriangles_wedge {n : ℕ} (G : Graph n) (u v w : Fin n) :
    hittingTriangles G (wedgeEdges u v w) =
      incidentTriangles G {u,w} ∪ incidentTriangles G {v,w} := by
  rw [hittingTriangles_eq_biUnion]
  simp [wedgeEdges]

theorem wedge_incident_inter {n : ℕ} (G : Graph n) {u v w : Fin n}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    incidentTriangles G {u,w} ∩ incidentTriangles G {v,w} =
      if {u,v,w} ∈ triangles G then {{u,v,w}} else ∅ := by
  ext t
  simp only [Finset.mem_inter, incidentTriangles, Finset.mem_filter]
  have hpairu : ({u,w} : Finset (Fin n)).card = 2 := Finset.card_pair huw
  have hpairv : ({v,w} : Finset (Fin n)).card = 2 := Finset.card_pair hvw
  have htriple : ({u,v,w} : Finset (Fin n)).card = 3 := by simp [huv,huw,hvw]
  have hpt : ({u,w} : Finset (Fin n)) ⊆ {u,v,w} := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  have hqt : ({v,w} : Finset (Fin n)) ⊆ {u,v,w} := by
    simp
  have hpq : ({u,w} : Finset (Fin n)) ≠ {v,w} := by
    intro he
    have hh : u ∈ ({v,w} : Finset (Fin n)) := he ▸ (by simp)
    simp [huv,huw] at hh
  constructor
  · rintro ⟨⟨ht,he⟩,_,hf⟩
    have heq := triangle_eq_of_two_edges (mem_triangles.mp ht).1 htriple
      hpairu hpairv hpq (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp hf).1 hpt hqt
    subst t
    simp [ht]
  · intro hh
    split_ifs at hh with ht
    · have heq : t = {u,v,w} := Finset.mem_singleton.mp hh
      subst t
      exact ⟨⟨ht,Finset.mem_powersetCard.mpr ⟨hpt,hpairu⟩⟩,
        ht,Finset.mem_powersetCard.mpr ⟨hqt,hpairv⟩⟩
    · exact False.elim (Finset.notMem_empty t hh)

theorem wedge_hazard_exact {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    ((hittingTriangles G (wedgeEdges u v w)).card : ℝ) =
      (triangleDegree G {u,w} : ℝ) + (triangleDegree G {v,w} : ℝ) -
        if {u,v,w} ∈ triangles G then 1 else 0 := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  have hh := Finset.card_union_add_card_inter
    (incidentTriangles G {u,w}) (incidentTriangles G {v,w})
  rw [wedge_incident_inter G huv huw hvw] at hh
  rw [hittingTriangles_wedge]
  unfold triangleDegree
  split_ifs at hh ⊢ with ht <;> simp only [Finset.card_singleton, Finset.card_empty] at hh
  all_goals
    have hh' : ((incidentTriangles G {u,w} ∪ incidentTriangles G {v,w}).card : ℝ) +
        (if {u,v,w} ∈ triangles G then 1 else 0) =
        (incidentTriangles G {u,w}).card + (incidentTriangles G {v,w}).card := by
      simp only [ht, ↓reduceIte]
      exact_mod_cast hh
    simp only [ht, ↓reduceIte] at hh'
    linarith

end SharpTerminalLeave

end
end

end OAI
