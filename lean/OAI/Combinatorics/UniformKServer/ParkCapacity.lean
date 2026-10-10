import Mathlib
import OAI.Combinatorics.UniformKServer.RoundingChain

namespace OAI

                                   
section

/-! Shared subtree capacity for parks at many depths. The geometry enters only
through nested regions, same-depth disjointness, and actual validity witnesses. -/
noncomputable section
namespace UniformKServer.ParkCapacity
open Finset TreeRounding TreeParking TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem grouped (a : Allocation S k) (T : Finset (Vertex n)) (j : ℕ)
    (hj : ∀ v ∈ T, j ≤ depth S v) :
    (∑ v ∈ T, park S a.amount v) ≤ ∑ u ∈ T.image (ancestor S j), a.amount u := by
  rw [←sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem (ancestor S j) hv)
    (fun v => park S a.amount v)]
  apply sum_le_sum
  intro u _
  rw [←subtree_total a u]
  apply sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨hv,he⟩ := mem_filter.mp hv
    simp only [subtree,mem_filter,mem_univ,true_and]
    rw [←he]
    exact (ancestor_spec j v (hj v hv)).2
  · intro v _ _
    exact a.park_nonneg v

variable {X : Type*} [Fintype X] [MetricSpace X]

structure Geometry (S : Shape n) (X : Type*) [MetricSpace X] where
  region : Vertex n → Finset X
  nested : ∀ u v, descends S u v → region v ⊆ region u
  disjoint : ∀ u v, depth S u=depth S v → u ≠ v → Disjoint (region u) (region v)
  radius : ℕ → ℝ
  nonneg : ∀ j, 0 ≤ radius j
  antitone : Antitone radius
  diameter : ∀ v, ∀ x ∈ region v, ∀ z ∈ region v, dist x z ≤ 40*radius (depth S v)

def ball (y : X) (r : ℝ) : Finset X := univ.filter (fun z => dist y z ≤ r)
def mass (μ : X → ℝ) (A : Finset X) : ℝ := ∑ z ∈ A, μ z

theorem ancestor_region (G : Geometry S X) (j : ℕ) (y : X) (v : Vertex n)
    (hj : j ≤ depth S v) (z : X) (hz : z ∈ G.region v)
    (hzy : dist y z ≤ 27*G.radius (depth S v)) :
    G.region (ancestor S j v) ⊆ ball y (67*G.radius j) := by
  have ha := ancestor_spec j v hj
  have hza := G.nested _ _ ha.2 hz
  have hr := G.antitone hj
  intro x hx
  have hd := G.diameter (ancestor S j v) z hza x hx
  rw [ha.1] at hd
  simp only [ball,mem_filter,mem_univ,true_and]
  have ht := dist_triangle y z x
  nlinarith

omit [Fintype X] in
theorem disjoint_mass (μ : X → ℝ) (hμ : ∀ z, 0 ≤ μ z)
    (G : Geometry S X) (U : Finset (Vertex n)) (j : ℕ) (B : Finset X)
    (hj : ∀ u ∈ U, depth S u=j) (hsub : ∀ u ∈ U, G.region u ⊆ B) :
    (∑ u ∈ U, mass μ (G.region u)) ≤ mass μ B := by
  have hd : (U : Set (Vertex n)).PairwiseDisjoint G.region := by
    intro u hu v hv hne
    exact G.disjoint u v ((hj u hu).trans (hj v hv).symm) hne
  have he : (∑ u ∈ U, mass μ (G.region u))=mass μ (U.biUnion G.region) := by
    unfold mass
    exact (sum_biUnion hd).symm
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg
  · intro z hz
    obtain ⟨u,hu,hz⟩ := mem_biUnion.mp hz
    exact hsub u hu hz
  · intro z _ _
    exact hμ z

theorem cumulative (a : Allocation S k) (G : Geometry S X) (μ : X → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ v, a.amount v ≤ C*mass μ (G.region v))
    (T : Finset (Vertex n)) (j : ℕ) (y : X)
    (hj : ∀ v ∈ T, j ≤ depth S v)
    (hw : ∀ v ∈ T, ∃ z ∈ G.region v, dist y z ≤ 27*G.radius (depth S v)) :
    (∑ v ∈ T, park S a.amount v) ≤ C*mass μ (ball y (67*G.radius j)) := by
  have hdepth : ∀ u ∈ T.image (ancestor S j), depth S u=j := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
    exact (ancestor_spec j v (hj v hv)).1
  have hsub : ∀ u ∈ T.image (ancestor S j), G.region u ⊆ ball y (67*G.radius j) := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
    obtain ⟨z,hz,hd⟩ := hw v hv
    exact ancestor_region G j y v (hj v hv) z hz hd
  calc
    _ ≤ ∑ u ∈ T.image (ancestor S j), a.amount u := grouped a T j hj
    _ ≤ ∑ u ∈ T.image (ancestor S j), C*mass μ (G.region u) := sum_le_sum fun u _ => hdom u
    _ = C*(∑ u ∈ T.image (ancestor S j), mass μ (G.region u)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (disjoint_mass μ hμ G _ j _ hdepth hsub) hC

end UniformKServer.ParkCapacity

end


end

end OAI
