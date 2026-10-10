import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphApproximateNeighborhoods

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
structure Geometry (X : Type*) where
  graph : SimpleGraph X
  connected : graph.Connected
  locallyFinite : ∀ x, (graph.neighborSet x).Finite
  transitive : ∀ x y, ∃ g : graph ≃g graph, g x=y
  root : X

namespace Geometry
variable {X : Type*} (W : Geometry X)
abbrev Aut := W.graph ≃g W.graph

def around (x : X) (r : ℕ) : Finset X := (GraphTopology.reachBall_finite W.graph W.locallyFinite x r).toFinset
abbrev ball (r : ℕ) := W.around W.root r

@[simp] lemma mem_around {x y : X} {r : ℕ} :
    y∈W.around x r ↔ y∈GraphTopology.reachBall W.graph x r := (GraphTopology.reachBall_finite W.graph W.locallyFinite x r).mem_toFinset

lemma around_mono (x : X) : Monotone (W.around x) := by
  intro r s h y hy
  exact W.mem_around.mpr (GraphTopology.reachBall_mono W.graph x h (W.mem_around.mp hy))
lemma ball_mono : Monotone W.ball := W.around_mono W.root

lemma self_mem_around (x : X) (r : ℕ) : x∈W.around x r :=
  W.mem_around.mpr (GraphTopology.reachBall_self W.graph x r)
lemma mem_around_symm {x y : X} {r : ℕ} (h : y∈W.around x r) : x∈W.around y r :=
  W.mem_around.mpr (GraphTopology.reachBall_symm W.graph (W.mem_around.mp h))
lemma mem_around_add {x y z : X} {r s : ℕ} (hy : y∈W.around x r) (hz : z∈W.around y s) :
    z∈W.around x (r+s) :=
  W.mem_around.mpr (GraphTopology.reachBall_add W.graph (W.mem_around.mp hy) (W.mem_around.mp hz))
lemma around_subset_ball {x : X} {R r : ℕ} (hx : x∈W.ball R) : W.around x r⊆W.ball (R+r) :=
  fun _ hy => W.mem_around_add hx hy
lemma ball_card_pos (r : ℕ) : 0<(W.ball r).card :=
  Finset.card_pos.mpr ⟨W.root,W.self_mem_around W.root r⟩

lemma aut_around_image (g : W.Aut) (x : X) (r : ℕ) :
    (W.around x r).image g=W.around (g x) r := by
  ext y
  constructor
  · intro hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact W.mem_around.mpr (GraphTopology.iso_reachBall W.graph g (W.mem_around.mp hz))
  · intro hy
    refine Finset.mem_image.mpr ⟨g.symm y,?_,g.apply_symm_apply y⟩
    apply W.mem_around.mpr
    simpa using GraphTopology.iso_reachBall W.graph g.symm (W.mem_around.mp hy)

lemma card_around (x : X) (r : ℕ) : (W.around x r).card=(W.ball r).card := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.aut_around_image]
  exact Finset.card_image_of_injective _ g.injective

lemma exists_mem_ball (x : X) : ∃ n, x∈W.ball n := by
  obtain ⟨p,hp,he⟩ := W.connected.exists_path_of_dist W.root x
  exact ⟨p.length,W.mem_around.mpr ⟨p,le_rfl⟩⟩

def length (x : X) : ℕ := W.graph.dist W.root x
lemma mem_ball_length (x : X) : x∈W.ball (W.length x) := by
  obtain ⟨p,_,hp⟩ := W.connected.exists_path_of_dist W.root x
  exact W.mem_around.mpr ⟨p,hp.le⟩
lemma length_le_iff {x : X} {n : ℕ} : W.length x≤n ↔ x∈W.ball n := by
  constructor
  · intro h; exact W.ball_mono h (W.mem_ball_length x)
  · intro h
    obtain ⟨p,hp⟩ := W.mem_around.mp h
    exact (SimpleGraph.dist_le p).trans hp
lemma length_root : W.length W.root=0 := SimpleGraph.dist_self
lemma length_adj {x y : X} (h : W.graph.Adj x y) :
    W.length x≤W.length y+1 ∧ W.length y≤W.length x+1 := by
  have h1 := W.connected.dist_triangle (u:=W.root) (v:=x) (w:=y)
  have h2 := W.connected.dist_triangle (u:=W.root) (v:=y) (w:=x)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at h1
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at h2
  exact ⟨h2,h1⟩

lemma aut_length_le (g : W.Aut) (x : X) : W.length (g x)≤W.length (g W.root)+W.length x := by
  apply W.length_le_iff.mpr
  apply W.mem_around_add (W.mem_ball_length (g W.root))
  rw [←W.aut_around_image]
  exact Finset.mem_image.mpr ⟨x,W.mem_ball_length x,rfl⟩

def neighbors (x : X) : Finset X := (W.locallyFinite x).toFinset
@[simp] lemma mem_neighbors {x y : X} : y∈W.neighbors x ↔ W.graph.Adj x y := (W.locallyFinite x).mem_toFinset
lemma neighbors_image (g : W.Aut) (x : X) : (W.neighbors x).image g=W.neighbors (g x) := by
  ext y
  simp only [Finset.mem_image,W.mem_neighbors]
  constructor
  · rintro ⟨z,hz,rfl⟩; exact g.map_adj_iff.mpr hz
  · intro h; exact ⟨g.symm y,by simpa using g.symm.map_adj_iff.mpr h,g.apply_symm_apply y⟩
lemma neighbors_card (x : X) : (W.neighbors x).card=(W.neighbors W.root).card := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.neighbors_image]
  exact Finset.card_image_of_injective _ g.injective
abbrev degree := (W.neighbors W.root).card

def energy (F : Finset X) (u : X → ℝ) := ∑ x∈F, ∑ y∈W.neighbors x, (u y-u x)^2
lemma energy_nonneg (F : Finset X) (u : X → ℝ) : 0≤W.energy F u := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
lemma energy_mono {F H : Finset X} (h : F⊆H) (u : X → ℝ) : W.energy F u≤W.energy H u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intros; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def IsHarmonic (u : X → ℝ) : Prop := ∀ x, (∑ y∈W.neighbors x, (u x-u y))=0

def cutoff (R : ℕ) (x : X) : ℝ := max 0 (2*(R:ℝ)-(W.length x:ℝ))
lemma cutoff_nonneg (R : ℕ) (x : X) : 0≤W.cutoff R x := le_max_left _ _
lemma cutoff_large (R : ℕ) {x : X} (hx : x∈W.ball R) : (R:ℝ)≤W.cutoff R x := by
  have hl : (W.length x:ℝ)≤R := by exact_mod_cast W.length_le_iff.mpr hx
  exact (by linarith : (R:ℝ)≤2*R-W.length x).trans (le_max_right _ _)
lemma cutoff_eq_zero (R : ℕ) {x : X} (hx : 2*R≤W.length x) : W.cutoff R x=0 := by
  have hl : 2*(R:ℝ)≤W.length x := by exact_mod_cast hx
  exact max_eq_left (by linarith)
lemma cutoff_ne_zero_length (R : ℕ) {x : X} (hx : W.cutoff R x≠0) : W.length x<2*R := by
  by_contra! h; exact hx (W.cutoff_eq_zero R h)
lemma cutoff_lipschitz (R : ℕ) {x y : X} (h : W.graph.Adj x y) :
    |W.cutoff R y-W.cutoff R x|≤1 := by
  obtain ⟨h1,h2⟩ := W.length_adj h
  have h1' : (W.length x:ℝ)≤(W.length y:ℝ)+1 := by exact_mod_cast h1
  have h2' : (W.length y:ℝ)≤(W.length x:ℝ)+1 := by exact_mod_cast h2
  unfold cutoff
  rw [abs_le]
  constructor <;> rcases le_total 0 (2*(R:ℝ)-W.length y) with hx|hx <;>
    rcases le_total 0 (2*(R:ℝ)-W.length x) with hy|hy <;>
    simp only [max_eq_right hx,max_eq_left hx,max_eq_right hy,max_eq_left hy] <;> linarith

end Geometry
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
