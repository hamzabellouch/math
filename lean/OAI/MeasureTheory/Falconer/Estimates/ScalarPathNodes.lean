import OAI.MeasureTheory.Falconer.Estimates.ScalarSelectedForks
import Mathlib.Data.Set.Function

namespace OAI

/-! Translating actual scalar prefix nodes into their distinct centers.
 This is the coordinate bridge to the separated-tree projection estimate. -/
namespace Falconer.Regularization

noncomputable def scalarPrefixPath (Q : Finset (CellPath 1)) (d : ℕ) (x : ℝ) : CellPath 1 :=
  Function.invFunOn scalarPathCenter (Q.image (List.take d) : Set (CellPath 1)) x

noncomputable def scalarPrefixPoints (Q : Finset (CellPath 1)) (d : ℕ) (x : ℝ) : Finset ℝ :=
  (prefixFiber Q d (scalarPrefixPath Q d x)).image scalarPathCenter

noncomputable def scalarPrefixChildren (Q : Finset (CellPath 1)) (a b : ℕ) (x : ℝ) : Finset ℝ :=
  (prefixChildren Q a b (scalarPrefixPath Q a x)).image scalarPathCenter

 theorem scalar_prefix_path_mem {Q : Finset (CellPath 1)} {d : ℕ} {x : ℝ}
    (hx : x ∈ (Q.image (List.take d)).image scalarPathCenter) :
    scalarPrefixPath Q d x ∈ Q.image (List.take d) := by
  obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp hx
  exact Function.invFunOn_mem ⟨p,hp,heq⟩

 theorem scalar_prefix_path_center {Q : Finset (CellPath 1)} {d : ℕ} {x : ℝ}
    (hx : x ∈ (Q.image (List.take d)).image scalarPathCenter) :
    scalarPathCenter (scalarPrefixPath Q d x) = x := by
  obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp hx
  exact Function.invFunOn_eq ⟨p,hp,heq⟩

 theorem scalar_prefix_path_eq {N d : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (hd : d ≤ N) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take d)) : scalarPrefixPath Q d (scalarPathCenter p) = p := by
  have hlen : ∀ q ∈ Q.image (List.take d), q.length = d := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    have hrN := (mem_cubePaths 1 N r).mp (hQ hr)
    simp only [List.length_take,hrN,min_eq_left hd]
  exact (scalarPathCenter_injOn _ hlen).leftInvOn_invFunOn hp

 theorem scalar_prefix_points_eq {N d : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (hd : d ≤ N) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take d)) :
    scalarPrefixPoints Q d (scalarPathCenter p) = (prefixFiber Q d p).image scalarPathCenter := by
  unfold scalarPrefixPoints
  rw [scalar_prefix_path_eq hQ hd hp]

 theorem scalar_prefix_children_eq {N a b : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (ha : a ≤ N) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take a)) :
    scalarPrefixChildren Q a b (scalarPathCenter p) = (prefixChildren Q a b p).image scalarPathCenter := by
  unfold scalarPrefixChildren
  rw [scalar_prefix_path_eq hQ ha hp]

 theorem prefixFiber_children_union (Q : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (p : CellPath 1) :
    prefixFiber Q a p = (prefixChildren Q a b p).biUnion (prefixFiber Q b) := by
  classical
  ext q
  constructor
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨q.take b,Finset.mem_image_of_mem _ hq,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,rfl⟩⟩
  · intro hq
    obtain ⟨c,hc,hq⟩ := Finset.mem_biUnion.mp hq
    exact prefixFiber_child_subset hab hc hq

 theorem scalar_prefix_points_children {N a b : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N)
    (x : ℝ) :
    scalarPrefixPoints Q a x =
      (scalarPrefixChildren Q a b x).biUnion (scalarPrefixPoints Q b) := by
  classical
  let p := scalarPrefixPath Q a x
  ext y
  constructor
  · intro hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    have hc : u.take b ∈ prefixChildren Q a b p := Finset.mem_image_of_mem _ hu
    have hcm := prefixChildren_mem_image hc
    apply Finset.mem_biUnion.mpr
    refine ⟨scalarPathCenter (u.take b),Finset.mem_image_of_mem _ hc,?_⟩
    rw [scalar_prefix_points_eq hQ hb hcm]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,rfl⟩)
  · intro hy
    obtain ⟨z,hz,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    rw [scalar_prefix_points_eq hQ hb (prefixChildren_mem_image hc)] at hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem _ (prefixFiber_child_subset hab hc hu)

 theorem scalar_prefix_points_leaf {N : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) {x : ℝ}
    (hx : x ∈ (Q.image (List.take N)).image scalarPathCenter) :
    scalarPrefixPoints Q N x = {x} := by
  classical
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  rw [scalar_prefix_points_eq hQ le_rfl hp]
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 1 N u).mp (hQ hu)
  have he : u.take N = u := by rw [← hlen,List.take_length]
  rw [he,prefixFiber_leaf hQ hu]
  simp

 theorem ScalarBranchingLevel.separated {Q : Finset (CellPath 1)} {a b k n : ℕ}
    (h : ScalarBranchingLevel Q a b k n) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take a)) :
    ∀ q ∈ prefixChildren Q a b p, ∀ r ∈ prefixChildren Q a b p, q ≠ r →
      8*(1/2:ℝ)^n ≤ |scalarPathCenter q-scalarPathCenter r| := by
  intro q hq r hr hqr
  rcases h.fork_geometry p hp with hk | ⟨_,_,hs,_⟩
  · have hc : (prefixChildren Q a b p).card ≤ 1 := by rw [h.children_card p hp,hk]; simp
    exact False.elim (hqr (Finset.card_le_one.mp hc q hq r hr))
  · exact (hs q hq r hr hqr).le

end Falconer.Regularization

end OAI
