import OAI.MeasureTheory.Falconer.Estimates.EndpointCoarsening
import OAI.MeasureTheory.Falconer.Estimates.ChildRetention

namespace OAI

/-! Lift a retained set of endpoint cells to its actual original leaves.
The cost is measured inside the active parent and uses the existing block
fiber bounds, rather than the cardinality of the whole configuration. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quarter_endpoint_subset_paths {N a b : ℕ}
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (P : Finset (Space 2)) (hP : P ⊆ quarterEndpointSet Q C a b p₀) :
    ∃ D ⊆ prefixChildren C a b p₀,
      D.image (quarterEndpointPoint Q a p₀) = P ∧ D.card = P.card := by
  let F := quarterEndpointPoint Q a p₀
  let D := (prefixChildren C a b p₀).filter (fun r => F r ∈ P)
  have hD : D ⊆ prefixChildren C a b p₀ := Finset.filter_subset _ _
  have he : D.image F = P := by
    ext x
    constructor
    · intro hx
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hr).2
    · intro hx
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp (hP hx)
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr,hx⟩)
  have hinj : Set.InjOn F (D:Set (CellPath 2)) := by
    apply (quarterEndpointPoint_injOn Q hQ a p₀).mono
    intro r hr
    exact planar_prefix_image_take_cubePaths hC hbN (prefixChildren_mem_image (hD hr))
  refine ⟨D,hD,he,?_⟩
  rw [← he,Finset.card_image_iff.mpr hinj]

theorem blockClass_lift_endpoint_selection {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (p₀ : CellPath 2)
    (D : Finset (CellPath 2))
    (hD : D ⊆ prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀)
    (hDne : D.Nonempty) {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(D.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let E := (prefixFiber C (blockDepth N B i) p₀).filter
      (fun r => r.take (blockDepth N B j) ∈ D)
    E ⊆ prefixFiber C (blockDepth N B i) p₀ ∧ E.Nonempty ∧
      ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
        (H*(2:ℝ)^j)*(E.card:ℝ) ∧ E.image (List.take (blockDepth N B j)) = D := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let A := prefixFiber C (blockDepth N B i) p₀
  let E := A.filter (fun r => r.take (blockDepth N B j) ∈ D)
  let u : ℝ := blockProduct L (blockLabel L N B f K) N B j p
  have hu : 0 < u := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hfiber (q : CellPath 2) (hq : q ∈ D) :
      A.filter (fun r => r.take (blockDepth N B j) = q) =
        prefixFiber C (blockDepth N B j) q :=
    prefixFiber_parent_filter (blockDepth_antitone N B hji) (hD hq)
  have hcount : (E.card:ℝ) = ∑ q ∈ D, ((prefixFiber C (blockDepth N B j) q).card:ℝ) := by
    have he := Finset.sum_card_fiberwise_eq_card_filter A D (List.take (blockDepth N B j))
    rw [show A.filter (fun x => x.take (blockDepth N B j) ∈ D) = E from rfl] at he
    rw [← he]
    push_cast
    apply Finset.sum_congr rfl
    intro q hq
    rw [hfiber q hq]
  have hbounds (q : CellPath 2) (hq : q ∈ prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀) :
      u ≤ ((prefixFiber C (blockDepth N B j) q).card:ℝ) ∧
        ((prefixFiber C (blockDepth N B j) q).card:ℝ) ≤ (2:ℝ)^j*u := by
    dsimp only [C,u]
    exact_mod_cast blockClass_leaf_count hL B f K p (hji.trans hi) (prefixChildren_mem_image hq)
  have hElow : (D.card:ℝ)*u ≤ (E.card:ℝ) := by
    rw [hcount]
    calc
      _ = ∑ _q ∈ D, u := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hbounds q (hD hq)).1
  have hE : E.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos (Nat.cast_pos.mpr hDne.card_pos) hu).trans_le hElow))
  have hupper := (prefix_children_mass_bounds C (blockDepth_antitone N B hji) p₀ hbounds).2
  refine ⟨Finset.filter_subset _ _,hE,?_,?_⟩
  · calc
      _ ≤ ((prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ)*((2:ℝ)^j*u) := hupper
      _ ≤ (H*(D.card:ℝ))*((2:ℝ)^j*u) := mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = (H*(2:ℝ)^j)*((D.card:ℝ)*u) := by ring
      _ ≤ (H*(2:ℝ)^j)*(E.card:ℝ) := mul_le_mul_of_nonneg_left hElow (by positivity)
  · ext q
    constructor
    · intro hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
      exact (Finset.mem_filter.mp hr).2
    · intro hq
      obtain ⟨r,hr,he⟩ := Finset.mem_image.mp (hD hq)
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,by rwa [he]⟩,he⟩

end Falconer

end OAI
