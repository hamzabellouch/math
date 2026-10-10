import OAI.MeasureTheory.Falconer.Estimates.QuarterEndpointMap

namespace OAI

/-! Coarsen actual endpoint centers by their original dyadic prefixes.
The point fibers are exact, not geometric enlargements. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_prefixChildren_filter (C : Finset (CellPath 2)) {a c b : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) {p₀ r : CellPath 2}
    (hr : r ∈ prefixChildren C a c p₀) :
    (prefixChildren C a b p₀).filter (fun u => u.take c = r) = prefixChildren C c b r := by
  change prefixFiber ((prefixFiber C a p₀).image (List.take b)) c r = _
  rw [planar_prefixFiber_image_take _ hcb]
  have he : prefixFiber (prefixFiber C a p₀) c r = prefixFiber C c r :=
    prefixFiber_parent_filter hac hr
  rw [he]
  rfl

theorem exists_quarterEndpoint_prefix_map {N a b c : ℕ}
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2) :
    ∃ q : Space 2 → Space 2, ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c) := by
  let D := prefixChildren C a b p₀
  let F := quarterEndpointPoint Q a p₀
  let P := D.image F
  have hD : D ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  let pick := fun x : Space 2 => if hx : x ∈ P then (Finset.mem_image.mp hx).choose else []
  have hpick (x : Space 2) (hx : x ∈ P) : pick x ∈ D ∧ F (pick x) = x := by
    simpa only [pick,dite_eq_left hx] using (Finset.mem_image.mp hx).choose_spec
  refine ⟨fun x => F ((pick x).take c),?_⟩
  intro r hr
  have hx : F r ∈ P := Finset.mem_image_of_mem _ hr
  have he : pick (F r) = r := quarterEndpointPoint_injOn Q hQ a p₀
    (hD (hpick _ hx).1) (hD hr) (hpick _ hx).2
  change F ((pick (F r)).take c) = F (r.take c)
  rw [he]

theorem quarterEndpoint_prefix_image {a b c : ℕ} (hcb : c ≤ b)
    (Q : DyadicCube 2) (C : Finset (CellPath 2)) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c)) :
    (quarterEndpointSet Q C a b p₀).image q = quarterEndpointSet Q C a c p₀ := by
  unfold quarterEndpointSet
  rw [Finset.image_image]
  calc
    _ = (prefixChildren C a b p₀).image
        (fun r => quarterEndpointPoint Q a p₀ (r.take c)) := Finset.image_congr hq
    _ = _ := by
      simp only [prefixChildren,Finset.image_image,Function.comp_def,List.take_take,
        Nat.min_eq_left hcb]

theorem quarterEndpoint_prefix_fiber {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c))
    {r : CellPath 2} (hr : r ∈ prefixChildren C a c p₀) :
    (quarterEndpointSet Q C a b p₀).filter (fun x => q x = quarterEndpointPoint Q a p₀ r) =
      (prefixChildren C c b r).image (quarterEndpointPoint Q a p₀) := by
  have hD : prefixChildren C a b p₀ ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  have hrC : r ∈ cubePaths 2 c :=
    planar_prefix_image_take_cubePaths hC (hcb.trans hbN) (prefixChildren_mem_image hr)
  unfold quarterEndpointSet
  rw [Finset.filter_image]
  have hf : (prefixChildren C a b p₀).filter
      (fun u => q (quarterEndpointPoint Q a p₀ u) = quarterEndpointPoint Q a p₀ r) =
      (prefixChildren C a b p₀).filter (fun u => u.take c = r) := by
    apply Finset.filter_congr
    intro u hu
    rw [hq u hu]
    constructor
    · intro he
      have huc : u.take c ∈ cubePaths 2 c := by
        rw [mem_cubePaths,List.length_take,(mem_cubePaths _ _ _).mp (hD hu),Nat.min_eq_left hcb]
      exact quarterEndpointPoint_injOn Q hQ a p₀ huc hrC he
    · intro he
      rw [he]
  rw [hf,planar_prefixChildren_filter C hac hcb hr]

theorem quarterEndpoint_prefix_local_fiber {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c))
    {r : CellPath 2} (hr : r ∈ prefixChildren C a c p₀) :
    ((quarterEndpointSet Q C a b p₀).filter
      (fun x => q x = quarterEndpointPoint Q a p₀ r)).image
        (localPacketPoint (4*(1/(2:ℝ)^(c-a+2)))
          (quarterEndpointPoint Q a p₀ r 0) (quarterEndpointPoint Q a p₀ r 1)) =
      quarterEndpointSet Q C c b r := by
  rw [quarterEndpoint_prefix_fiber hac hcb Q hQ C hC hbN p₀ q hq hr,Finset.image_image]
  exact Finset.image_congr fun u _ => quarterEndpointPoint_local hac Q p₀ r u

theorem quarterEndpoint_prefix_near {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c)) :
    ∀ x ∈ quarterEndpointSet Q C a b p₀, dist x (q x) ≤ 1/(2:ℝ)^(c-a+2) := by
  intro x hx
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
  rw [hq r hr]
  have hrC : r ∈ cubePaths 2 b :=
    planar_prefix_image_take_cubePaths hC hbN (prefixChildren_mem_image hr)
  have hh := quarterEndpointPoint_near hcb Q hQ a p₀ r hrC
  rw [show 4/(2:ℝ)^a = 4*(1/(2:ℝ)^a) by ring,dyadic_local_mesh a c hac] at hh
  exact hh

end Falconer

end OAI
