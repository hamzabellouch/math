import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonGraphCore
variable {X : Type*} [MetricSpace X] [PreconnectedSpace X]

theorem net_joined {r : ℝ} (hr : 0<r) (T Q : Set X) (hTQ : T⊆Q)
    (hcover : ∀ x : X, ∃ t∈T, dist x t≤r)
    (hjoin : ∀ x∈T, ∀ y∈T, dist x y<4*r → JoinedIn Q x y)
    {a : X} (ha : a∈T) : ∀ b∈T, JoinedIn Q a b := by
  let U := ⋃ (t : X) (_ : t∈T) (_ : JoinedIn Q a t), ball t (2*r)
  let V := ⋃ (t : X) (_ : t∈T) (_ : ¬JoinedIn Q a t), ball t (2*r)
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    simp only [U,mem_iUnion] at hzU
    obtain ⟨t,ht,hjt,hzt⟩ := hzU
    simp only [V,mem_iUnion] at hzV
    obtain ⟨u,hu,hju,hzu⟩ := hzV
    have hdt : dist z t<2*r := hzt
    have hdu : dist z u<2*r := hzu
    have htu : dist t u<4*r := by
      have hh := dist_triangle t z u
      rw [dist_comm t z] at hh
      linarith
    exact hju (hjt.trans (hjoin t ht u hu htu))
  have hcover' : (univ : Set X)⊆U∪V := by
    intro x _
    obtain ⟨t,ht,hxt⟩ := hcover x
    have hxt' : x∈ball t (2*r) := hxt.trans_lt (by linarith)
    by_cases hj : JoinedIn Q a t
    · exact Or.inl (mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨ht,mem_iUnion.mpr ⟨hj,hxt'⟩⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨ht,mem_iUnion.mpr ⟨hj,hxt'⟩⟩⟩)
  have haU : a∈U := mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨ha,
    mem_iUnion.mpr ⟨JoinedIn.refl (hTQ ha),mem_ball_self (by positivity)⟩⟩⟩
  have hall := isPreconnected_univ.subset_left_of_subset_union hU hV hdisj hcover' ⟨a,mem_univ a,haU⟩
  intro b hb
  have hbU := hall (mem_univ b)
  simp only [U,mem_iUnion] at hbU
  obtain ⟨t,ht,hjt,hbt⟩ := hbU
  apply hjt.trans (hjoin t ht b hb ?_)
  have hbt' : dist b t<2*r := hbt
  rw [dist_comm]
  linarith

end CannonGraphCore

namespace CannonGraphCore
variable {X ι : Type*} [TopologicalSpace X]

theorem component_whole_edges (E : ι → C(I,X)) (T : Set X) (a : X)
    (_ha : a∈T)
    (hT : ∀ t∈T, JoinedIn ((⋃ i, range (E i))∪T) a t) :
    let Q := (⋃ i, range (E i))∪T
    let J := {i : ι // E i 0∈pathComponentIn Q a}
    pathComponentIn Q a = (⋃ j : J, range (E j.val))∪T := by
  dsimp only
  let Q := (⋃ i, range (E i))∪T
  let _ : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  have hed (i : ι) : range (E i)⊆Q := by
    intro x hx
    exact Or.inl (mem_iUnion.mpr ⟨i,hx⟩)
  have hc (i : ι) : IsPathConnected (range (E i)) := isPathConnected_range (E i).continuous
  apply Set.Subset.antisymm
  · intro x hx
    rcases pathComponentIn_subset hx with h|h
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      have h₀ : E i 0∈pathComponentIn Q a := hx.trans ((hc i).joinedIn x hi _ (mem_range_self 0) |>.mono (hed i))
      exact Or.inl (mem_iUnion.mpr ⟨⟨i,h₀⟩,hi⟩)
    · exact Or.inr h
  · intro x hx
    rcases hx with h|h
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact i.property.trans ((hc i.val).joinedIn _ (mem_range_self 0) _ hi |>.mono (hed i.val))
    · exact hT x h

theorem path_range_in_component {Q : Set X} {a x y : X} (hax : JoinedIn Q a x)
    (p : Path x y) (hp : range p⊆Q) : range p⊆pathComponentIn Q a := by
  let _ : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  intro z hz
  have hc : IsPathConnected (range p) := isPathConnected_range p.continuous
  have hx : x∈range p := ⟨0,p.source⟩
  exact hax.trans ((hc.joinedIn x hx z hz).mono hp)
end CannonGraphCore

namespace CannonGraphCore
variable {X ι : Type*} [TopologicalSpace X]
theorem component_retains_edges (E : ι → C(I,X)) {Q : Set X} {a x : X}
    (hEQ : (⋃ i, range (E i))⊆Q) (hx : x∈pathComponentIn Q a)
    (hxE : x∈⋃ i, range (E i)) :
    x∈⋃ j : {i : ι // E i 0∈pathComponentIn Q a}, range (E j.val) := by
  let _ : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxE
  have h₀ : E i 0∈pathComponentIn Q a := hx.trans
    (((isPathConnected_range (E i).continuous).joinedIn x hi _ (mem_range_self 0)).mono
      (fun z hz => hEQ (mem_iUnion.mpr ⟨i,hz⟩)))
  exact mem_iUnion.mpr ⟨⟨i,h₀⟩,hi⟩
end CannonGraphCore

end
end
end
end
end
end
end
end

end OAI
