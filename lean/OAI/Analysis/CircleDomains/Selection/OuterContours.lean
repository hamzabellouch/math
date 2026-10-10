import OAI.Analysis.CircleDomains.Topology.JordanContours
import Mathlib.Order.Preorder.Finite

namespace OAI

/-!
# Selecting outer Jordan contours

The disks are images of the unit disk by planar homeomorphisms. Connected
exteriors and the nesting alternative allow selection of the maximal
members of a finite family.
-/

open Set Filter Function
open scoped Topology

namespace CircleDomainRigidity

def jordanInterior (H : ℂ ≃ₜ ℂ) : Set ℂ := H '' Metric.ball (0 : ℂ) 1

theorem jordanInterior_isOpen (H : ℂ ≃ₜ ℂ) : IsOpen (jordanInterior H) :=
  H.isOpenMap _ Metric.isOpen_ball

theorem closure_jordanInterior (H : ℂ ≃ₜ ℂ) :
    closure (jordanInterior H) = H '' Metric.closedBall (0 : ℂ) 1 := by
  rw [jordanInterior, ← H.image_closure, closure_ball _ one_ne_zero]

theorem isCompact_closure_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsCompact (closure (jordanInterior H)) := by
  rw [closure_jordanInterior]
  exact (isCompact_closedBall (0 : ℂ) 1).image H.continuous

theorem interior_closure_jordanInterior (H : ℂ ≃ₜ ℂ) :
    interior (closure (jordanInterior H)) = jordanInterior H := by
  rw [closure_jordanInterior, ← H.image_interior, interior_closedBall _ one_ne_zero]
  rfl

theorem frontier_jordanInterior (H : ℂ ≃ₜ ℂ) :
    frontier (jordanInterior H) = H '' Metric.sphere (0 : ℂ) 1 := by
  rw [jordanInterior, ← H.image_frontier, frontier_ball _ one_ne_zero]

theorem isConnected_jordanInterior (H : ℂ ≃ₜ ℂ) : IsConnected (jordanInterior H) :=
  (Metric.isConnected_ball zero_lt_one).image H H.continuous.continuousOn

private theorem planar_unit_sphere_connected : IsConnected (Metric.sphere (0 : ℂ) 1) :=
  isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one

theorem isConnected_frontier_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsConnected (frontier (jordanInterior H)) := by
  rw [frontier_jordanInterior]
  exact planar_unit_sphere_connected.image H H.continuous.continuousOn

private theorem planar_unit_exterior_connected :
    IsConnected (Metric.closedBall (0 : ℂ) 1)ᶜ := by
  let g : ℂ × ℝ → ℂ := fun p => p.2 • p.1
  have hg : Continuous g := continuous_snd.smul continuous_fst
  have heq : g '' (Metric.sphere (0 : ℂ) 1 ×ˢ Ioi (1 : ℝ)) =
      (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨w, r⟩, ⟨hw, hr⟩, rfl⟩
      have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hr0 : 0 < r := zero_lt_one.trans hr
      simpa [g, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hw'] using hr
    · intro hz
      have hz' : 1 < ‖z‖ := by simpa using hz
      have hn : ‖z‖ ≠ 0 := (zero_lt_one.trans hz').ne'
      refine ⟨(‖z‖⁻¹ • z, ‖z‖), ⟨?_, hz'⟩, ?_⟩
      · apply mem_sphere_zero_iff_norm.mpr
        simp [hn]
      · simp [g, hn]
  rw [← heq]
  exact (planar_unit_sphere_connected.prod isConnected_Ioi).image g hg.continuousOn

theorem isConnected_exterior_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsConnected (closure (jordanInterior H))ᶜ := by
  rw [closure_jordanInterior, ← H.image_compl]
  exact planar_unit_exterior_connected.image H H.continuous.continuousOn

private theorem subset_inside_or_exterior {S U : Set ℂ} (hU : IsOpen U)
    (hS : IsPreconnected S) (hdisj : Disjoint S (frontier U)) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
  · intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      intro hzcl
      apply Set.disjoint_left.mp hdisj hz
      rw [frontier, hU.interior_eq]
      exact ⟨hzcl, hzU⟩

private theorem exterior_not_bounded {U : Set ℂ} (hU : Bornology.IsBounded U) :
    ¬ Bornology.IsBounded Uᶜ := by
  intro hUc
  apply NormedSpace.unbounded_univ ℝ ℂ
  simpa only [union_compl_self] using hU.union hUc

private theorem closed_fill_subset_of_frontier_subset {U V : Set ℂ}
    (hU : IsOpen U) (_hV : IsOpen V)
    (hVregular : interior (closure V) = V)
    (hUcompact : IsCompact (closure U)) (hVcompact : IsCompact (closure V))
    (hVexterior : IsPreconnected (closure V)ᶜ)
    (hfront : frontier U ⊆ V) : closure U ⊆ V := by
  have hdisj : Disjoint (closure V)ᶜ (frontier U) :=
    Set.disjoint_left.mpr (fun z hz hz' => hz (subset_closure (hfront hz')))
  have hext : (closure V)ᶜ ⊆ (closure U)ᶜ := by
    rcases subset_inside_or_exterior hU hVexterior hdisj with h | h
    · exact False.elim (exterior_not_bounded hVcompact.isBounded
        ((hUcompact.isBounded.subset subset_closure).subset h))
    · exact h
  have hcl : closure U ⊆ closure V := compl_subset_compl.mp hext
  have hUV : U ⊆ V := by
    calc
      U = interior U := hU.interior_eq.symm
      _ ⊆ interior (closure V) := interior_mono (subset_closure.trans hcl)
      _ = V := hVregular
  rw [closure_eq_self_union_frontier]
  exact union_subset hUV hfront

/-- A Jordan contour contained in the interior of another Jordan disk has its
entire closed fill in that interior. -/
theorem closed_jordanInterior_subset_of_frontier_subset (H K : ℂ ≃ₜ ℂ)
    (hfront : frontier (jordanInterior H) ⊆ jordanInterior K) :
    closure (jordanInterior H) ⊆ jordanInterior K :=
  closed_fill_subset_of_frontier_subset (jordanInterior_isOpen H) (jordanInterior_isOpen K)
    (interior_closure_jordanInterior K) (isCompact_closure_jordanInterior H)
    (isCompact_closure_jordanInterior K)
    (isConnected_exterior_jordanInterior K).isPreconnected hfront

private theorem disjoint_or_nested_closed_fills {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVregular : interior (closure V) = V)
    (hUcompact : IsCompact (closure U)) (hVcompact : IsCompact (closure V))
    (hUfront : IsPreconnected (frontier U)) (hVconn : IsPreconnected V)
    (hVext : IsPreconnected (closure V)ᶜ)
    (hdisj : Disjoint (frontier U) (frontier V)) :
    Disjoint (closure U) (closure V) ∨ closure U ⊆ V ∨ closure V ⊆ U := by
  rcases subset_inside_or_exterior hV hUfront hdisj with hfront | hfront
  · exact Or.inr (Or.inl (closed_fill_subset_of_frontier_subset hU hV hVregular
      hUcompact hVcompact hVext hfront))
  · have hd : Disjoint V (frontier U) := Set.disjoint_left.mpr (fun z hz hz' =>
      hfront hz' (subset_closure hz))
    rcases subset_inside_or_exterior hU hVconn hd with hVU | hVout
    · right; right
      intro z hz
      have hzclU := closure_mono hVU hz
      by_contra hzU
      have hzfront : z ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hzclU, hzU⟩
      exact hfront hzfront hz
    · left
      have hVclout : closure V ⊆ Uᶜ := by
        apply closure_minimal _ hU.isClosed_compl
        intro z hz hzU
        exact hVout hz (subset_closure hzU)
      apply Set.disjoint_left.mpr
      intro z hzU hzV
      have hnotU := hVclout hzV
      have hzfront : z ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hzU, hnotU⟩
      exact hfront hzfront hzV

/-- Disjoint Jordan contours have disjoint closed fills or one closed fill
lies strictly inside the other disk. -/
theorem disjoint_or_nested_jordanInteriors (H K : ℂ ≃ₜ ℂ)
    (hdisj : Disjoint (frontier (jordanInterior H)) (frontier (jordanInterior K))) :
    Disjoint (closure (jordanInterior H)) (closure (jordanInterior K)) ∨
      closure (jordanInterior H) ⊆ jordanInterior K ∨
      closure (jordanInterior K) ⊆ jordanInterior H :=
  disjoint_or_nested_closed_fills (jordanInterior_isOpen H) (jordanInterior_isOpen K)
    (interior_closure_jordanInterior K) (isCompact_closure_jordanInterior H)
    (isCompact_closure_jordanInterior K) (isConnected_frontier_jordanInterior H).isPreconnected
    (isConnected_jordanInterior K).isPreconnected
    (isConnected_exterior_jordanInterior K).isPreconnected hdisj

/-- Select the outer members of a finite family of disjoint Jordan contours.
Their closed disks are pairwise disjoint and cover all the original filled
disks. Since this is a subfamily, any prescribed contour properties persist. -/
theorem exists_outer_jordanInteriors {ι : Type*} [Finite ι]
    (H : ι → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j))))) :
    ∃ s : Set ι, s.Finite ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i, ∃ j ∈ s, closure (jordanInterior (H i)) ⊆ closure (jordanInterior (H j))) ∧
      (⋃ i ∈ s, closure (jordanInterior (H i))) = ⋃ i, closure (jordanInterior (H i)) := by
  classical
  let C : ι → Set ℂ := fun i => closure (jordanInterior (H i))
  let s : Set ι := {i | ∀ j, C i ⊆ C j → C j ⊆ C i}
  have hdom (i : ι) : ∃ j ∈ s, C i ⊆ C j := by
    obtain ⟨D, hiD, hD⟩ := (Set.finite_range C).exists_le_maximal (Set.mem_range_self i)
    obtain ⟨j, rfl⟩ := hD.1
    exact ⟨j, fun k hk => hD.2 (Set.mem_range_self k) hk, hiD⟩
  refine ⟨s, s.toFinite, ?_, hdom, ?_⟩
  · intro i hi j hj hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hdisj hij) with h | h | h
    · exact h
    · have hji : C j ⊆ C i := hi j (h.trans subset_closure)
      have hbad : C j ⊆ jordanInterior (H j) := hji.trans h
      obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hz' := hbad (frontier_subset_closure hz)
      have hn : z ∉ jordanInterior (H j) := by
        simpa [frontier, (jordanInterior_isOpen (H j)).interior_eq] using hz.2
      exact (hn hz').elim
    · have hij' : C i ⊆ C j := hj i (h.trans subset_closure)
      have hbad : C i ⊆ jordanInterior (H i) := hij'.trans h
      obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hz' := hbad (frontier_subset_closure hz)
      have hn : z ∉ jordanInterior (H i) := by
        simpa [frontier, (jordanInterior_isOpen (H i)).interior_eq] using hz.2
      exact (hn hz').elim
  · apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion_of_subset i subset_rfl
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨j, hj, hij⟩ := hdom i
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hij hi⟩⟩

/-- The selected outer disks stay inside a Jordan container whenever every
original boundary curve lies inside it. This is the containment step used
when smoothing dust neighborhoods. -/
theorem exists_outer_jordanInteriors_in_container {ι : Type*} [Finite ι]
    (H : ι → ℂ ≃ₜ ℂ) (K : ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))))
    (hinside : ∀ i, frontier (jordanInterior (H i)) ⊆ jordanInterior K) :
    ∃ s : Set ι, s.Finite ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i, ∃ j ∈ s, closure (jordanInterior (H i)) ⊆ closure (jordanInterior (H j))) ∧
      ∀ i ∈ s, closure (jordanInterior (H i)) ⊆ jordanInterior K := by
  obtain ⟨s, hs, hpair, hdom, _⟩ := exists_outer_jordanInteriors H hdisj
  exact ⟨s, hs, hpair, hdom, fun i _ =>
    closed_jordanInterior_subset_of_frontier_subset (H i) K (hinside i)⟩

theorem frontier_jordanInterior_eq_circle_range (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ)
    (hH : ∀ z : Circle, H (z : ℂ) = γ z) :
    frontier (jordanInterior H) = range γ := by
  rw [frontier_jordanInterior]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, (hH ⟨z, hz⟩).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.property, hH z⟩

/-- Actual disjoint closed fills for an outer subfamily of finitely many
embedded circles in a Jordan container. The circle maps are retained, so
smoothness and avoidance properties of those maps require no reconstruction. -/
theorem exists_outer_circle_fills_in_container {ι : Type*} [Finite ι]
    (hschoenflies : PlanarSchoenflies) (γ : ι → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hinj : ∀ i, Injective (γ i))
    (hdisj : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (K : ℂ ≃ₜ ℂ) (hinside : ∀ i, range (γ i) ⊆ jordanInterior K) :
    ∃ (H : ι → ℂ ≃ₜ ℂ) (s : Set ι), s.Finite ∧
      (∀ i, frontier (jordanInterior (H i)) = range (γ i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i, ∃ j ∈ s, closure (jordanInterior (H i)) ⊆ closure (jordanInterior (H j))) ∧
      ∀ i ∈ s, closure (jordanInterior (H i)) ⊆ jordanInterior K := by
  classical
  choose H hH using fun i => hschoenflies (γ i) (hγ i) (hinj i)
  have hfront i := frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hdisj hij
  have hc i : frontier (jordanInterior (H i)) ⊆ jordanInterior K := by
    rw [hfront]
    exact hinside i
  obtain ⟨s, hs, hp, hd, hc⟩ := exists_outer_jordanInteriors_in_container H K hpair hc
  exact ⟨H, s, hs, hfront, hp, hd, hc⟩

end CircleDomainRigidity

end OAI
