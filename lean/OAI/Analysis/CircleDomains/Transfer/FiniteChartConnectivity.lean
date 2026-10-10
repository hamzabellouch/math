import OAI.Analysis.CircleDomains.Topology.SmallPhysicalDisks

namespace OAI

/-!
# Passing a connected exterior through the finite sphere chart

Deleting an interior point from a connected set preserves connectedness when
that point has a connected punctured neighborhood. Applied at infinity, this
turns the connected sphere inverse image of a quotient exterior into the
connected unbounded planar exterior needed for smooth contour filling.
-/

open Set Filter Function Metric
open scoped Topology OnePoint

namespace CircleDomainRigidity

private theorem puncture_subset_of_boundary_color
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {S A B U : Set X} {p : X} (hp : p ∉ S)
    (hconn : IsPreconnected (insert p S))
    (hA : IsClosed A) (hB : IsClosed B) (hcover : S ⊆ A ∪ B)
    (hAB : S ∩ (A ∩ B) = ∅) (hU : U ∈ 𝓝 p)
    (hcolor : U \ {p} ⊆ A) : S ⊆ A := by
  have hpB : p ∉ closure (S ∩ B) := by
    intro h
    obtain ⟨z, hzU, hzS, hzB⟩ := mem_closure_iff_nhds.mp h U hU
    have hzp : z ≠ p := fun heq => hp (heq ▸ hzS)
    have hzA := hcolor ⟨hzU, by simpa using hzp⟩
    have hbad : z ∈ S ∩ (A ∩ B) := ⟨hzS, hzA, hzB⟩
    simp only [hAB, mem_empty_iff_false] at hbad
  let A' := closure (S ∩ A) ∪ {p}
  let B' := closure (S ∩ B)
  have hcov : insert p S ⊆ A' ∪ B' := by
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl (Or.inr rfl)
    · rcases hcover hz with hzA | hzB
      · exact Or.inl (Or.inl (subset_closure ⟨hz, hzA⟩))
      · exact Or.inr (subset_closure ⟨hz, hzB⟩)
  have hdisj : insert p S ∩ (A' ∩ B') = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hzA, hzB⟩
    rcases hz with rfl | hz
    · exact hpB hzB
    · have hzA' : z ∈ A := by
        rcases hzA with hzA | hzA
        · exact closure_minimal inter_subset_right hA hzA
        · exact (hp (mem_singleton_iff.mp hzA ▸ hz)).elim
      have hzB' : z ∈ B := closure_minimal inter_subset_right hB hzB
      have hbad : z ∈ S ∩ (A ∩ B) := ⟨hz, hzA', hzB'⟩
      simp only [hAB, mem_empty_iff_false] at hbad
  have hside := (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) A' B'
    (isClosed_closure.union isClosed_singleton) isClosed_closure hcov hdisj
  rcases hside with hside | hside
  · intro z hz
    rcases hside (Or.inr hz) with hzA | hzA
    · exact closure_minimal inter_subset_right hA hzA
    · exact (hp (mem_singleton_iff.mp hzA ▸ hz)).elim
  · exact (hpB (hside (Or.inl rfl))).elim

/-- A point with a connected punctured neighborhood is not a cut point
of any connected set containing that neighborhood. -/
theorem isPreconnected_puncture_of_connected_neighborhood
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {S U : Set X} {p : X} (hp : p ∉ S)
    (hconn : IsPreconnected (insert p S)) (hU : U ∈ 𝓝 p)
    (hUS : U \ {p} ⊆ S) (hpuncture : IsPreconnected (U \ {p})) :
    IsPreconnected S := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro A B hA hB hcover hAB
  have hchoice := (isPreconnected_iff_subset_of_disjoint_closed.mp hpuncture)
    A B hA hB (hUS.trans hcover) (by
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz, hzA, hzB⟩
      have hbad : z ∈ S ∩ (A ∩ B) := ⟨hUS hz, hzA, hzB⟩
      simp only [hAB, mem_empty_iff_false] at hbad)
  rcases hchoice with hchoice | hchoice
  · exact Or.inl (puncture_subset_of_boundary_color hp hconn hA hB hcover hAB hU hchoice)
  · right
    apply puncture_subset_of_boundary_color hp hconn hB hA
      (by simpa only [union_comm] using hcover) _ hU hchoice
    simpa only [inter_comm A B] using hAB

theorem isConnected_complex_exterior_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (closedBall (0 : ℂ) R)ᶜ := by
  let g : ℂ × ℝ → ℂ := fun p => p.2 • p.1
  have hg : Continuous g := continuous_snd.smul continuous_fst
  have heq : g '' (sphere (0 : ℂ) 1 ×ˢ Ioi R) = (closedBall (0 : ℂ) R)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨w, r⟩, ⟨hw, hr⟩, rfl⟩
      have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hr0 : 0 < r := hR.trans_lt hr
      simpa [g, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hw'] using hr
    · intro hz
      have hz' : R < ‖z‖ := by simpa using hz
      have hn : ‖z‖ ≠ 0 := (hR.trans_lt hz').ne'
      refine ⟨(‖z‖⁻¹ • z, ‖z‖), ⟨?_, hz'⟩, ?_⟩
      · apply mem_sphere_zero_iff_norm.mpr
        simp [hn]
      · simp [g, hn]
  rw [← heq]
  exact ((isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num)
    (0 : ℂ) zero_le_one).prod isConnected_Ioi).image g hg.continuousOn

/-- The finite part of a connected sphere set containing a neighborhood
of infinity is preconnected and unbounded. -/
theorem finite_part_connected_unbounded {K : Set Sphere}
    (hK : IsPreconnected K) (hinfty : ∞ ∈ interior K) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' K) ∧
      ¬ Bornology.IsBounded (((↑) : ℂ → Sphere) ⁻¹' K) := by
  have hsmall := (OnePoint.isOpen_iff_of_mem hinfty).mp isOpen_interior
  obtain ⟨R, hR, hbound⟩ := hsmall.2.isBounded.exists_pos_norm_lt
  let E : Set ℂ := (closedBall (0 : ℂ) R)ᶜ
  let U : Set Sphere := (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) R)ᶜ
  have hUopen : IsOpen U :=
    (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩).isOpen_compl
  have hinftyU : (∞ : Sphere) ∈ U := OnePoint.infty_notMem_image_coe
  have hUeq : U \ {∞} = ((↑) : ℂ → Sphere) '' E := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [U]
    | coe z => simp [U, E, OnePoint.coe_injective.mem_set_image]
  have hEs : E ⊆ ((↑) : ℂ → Sphere) ⁻¹' K := by
    intro z hz
    by_contra hzK
    have hzsmall : z ∈ (((↑) : ℂ → Sphere) ⁻¹' interior K)ᶜ := by
      intro h
      apply hzK
      change (z : Sphere) ∈ K
      exact interior_subset h
    have hn : R < ‖z‖ := by simpa [E] using hz
    exact (not_lt_of_ge (hbound z hzsmall).le) hn
  have hpuncture : IsPreconnected (U \ {∞}) := by
    rw [hUeq]
    exact (isConnected_complex_exterior_closedBall hR.le).isPreconnected.image _
      OnePoint.continuous_coe.continuousOn
  have hset : insert (∞ : Sphere) (K \ {∞}) = K := by
    rw [insert_sdiff_singleton, insert_eq_of_mem (interior_subset hinfty)]
  have hfinite : IsPreconnected (K \ {∞}) := by
    apply isPreconnected_puncture_of_connected_neighborhood
      (by simp) (hset.symm ▸ hK) (hUopen.mem_nhds hinftyU) _ hpuncture
    rw [hUeq]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hEs hz, by simp⟩
  have himage : ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' K) = K \ {∞} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  refine ⟨OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    (himage.symm ▸ hfinite), ?_⟩
  intro hb
  have hball : Bornology.IsBounded (closedBall (0 : ℂ) R) := isBounded_closedBall
  have htotal := hball.union (hb.subset hEs)
  rw [union_compl_self] at htotal
  exact NormedSpace.unbounded_univ ℝ ℂ htotal

/-- A closed quotient with connected fibers pulls a closed connected
quotient exterior back to a connected unbounded physical exterior. -/
theorem physical_exterior_connected_unbounded_of_quotient
    {X : Type*} [TopologicalSpace X]
    (π : Sphere → X) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hsurj : Surjective π) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {V : Set X} (hV : IsOpen V) (hVconn : IsConnected Vᶜ)
    (hinfty : π ∞ ∉ closure V) :
    IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ ∧
      ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ := by
  have hK : IsConnected (π ⁻¹' Vᶜ) :=
    (hclosed.isQuotientMap hπ hsurj).isCoinducing.isConnected_preimage_of_isClosed
      hfibers hV.isClosed_compl hVconn
  have hnbd : π ⁻¹' (closure V)ᶜ ∈ 𝓝 (∞ : Sphere) :=
    (isClosed_closure.isOpen_compl.preimage hπ).mem_nhds hinfty
  have hnear : π ⁻¹' Vᶜ ∈ 𝓝 (∞ : Sphere) :=
    Filter.mem_of_superset hnbd (preimage_mono (compl_subset_compl.mpr subset_closure))
  have h := finite_part_connected_unbounded hK.isPreconnected
    (mem_interior_iff_mem_nhds.mpr hnear)
  simpa only [preimage_compl, preimage_preimage, Function.comp_def] using h

/-- Specialization to a component-collapse quotient. -/
theorem physical_exterior_connected_unbounded_of_component_collapse
    {X : Type*} [TopologicalSpace X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {V : Set X} (hV : IsOpen V) (hVconn : IsConnected Vᶜ)
    (hinfty : π ∞ ∉ closure V) :
    IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ ∧
      ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ :=
  physical_exterior_connected_unbounded_of_quotient π hπ hclosed hsurj
    (connected_fibers_of_component_collapse G π hsurj hr) hV hVconn hinfty

end CircleDomainRigidity

end OAI
