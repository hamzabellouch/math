import OAI.Geometry.SurfaceImmersion.Whitney.NormalBoundaryCollar

namespace OAI

/-! Construct the global normal from interior/exterior fields and strict
conditions on the disk boundary. The transition collar is derived. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
open VelocityFrame NormalFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype κ]

theorem preferredNormal_disk_gluing_within {F a b : M → Space} {D U V : Set M}
    (O : Set M) (hO : IsOpen O) (hfO : frontier D ⊆ O)
    (hD : IsOpen D) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : closure D ⊆ U) (hDV : Dᶜ ⊆ V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ frontier D, b p ≠ -a p)
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, ContinuousOn (B k) (U ∩ V))
    (haAvoid : ∀ k p, p ∈ C k → p ∈ D → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∉ closure D → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ W ⊆ O ∧ ∃ N : PreferredNormal F,
      (∀ p ∈ D \ W, N.vector p = a p) ∧
      (∀ p ∈ (closure D)ᶜ \ W, N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨W₀,hW₀,hfW₀,hW₀UV,hneW₀,hposW₀⟩ := normal_boundary_collar hD hU hV hDU hDV
    ha.continuousOn hb.continuousOn hne C hC (fun k p => spaceCoordinates.symm (B k p))
    (fun k => spaceCoordinates.symm.continuous.comp_continuousOn (hB k)) hpositive
  let W := W₀ ∩ O
  have hW : IsOpen W := hW₀.inter hO
  have hfW : frontier D ⊆ W := fun _ hp => ⟨hfW₀ hp,hfO hp⟩
  have hWUV : W ⊆ U ∩ V := fun _ hp => hW₀UV hp.1
  have hneW : ∀ p ∈ W, b p ≠ -a p := fun p hp => hneW₀ p hp.1
  have hposW : ∀ k p, p ∈ C k → p ∈ W →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p) :=
    fun k p hpC hpW => hposW₀ k p hpC hpW.1
  let U' := D ∪ W
  let V' := (closure D)ᶜ ∪ W
  have hU' : IsOpen U' := hD.union hW
  have hV' : IsOpen V' := isClosed_closure.isOpen_compl.union hW
  have hUU : U' ⊆ U := by
    intro p hp
    rcases hp with hp | hp
    · exact hDU (subset_closure hp)
    · exact (hWUV hp).1
  have hVV : V' ⊆ V := by
    intro p hp
    rcases hp with hp | hp
    · exact hDV (fun h => hp (subset_closure h))
    · exact (hWUV hp).2
  have hcover : U' ∪ V' = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ D
    · exact Or.inl (Or.inl hp)
    by_cases hpc : p ∈ closure D
    · have hf : p ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hpc,hp⟩
      exact Or.inl (Or.inr (hfW hf))
    · exact Or.inr (Or.inl hpc)
  have hUV' : U' ∩ V' ⊆ W := by
    intro p hp
    rcases hp.1 with hpD | hpW
    · rcases hp.2 with hpcl | hpW
      · exact False.elim (hpcl (subset_closure hpD))
      · exact hpW
    · exact hpW
  have havoidW (k : κ) (p : M) (hpC : p ∈ C k) (hpW : p ∈ W) :
      spaceCoordinates (a p) ≠ -normalize (B k p) ∧
      spaceCoordinates (b p) ≠ -normalize (B k p) := by
    have hh := hposW k p hpC hpW
    have hid (t : Space) : B k p ⬝ᵥ spaceCoordinates t = inner ℝ (spaceCoordinates.symm (B k p)) t := by
      rw [← spaceCoordinates_dot,ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨ne_neg_normalize_of_pairing_pos (by rw [hid]; exact hh.1),
      ne_neg_normalize_of_pairing_pos (by rw [hid]; exact hh.2)⟩
  obtain ⟨N,hNa,hNb,havoid⟩ := preferredNormal_from_cover hU' hV' (ha.mono hUU) (hb.mono hVV)
    (fun p hp => ha1 p (hUU hp)) (fun p hp => hb1 p (hVV hp))
    (fun p hp => haN p (hUU hp)) (fun p hp => hbN p (hVV hp))
    (fun p hp => hneW p (hUV' hp)) hcover C B
    (by
      intro k p hpC hpU
      rcases hpU with hpD | hpW
      · exact haAvoid k p hpC hpD
      · exact (havoidW k p hpC hpW).1)
    (by
      intro k p hpC hpV
      rcases hpV with hpcl | hpW
      · exact hbAvoid k p hpC hpcl
      · exact (havoidW k p hpC hpW).2)
    (fun k p hpC hpUV => hposW k p hpC (hUV' hpUV))
  refine ⟨W,hW,hfW,inter_subset_right,N,?_,?_,havoid⟩
  · intro p hp
    exact hNa p ⟨Or.inl hp.1,by
      intro h
      rcases h with hcl | hW
      · exact hcl (subset_closure hp.1)
      · exact hp.2 hW⟩
  · intro p hp
    exact hNb p ⟨Or.inl hp.1,by
      intro h
      rcases h with hD | hW
      · exact hp.1 (subset_closure hD)
      · exact hp.2 hW⟩


theorem preferredNormal_disk_gluing {F a b : M → Space} {D U V : Set M}
    (hD : IsOpen D) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : closure D ⊆ U) (hDV : Dᶜ ⊆ V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ frontier D, b p ≠ -a p)
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, ContinuousOn (B k) (U ∩ V))
    (haAvoid : ∀ k p, p ∈ C k → p ∈ D → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∉ closure D → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ ∃ N : PreferredNormal F,
      (∀ p ∈ D \ W, N.vector p = a p) ∧
      (∀ p ∈ (closure D)ᶜ \ W, N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨W,hW,hfW,_,N,hNa,hNb,havoid⟩ := preferredNormal_disk_gluing_within
    univ isOpen_univ (subset_univ _) hD hU hV hDU hDV ha hb ha1 hb1 haN hbN hne
    C hC B hB haAvoid hbAvoid hpositive
  exact ⟨W,hW,hfW,N,hNa,hNb,havoid⟩

end ClosedSurfaceR4

end

end OAI
