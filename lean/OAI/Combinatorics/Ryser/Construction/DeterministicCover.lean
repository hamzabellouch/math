import OAI.Combinatorics.Ryser.Construction.InfiniteCover
import OAI.Combinatorics.Ryser.Construction.FiniteInsideCover
import OAI.Combinatorics.Ryser.Construction.FiniteOutsideCover
import OAI.Combinatorics.Ryser.Construction.DeletionUnionInside
import OAI.Combinatorics.Ryser.Construction.DeletionParallel
import OAI.Combinatorics.Ryser.Construction.GroupBounds
import OAI.Combinatorics.Ryser.Construction.GadgetGood
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

section Forcing

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F] [Fintype G]

theorem forcedPencilVertices_subset_of_near_pencil
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) (δ ρ : ℝ)
    (hgap : 1 + ρ * Fintype.card F < δ * Fintype.card F / 2)
    (hline : ∀ ell ∉ B,
      δ * Fintype.card F / 2 ≤ ((data.ordinaryPoints ∩ linePoints ell).card : ℝ))
    (hnear : (1 - ρ) * Fintype.card F ≤
      ((ordinaryLines data C ∩ affinePencil p).card : ℝ)) :
    forcedPencilVertices data B p ⊆ C := by
  have hbudget := (ordinaryLines_offPencil_add_onPencil_le data C p).trans hCcard
  have hbudgetReal : ((ordinaryLines data C \ affinePencil p).card : ℝ) +
      ((ordinaryLines data C ∩ affinePencil p).card : ℝ) ≤ Fintype.card F := by
    exact_mod_cast hbudget
  have hoff : ((ordinaryLines data C \ affinePencil p).card : ℝ) ≤
      ρ * Fintype.card F := by nlinarith
  apply forcedPencilVertices_subset_cover data C hC B p
  intro ell _ hell
  have hdensity := hline ell hell
  have hstrict : (1 : ℝ) + ((ordinaryLines data C \ affinePencil p).card : ℝ) <
      ((data.ordinaryPoints ∩ linePoints ell).card : ℝ) := by linarith
  exact_mod_cast hstrict

end Forcing

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]
variable (σ : k →+* F) (u v : k) (huv : u ≠ v)
variable (a : GadgetOutcome k) (b : ConfigurationGroup σ → Point F)
variable (X : Finset (Point F))

local instance : DecidableEq (ConfigurationGroup σ) := Classical.decEq _

local notation "M" => groupPlacement σ u v huv
local notation "data" => placedConfiguration σ M b (retainedPoints a) X

theorem not_isCover_actual_group_configuration
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (ha : GoodGadget a)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : 1 + (δ / 10) * Fintype.card F < δ * Fintype.card F / 2)
    (hsep : DeletionSeparated σ M b a)
    (hthin : ∀ p : Point F, OffPencilThin data p)
    (hline : ∀ ell ∉ allDeletedLines σ M b a,
      δ * Fintype.card F / 2 ≤ ((X ∩ linePoints ell).card : ℝ))
    (hnear : ∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      (∀ x ∈ X, ∃ ell ∈ L, Incidence x ell) →
      ∃ p : ProjectivePoint F,
        (1 - δ / 10) * Fintype.card F ≤ ((L ∩ affinePencil p).card : ℝ))
    (C : Finset (Vertex (k := k) (data).altered))
    (hCcard : C.card ≤ Fintype.card F) : ¬ IsCover (hypergraph data) C := by
  let _ := hδ
  classical
  intro hC
  let B := allDeletedLines σ M b a
  have hY : GadgetCoverProperty ((retainedPoints a).image cubeMap) := ha.2.2
  have hordinary := ordinaryLines_cover_ordinaryPoints data C hC
  obtain ⟨p, hp⟩ := hnear (ordinaryLines data C)
    ((ordinaryLines_card_le data C).trans hCcard) hordinary
  have hforced : forcedPencilVertices data B p ⊆ C :=
    forcedPencilVertices_subset_of_near_pencil data C hC hCcard B p δ (δ / 10)
      hgap hline hp
  cases p with
  | inr d =>
      let I : Finset (ConfigurationGroup σ) :=
        Finset.univ.filter (fun i => d ∈ groupAltered σ u v huv i)
      have hIle : I.card ≤ 2 := groupAltered_multiplicity_le_two σ u v huv d
      have hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤
          I.card * (Fintype.card k - 1) :=
        card_allDeletedLines_inter_affinePencil_infinite_le σ M b a ha.1 d
      obtain ⟨i, hi⟩ := exists_groupAltered σ u v huv hu hv d
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      by_cases hother : ∃ j ∈ I, j ≠ i
      · obtain ⟨j, hjI, hji⟩ := hother
        have hij : i ≠ j := hji.symm
        have hj : d ∈ groupAltered σ u v huv j := (Finset.mem_filter.mp hjI).2
        have hItwo : I.card = 2 := by
          have hgt : 1 < I.card := Finset.one_lt_card.mpr ⟨i, hiI, j, hjI, hij⟩
          omega
        rw [hItwo] at hdeleted
        exact double_infinite_center_impossible σ M b (retainedPoints a) X hcop hY
          C hC hCcard B d i j hij hi hj
          (shared_groupAltered_axes_subset σ u v huv hu hv hij hi hj)
          (shared_groupAltered_axes_subset σ u v huv hu hv hji hj hi)
          hforced hdeleted
      · have hIone : I.card = 1 := by
          have hsub : I ⊆ {i} := by
            intro j hj
            have hji : j = i := by
              by_contra hji
              exact hother ⟨j, hj, hji⟩
            exact Finset.mem_singleton.mpr hji
          have hle : I.card ≤ 1 := by
            simpa only [Finset.card_singleton] using (Finset.card_le_card hsub)
          have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hiI⟩
          omega
        rw [hIone, one_mul] at hdeleted
        exact single_infinite_center_impossible σ M b (retainedPoints a) X hcop hY
          C hC hCcard B d i hi hforced hdeleted
  | inl p =>
      by_cases hinside : ∃ i : ConfigurationGroup σ,
          p ∈ placedSubplane σ (M i) (b i)
      · obtain ⟨i, hpi⟩ := hinside
        have hdeleted := card_deletedPencil_le_of_mem_placedSubplane
          σ M b a hsep i p hpi
        have hpencil : deletedPencil σ M b a p = B ∩ affinePencil (Sum.inl p) := by
          ext ell
          simp only [mem_deletedPencil, Finset.mem_inter, mem_affinePencil,
            projectiveIncidence_finite_affine, B]
        rw [hpencil] at hdeleted
        obtain ⟨wp, rfl⟩ := (mem_placedSubplane_iff σ (M i) (b i) p).1 hpi
        exact finite_inside_center_impossible σ M b (retainedPoints a) X hcop hY
          i wp C hC hCcard B hforced hdeleted
      · have hout : ∀ i : ConfigurationGroup σ,
            p ∉ placedSubplane σ (M i) (b i) := by
          intro i hi
          exact hinside ⟨i, hi⟩
        exact not_isCover_of_finite_outside_placedSubplanes σ M b a ha.1 hsep data
          (fun _ => rfl) (fun _ => rfl) rfl p hout (hthin p) C hforced hCcard hC

end RyserCoveringCounterexample.Construction

end

end OAI
