import OAI.Analysis.SphereIsometry.FiniteComplex
import OAI.Analysis.SphereIsometry.SpernerFacet
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Counting labelled incidences in a finite complex

The two orders of summation count the same actual top-cell/facet pairs. Local
facet parity leaves the fully labelled top cells on one side. Degree two
facets cancel on the other side, leaving only the degree one boundary facets.
-/

open scoped BigOperators

namespace Tingley.FiniteComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem goodFacets_eq_codim_filter (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) {σ : Finset V} (hσ : σ ∈ K.topCells m) :
    (K.codimFaces m).filter
        (fun τ => τ ⊆ σ ∧ τ.image label = spernerSmallLabels m) =
      spernerGoodFacets m label σ := by
  classical
  ext τ
  rw [Finset.mem_filter, mem_spernerGoodFacets]
  constructor
  · rintro ⟨hτ, hsub, hlabel⟩
    exact ⟨hsub, (mem_codimFaces.mp hτ).2, hlabel⟩
  · rintro ⟨hsub, hcard, hlabel⟩
    exact ⟨mem_codimFaces.mpr
      ⟨K.down_closed (mem_topCells.mp hσ).1 hsub, hcard⟩, hsub, hlabel⟩

/-- Finite incidence parity, before the boundary restriction is identified with
the lower-dimensional simplex. All hypotheses concern finite face incidence. -/
theorem sperner_count_mod_two (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2) :
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
      (((K.codimFaces m).filter
        (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) := by
  classical
  have hrow : ∀ σ ∈ K.topCells m,
      (∑ τ ∈ K.codimFaces m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if σ.image label = Finset.univ then 1 else 0 := by
    intro σ hσ
    rw [Finset.sum_boole, goodFacets_eq_codim_filter K m label hσ]
    exact spernerGoodFacets_card_mod_two label σ (mem_topCells.mp hσ).2
  have hcolumn : ∀ τ ∈ K.codimFaces m,
      (∑ σ ∈ K.topCells m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if τ.image label = spernerSmallLabels m ∧ boundary τ then 1 else 0 := by
    intro τ hτ
    by_cases hg : τ.image label = spernerSmallLabels m
    · simp only [hg, and_true, true_and]
      rw [Finset.sum_boole]
      change ((K.incidentTop m τ).card : ZMod 2) = if boundary τ then 1 else 0
      rw [hdegree τ hτ]
      by_cases hb : boundary τ
      · simp [hb]
      · simp only [hb, ite_false]
        exact ZMod.natCast_self 2
    · simp [hg]
  calc
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
        ∑ σ ∈ K.topCells m,
          if σ.image label = Finset.univ then (1 : ZMod 2) else 0 :=
      Finset.natCast_card_filter _ _
    _ = ∑ σ ∈ K.topCells m, ∑ τ ∈ K.codimFaces m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl (fun σ hσ => (hrow σ hσ).symm)
    _ = ∑ τ ∈ K.codimFaces m, ∑ σ ∈ K.topCells m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_comm
    _ = ∑ τ ∈ K.codimFaces m,
          if τ.image label = spernerSmallLabels m ∧ boundary τ then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl hcolumn
    _ = (((K.codimFaces m).filter
          (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) :=
      Finset.sum_boole _ _

/-- An odd number of good boundary facets gives an odd number of fully labelled cells. -/
theorem sperner_odd_of_boundary_odd (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2)
    (hboundary : Odd (((K.codimFaces m).filter
      (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card)) :
    Odd (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  rw [sperner_count_mod_two K m label boundary hdegree]
  exact ZMod.natCast_eq_one_iff_odd.mpr hboundary

end Tingley.FiniteComplex

end OAI
