import OAI.Analysis.SphereIsometry.DiameterBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! # The Kuratowski measure from finite diameter covers

The infimum uses positive real radii. The boundedness
hypotheses ensure that its defining set is nonempty. No compactness theorem
or fixed-point principle is part of this definition.
-/

namespace Tingley

variable {E : Type*} [PseudoMetricSpace E]

/-- A finite family of sets of pairwise diameter at most the given radius. -/
def FiniteDiameterCover (H : Set E) (δ : ℝ) : Prop :=
  ∃ n : ℕ, ∃ A : Fin n → Set E,
    (H ⊆ ⋃ i, A i) ∧ ∀ i, DiameterLE (A i) δ

namespace FiniteDiameterCover

variable {H A B : Set E} {δ ε : ℝ}

theorem of_fintype {ι : Type*} [Fintype ι] (U : ι → Set E)
    (hc : H ⊆ ⋃ i, U i) (hd : ∀ i, DiameterLE (U i) δ) :
    FiniteDiameterCover H δ := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => U (e.symm j), ?_, fun j => hd (e.symm j)⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
  exact Set.mem_iUnion.mpr ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩

theorem of_finite {ι : Type*} [Finite ι] (U : ι → Set E)
    (hc : H ⊆ ⋃ i, U i) (hd : ∀ i, DiameterLE (U i) δ) :
    FiniteDiameterCover H δ := by
  classical
  let := Fintype.ofFinite ι
  exact of_fintype U hc hd

theorem empty (δ : ℝ) : FiniteDiameterCover (∅ : Set E) δ := by
  refine ⟨0, fun _ => ∅, Set.empty_subset _, ?_⟩
  intro i
  exact Fin.elim0 i

theorem mono_set (hc : FiniteDiameterCover B δ) (hAB : A ⊆ B) :
    FiniteDiameterCover A δ := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  exact ⟨n, U, hAB.trans hcover, hd⟩

theorem mono_radius (hc : FiniteDiameterCover H δ) (hδε : δ ≤ ε) :
    FiniteDiameterCover H ε := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  exact ⟨n, U, hcover, fun i => (hd i).mono_radius hδε⟩

theorem closure (hc : FiniteDiameterCover H δ) :
    FiniteDiameterCover (closure H) δ := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  refine ⟨n, fun i => _root_.closure (U i), ?_, fun i => (hd i).closure⟩
  intro x hx
  have hx' : x ∈ _root_.closure (⋃ i, U i) := closure_mono hcover hx
  simpa only [closure_iUnion_of_finite] using hx'

end FiniteDiameterCover

/-- Positive radii admitting a finite diameter cover. -/
def coverRadii (H : Set E) : Set ℝ :=
  {δ | 0 < δ ∧ FiniteDiameterCover H δ}

/-- The Kuratowski measure of noncompactness, on bounded sets. -/
noncomputable def chi (H : Set E) : ℝ := sInf (coverRadii H)

theorem coverRadii_bddBelow (H : Set E) : BddBelow (coverRadii H) :=
  ⟨0, fun _ hδ => hδ.1.le⟩

theorem coverRadii_nonempty {H : Set E} (hH : Bornology.IsBounded H) :
    (coverRadii H).Nonempty := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hH
  have hc : FiniteDiameterCover H (max R 1) := by
    refine ⟨1, fun _ => H, ?_, ?_⟩
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · intro i x hx y hy
      exact (hR hx hy).trans (le_max_left R 1)
  exact ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right R 1), hc⟩

theorem chi_nonneg {H : Set E} (hH : Bornology.IsBounded H) : 0 ≤ chi H :=
  le_csInf (coverRadii_nonempty hH) (fun _ hδ => hδ.1.le)

theorem chi_le_of_cover {H : Set E} {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : FiniteDiameterCover H δ) : chi H ≤ δ := by
  by_contra hnot
  have hlt : δ < chi H := lt_of_not_ge hnot
  let ε : ℝ := (chi H - δ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hmem : δ + ε ∈ coverRadii H :=
    ⟨by linarith, hc.mono_radius (by linarith)⟩
  have hupper : chi H ≤ δ + ε := csInf_le (coverRadii_bddBelow H) hmem
  dsimp only [ε] at hupper
  linarith

@[simp] theorem chi_empty : chi (∅ : Set E) = 0 := by
  apply le_antisymm
  · exact chi_le_of_cover le_rfl (FiniteDiameterCover.empty 0)
  · exact chi_nonneg Bornology.isBounded_empty

theorem chi_mono {A B : Set E} (hB : Bornology.IsBounded B) (hAB : A ⊆ B) :
    chi A ≤ chi B := by
  apply csInf_le_csInf (coverRadii_bddBelow A) (coverRadii_nonempty hB)
  intro δ hδ
  exact ⟨hδ.1, hδ.2.mono_set hAB⟩

theorem exists_cover_of_chi_lt {H : Set E} {ε : ℝ}
    (hH : Bornology.IsBounded H) (hε : chi H < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ FiniteDiameterCover H δ := by
  obtain ⟨δ, hδ, hδε⟩ :=
    (csInf_lt_iff (coverRadii_bddBelow H) (coverRadii_nonempty hH)).mp hε
  exact ⟨δ, hδ.1, hδε, hδ.2⟩

theorem chi_closure {H : Set E} (hH : Bornology.IsBounded H) :
    chi (closure H) = chi H := by
  apply le_antisymm
  · apply le_csInf (coverRadii_nonempty hH)
    intro δ hδ
    exact chi_le_of_cover hδ.1.le hδ.2.closure
  · exact chi_mono hH.closure subset_closure

end Tingley

end OAI
