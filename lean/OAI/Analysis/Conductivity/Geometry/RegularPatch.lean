import Mathlib
import OAI.Analysis.Conductivity.Variational.Unchanged

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.congr {u v : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (h : TwoFieldRankRegular u O) (he : EqOn v u O) :
    TwoFieldRankRegular v O := by
  rcases h with h | h | ⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_eq_of_eqOn_open hO he hx]
    exact h x hx
  · right; left
    obtain ⟨w,l,κ,hw,hl,hwd,hrel⟩ := h
    exact ⟨w,l,κ,hw,hl,hwd,fun x hx j => by rw [he hx]; exact hrel x hx j⟩
  · exact Or.inr (Or.inr ⟨κ,fun x hx => (he hx).trans (hκ x hx)⟩)

def RegularPatch (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (O : Set Coord3) : Prop :=
  IsOpen O ∧ ContDiffOn ℝ (↑(⊤ : ℕ∞)) u O ∧
  ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) O ∧ TwoFieldRankRegular u O

lemma RegularPatch.mono {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O W : Set Coord3} (h : RegularPatch u A O) (hW : IsOpen W) (hWO : W ⊆ O) :
    RegularPatch u A W :=
  ⟨hW,h.2.1.mono hWO,h.2.2.1.mono hWO,h.2.2.2.mono hWO⟩

lemma RegularPatch.congr {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (hu : EqOn v u O) (hA : EqOn B A O) :
    RegularPatch v B O := by
  exact ⟨h.1,h.2.1.congr hu,h.2.2.1.congr (fun x hx => congrArg Subtype.val (hA hx)),
    h.2.2.2.congr h.1 hu⟩

def regularRegion (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : Set Coord3 :=
  ⋃ (O : Set Coord3) (_ : O ⊆ U) (_ : RegularPatch u A O), O

lemma isOpen_regularRegion (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : IsOpen (regularRegion u A U) := by
  exact isOpen_iUnion (fun O => isOpen_iUnion (fun _ => isOpen_iUnion (fun h => h.1)))

lemma regularRegion_subset (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : regularRegion u A U ⊆ U := by
  intro x hx
  obtain ⟨O,hx⟩ := mem_iUnion.mp hx
  obtain ⟨hOU,hx⟩ := mem_iUnion.mp hx
  obtain ⟨_,hx⟩ := mem_iUnion.mp hx
  exact hOU hx

lemma mem_regularRegion_iff {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {p : Coord3} : p ∈ regularRegion u A U ↔
    ∃ O : Set Coord3, O ⊆ U ∧ RegularPatch u A O ∧ p ∈ O := by
  simp only [regularRegion, mem_iUnion, exists_prop]

lemma exists_precompact_regular_patch {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {U : Set Coord3} {p : Coord3}
    (hp : p ∈ regularRegion u A U) :
    ∃ W : Set Coord3, p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧ RegularPatch u A W := by
  obtain ⟨O,hOU,hO,hpO⟩ := mem_regularRegion_iff.mp hp
  obtain ⟨W,hW,hpW,hWO,hWc⟩ := exists_precompact_open_inside hO.1 hpO
  exact ⟨W,hpW,hWO.trans hOU,hWc,hO.mono hW (subset_closure.trans hWO)⟩

end ScalarConductivity

end

end OAI
