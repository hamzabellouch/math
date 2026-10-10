import OAI.GroupTheory.PolycyclicRecognition.Algebra.UltrafilterIndexBound
import Mathlib.Order.Filter.AtTopBot.Finset

namespace OAI

/-! # Uniform local solvability and index bounds give global virtual solvability

The ultrafilter is only a compactness device. The finite-index and derived
length bounds remain explicit hypotheses of this supporting implication.
-/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G : Type} [Group G]

theorem uniformLocalVirtualSolvability (b r : ℕ)
    (hlocal : ∀ H : Subgroup G, H.FG → ∃ K : Subgroup H,
      K.FiniteIndex ∧ K.index ≤ b ∧ derivedSeries K r = ⊥) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ K.index ≤ b ∧ derivedSeries K r = ⊥ := by
  classical
  let H (S : Finset G) := Subgroup.closure (S : Set G)
  have hH (S : Finset G) : (H S).FG :=
    (Subgroup.fg_iff _).mpr ⟨S, rfl, S.finite_toSet⟩
  choose K hKi hKb hKr using (fun S => hlocal (H S) (hH S))
  let L (S : Finset G) := (K S).map (H S).subtype
  let U := Ultrafilter.of (atTop : Filter (Finset G))
  have hLr (S : Finset G) : derivedSeries (L S) r = ⊥ := by
    let e := (K S).equivMapOfInjective (H S).subtype Subtype.val_injective
    rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective r, hKr S, Subgroup.map_bot]
  obtain ⟨hI, hb⟩ := ultrafilterSubgroup_index U L b (fun f => by
    have hev : ∀ᶠ S : Finset G in U, Finset.univ.image f ⊆ S :=
      Ultrafilter.of_le (atTop : Filter (Finset G)) (eventually_finset_atTop_subset _)
    filter_upwards [hev] with S hS
    let fH : Fin (b + 1) → H S := fun i =>
      ⟨f i, Subgroup.subset_closure (hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
    let := hKi S
    obtain ⟨i, j, hij, hm⟩ := cosetCollisionBound_of_index (K S) b (hKb S) fH
    exact ⟨i, j, hij, ⟨(fH i)⁻¹ * fH j, hm, rfl⟩⟩)
  exact ⟨ultrafilterSubgroup U L, hI, hb, ultrafilterSubgroup_derivedSeries U L r hLr⟩

end PolycyclicRecognition

end

end OAI
