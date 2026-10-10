import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyBoundedDerivedSeries
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Finite

namespace OAI

/-! # Subgroup limits preserve a fixed derived-series bound -/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G I : Type} [Group G]

def ultrafilterSubgroup (U : Ultrafilter I) (K : I → Subgroup G) : Subgroup G where
  carrier := {g | ∀ᶠ i in U, g ∈ K i}
  one_mem' := Eventually.of_forall (fun i => (K i).one_mem)
  mul_mem' hx hy := by
    filter_upwards [hx, hy] with i hi hj
    exact (K i).mul_mem hi hj
  inv_mem' hx := by
    filter_upwards [hx] with i hi
    exact (K i).inv_mem hi

theorem ultrafilterSubgroup_fg_le_eventually (U : Ultrafilter I) (K : I → Subgroup G)
    (H : Subgroup G) (hH : H.FG) (hHK : H ≤ ultrafilterSubgroup U K) :
    ∀ᶠ i in U, H ≤ K i := by
  obtain ⟨S, hS, hSf⟩ := (Subgroup.fg_iff H).mp hH
  have hs : ∀ᶠ i in U, ∀ s ∈ S, s ∈ K i :=
    hSf.eventually_all.mpr (fun s hs => hHK (hS ▸ Subgroup.subset_closure hs))
  filter_upwards [hs] with i hi
  rw [← hS]
  exact (Subgroup.closure_le (K i)).mpr hi

theorem ultrafilterSubgroup_derivedSeries (U : Ultrafilter I) (K : I → Subgroup G)
    (r : ℕ) (hr : ∀ i, derivedSeries (K i) r = ⊥) :
    derivedSeries (ultrafilterSubgroup U K) r = ⊥ := by
  apply derivedSeries_eq_bot_of_fg_subgroups
  intro H hH
  let L := ultrafilterSubgroup U K
  let J := H.map L.subtype
  have hJ : J.FG := fg_subgroup_map hH L.subtype
  have hJL : J ≤ L := by rintro _ ⟨x, _, rfl⟩; exact x.property
  obtain ⟨i, hi⟩ := (ultrafilterSubgroup_fg_le_eventually U K J hJ hJL).exists
  let f : H →* K i := (L.subtype.comp H.subtype).codRestrict (K i)
    (fun x => hi ⟨x, x.property, rfl⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : K i => (x : G)) hab
  have hm := map_derivedSeries_le_derivedSeries f r
  rw [hr i] at hm
  have he : (derivedSeries H r).map f = ⊥ := eq_bot_iff.mpr hm
  rw [Subgroup.map_eq_bot_iff, f.ker_eq_bot hf] at he
  exact eq_bot_iff.mpr he

end PolycyclicRecognition

end

end OAI
