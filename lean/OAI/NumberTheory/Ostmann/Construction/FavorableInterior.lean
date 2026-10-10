import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelectionFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

def interiorFavorable (S : Finset ℕ) (L : ℝ) : Finset ℕ :=
  S ∩ logLogPrimeBand ((3/50:ℝ)*L) ((89/100:ℝ)*L)

theorem favorable_band_cover (S : Finset ℕ) {L : ℝ} (hL : 0<L)
    (hS : ∀p∈S,p.Prime ∧ (1/20:ℝ)*L≤Real.log (Real.log p) ∧
      Real.log (Real.log p)≤(9/10:ℝ)*L) :
    S⊆(interiorFavorable S L ∪ logLogPrimeBand ((1/25:ℝ)*L) ((3/50:ℝ)*L)) ∪
      logLogPrimeBand ((89/100:ℝ)*L) ((91/100:ℝ)*L) := by
  intro p hp
  obtain ⟨hprime,hlo,hhi⟩ := hS p hp
  by_cases hin : p∈logLogPrimeBand ((3/50:ℝ)*L) ((89/100:ℝ)*L)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp,hin⟩))
  by_cases hlow : Real.log (Real.log p)≤(3/50:ℝ)*L
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact (logLogPrimeBand_mem_iff _ _ _).mpr ⟨hprime,by linarith,hlow⟩
  · apply Finset.mem_union_right
    apply (logLogPrimeBand_mem_iff _ _ _).mpr
    refine ⟨hprime,?_,by linarith⟩
    by_contra h
    exact hin ((logLogPrimeBand_mem_iff _ _ _).mpr ⟨hprime,lt_of_not_ge hlow,le_of_not_gt h⟩)

theorem interiorFavorable_mass_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℕ,
      (∀p∈S,p.Prime ∧ (1/20:ℝ)*L≤Real.log (Real.log p) ∧
        Real.log (Real.log p)≤(9/10:ℝ)*L) →
      (3/20:ℝ)*L≤harmonicPrimeMass S →
      (21/200:ℝ)*L≤harmonicPrimeMass (interiorFavorable S L) := by
  obtain ⟨C,hC,hM⟩ := logLogPrimeBand_mass_error
  filter_upwards [eventually_ge_atTop (max 1 (400*C))] with L hL
  have hL1 : 1≤L := (le_max_left _ _).trans hL
  have hLC : 400*C≤L := (le_max_right _ _).trans hL
  intro S hS hmass
  have hlo := hM ((1/25:ℝ)*L) ((3/50:ℝ)*L) (by positivity) (by nlinarith) ∅ (by simp)
  have hhi := hM ((89/100:ℝ)*L) ((91/100:ℝ)*L) (by positivity) (by nlinarith) ∅ (by simp)
  simp only [Finset.sdiff_empty] at hlo hhi
  have hcover := Ostmann.Supply.harmonicPrimeMass_mono (favorable_band_cover S (by linarith) hS)
  have hu₁ := Ostmann.Supply.harmonicPrimeMass_union_le
    (interiorFavorable S L ∪ logLogPrimeBand ((1/25:ℝ)*L) ((3/50:ℝ)*L))
    (logLogPrimeBand ((89/100:ℝ)*L) ((91/100:ℝ)*L))
  have hu₂ := Ostmann.Supply.harmonicPrimeMass_union_le (interiorFavorable S L)
    (logLogPrimeBand ((1/25:ℝ)*L) ((3/50:ℝ)*L))
  have hlow := (abs_le.mp hlo).2
  have hhigh := (abs_le.mp hhi).2
  linarith

end Ostmann.Construction

end

end OAI
