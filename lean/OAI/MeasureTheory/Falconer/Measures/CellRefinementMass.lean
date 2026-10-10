import OAI.MeasureTheory.Falconer.Estimates.RegularCoarseCells

namespace OAI

/-! Uniform coarse-cell occupancy converts a retained proportion of cells
and a retained proportion inside each cell into original fine-point mass. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cell_refinement_mass {J L F w : ℝ}
    (hJ : 0 ≤ J) (hL : 0 ≤ L) (_hF : 0 ≤ F) (hw : 0 ≤ w)
    (P C R : Finset (Space 2)) (q : Space 2 → Space 2)
    (A : Space 2 → Finset (Space 2)) (hRC : R ⊆ C)
    (hmass : (P.card:ℝ) ≤ J*∑ c ∈ C, ((P.filter fun p => q p = c).card:ℝ))
    (hband : ∀ c ∈ C, w ≤ ((P.filter fun p => q p = c).card:ℝ) ∧
      ((P.filter fun p => q p = c).card:ℝ) ≤ 2*w)
    (hcount : (C.card:ℝ) ≤ L*(R.card:ℝ))
    (hA : ∀ c ∈ R, A c ⊆ P.filter (fun p => q p = c) ∧
      ((P.filter fun p => q p = c).card:ℝ) ≤ F*((A c).card:ℝ)) :
    R.biUnion A ⊆ P ∧ (P.card:ℝ) ≤ (2*J*L*F)*((R.biUnion A).card:ℝ) := by
  have hsub : R.biUnion A ⊆ P := by
    intro p hp
    obtain ⟨c,hc,hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp ((hA c hc).1 hp)).1
  have hd : (R : Set (Space 2)).PairwiseDisjoint A := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro p hpc hpd
    have hqc := (Finset.mem_filter.mp ((hA c hc).1 hpc)).2
    have hqd := (Finset.mem_filter.mp ((hA d hd).1 hpd)).2
    exact hcd (hqc.symm.trans hqd)
  have hcard : ((R.biUnion A).card:ℝ) = ∑ c ∈ R, ((A c).card:ℝ) := by
    exact_mod_cast Finset.card_biUnion hd
  have hlocal : w*(R.card:ℝ) ≤ F*((R.biUnion A).card:ℝ) := by
    calc
      _ = ∑ _c ∈ R, w := by simp; ring
      _ ≤ ∑ c ∈ R, F*((A c).card:ℝ) := Finset.sum_le_sum fun c hc =>
        ((hband c (hRC hc)).1.trans (hA c hc).2)
      _ = _ := by rw [← Finset.mul_sum,hcard]
  refine ⟨hsub,?_⟩
  calc
    (P.card:ℝ) ≤ J*∑ c ∈ C, ((P.filter fun p => q p = c).card:ℝ) := hmass
    _ ≤ J*∑ _c ∈ C, 2*w := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun c hc => (hband c hc).2) hJ
    _ = 2*J*w*(C.card:ℝ) := by simp; ring
    _ ≤ 2*J*w*(L*(R.card:ℝ)) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (2*J*L)*(w*(R.card:ℝ)) := by ring
    _ ≤ (2*J*L)*(F*((R.biUnion A).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by ring

end Falconer

end OAI
