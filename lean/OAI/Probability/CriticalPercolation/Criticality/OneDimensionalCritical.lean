import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.HeightCuts
import OAI.Probability.CriticalPercolation.ProductMeasure.ClosedCutProbability

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma spaced_integer_levels (J n m : ℕ) (hnm : n≠m) :
    (J:ℤ) ≤ |(n:ℤ)*(J+1)-(m:ℤ)*(J+1)| := by
  have hne : (n:ℤ)-(m:ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hpos : 1 ≤ |(n:ℤ)-(m:ℤ)| := Int.add_one_le_iff.mpr (abs_pos.mpr hne)
  rw [← sub_mul,abs_mul,abs_of_nonneg (by omega : (0:ℤ)≤(J:ℤ)+1)]
  nlinarith [Int.natCast_nonneg J]

theorem proper_integer_height_percolates_null (hlocal : G.LocallyFinite)
    (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t)
    (p : unitInterval) (hp : (p:ℝ)<1) : G.law p G.percolates = 0 := by
  let Cpos : ℕ → Set E := fun n => G.heightCut π ((n:ℤ)*(J+1))
  let Cneg : ℕ → Set E := fun n => G.heightCut π (-((n:ℤ)*(J+1)))
  have hpdis : Pairwise (fun n m => Disjoint (Cpos n) (Cpos m)) := by
    intro n m hnm
    exact G.heightCut_disjoint π J hJ _ _ (spaced_integer_levels J n m hnm)
  have hmdis : Pairwise (fun n m => Disjoint (Cneg n) (Cneg m)) := by
    intro n m hnm
    apply G.heightCut_disjoint π J hJ
    rw [neg_sub_neg,abs_sub_comm]
    exact spaced_integer_levels J n m hnm
  have hplus := BernoulliProduct.frequently_closedBlock_ae p hp Cpos
    (fun n => G.finite_heightCut hlocal π hπ J hJ _) hpdis (G.heightCut π 0).ncard
    (fun n => G.heightCut_ncard π htrans _)
  have hminus := BernoulliProduct.frequently_closedBlock_ae p hp Cneg
    (fun n => G.finite_heightCut hlocal π hπ J hJ _) hmdis (G.heightCut π 0).ncard
    (fun n => G.heightCut_ncard π htrans _)
  rw [BernoulliProduct.law_const] at hplus hminus
  have hno : ∀ᵐ ω ∂G.law p, ω ∉ G.percolates := by
    filter_upwards [hplus,hminus] with ω hpω hmω
    rintro ⟨o,ho⟩
    obtain ⟨n,hn,hncut⟩ := Filter.frequently_atTop.mp hpω ((π o).natAbs+1)
    obtain ⟨m,hm,hmcut⟩ := Filter.frequently_atTop.mp hmω ((π o).natAbs+1)
    have hno : π o ≤ (n:ℤ)*(J+1) := by
      have habs : π o ≤ ((π o).natAbs : ℤ) := Int.le_natAbs
      have hh : (π o).natAbs+1 ≤ (n:ℤ) := by exact_mod_cast hn
      have hprod : (n:ℤ) ≤ (n:ℤ)*(J+1) := by nlinarith [Int.natCast_nonneg n,Int.natCast_nonneg J]
      omega
    have hmo : -((m:ℤ)*(J+1)) < π o := by
      have habs : -((π o).natAbs : ℤ) ≤ π o := by
        simpa only [Int.natCast_natAbs] using neg_abs_le (π o)
      have hh : (π o).natAbs+1 ≤ (m:ℤ) := by exact_mod_cast hm
      have hprod : (m:ℤ) ≤ (m:ℤ)*(J+1) := by nlinarith [Int.natCast_nonneg m,Int.natCast_nonneg J]
      omega
    exact ho ((finite_height_interval π hπ _ _).subset
      (G.cluster_bounded_by_closed_cuts π ω _ _ hmcut hncut o hmo hno))
  rw [ae_iff] at hno
  simpa only [not_not,Set.ofPred_mem_eq] using hno

theorem proper_integer_height_critical_one (hlocal : G.LocallyFinite)
    (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t) :
    G.criticalProbability=1 := by
  apply le_antisymm le_top
  apply le_sInf
  intro p hp
  by_contra h
  have hlt : (p:ℝ)<1 := lt_of_not_ge h
  have hz := G.proper_integer_height_percolates_null hlocal π hπ J hJ htrans p hlt
  exact (ne_of_gt hp) hz

end CriticalPercolation.BondGraph
end
end
end

end OAI
