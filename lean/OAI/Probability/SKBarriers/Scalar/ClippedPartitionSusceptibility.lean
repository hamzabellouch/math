import Mathlib
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Hierarchy.HierarchyAtomCoordinates

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_eq_clipped_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (m : Fin n → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmm : Monotone m)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β α r=
      1-∑ j, hierarchyAtom n m 1 j*scalarCDFOverlap β α (max (q j) r) := by
  let p := fun i => min (q i) r
  let s := fun i => max (q i) r
  have hp : Monotone p := fun i j hij => min_le_min_right _ (hq hij)
  have hs : Monotone s := fun i j hij => max_le_max_right _ (hq hij)
  have hp0 : p 0=0 := by simp only [p,hq0,min_eq_left hr.1]
  have hs1 : s (Fin.last n)=1 := by simp only [s,hq1,max_eq_left hr.2]
  have hp1 : p (Fin.last n)=r := by simp only [p,hq1,min_eq_right hr.2]
  have hs0 : s 0=r := by simp only [s,hq0,max_eq_right hr.1]
  have hmp (i : Fin n) (z : ℝ) (hz : z∈Ico (p i.castSucc) (p i.succ)) : α z=m i := by
    apply hmodel i z
    change min (q i.castSucc) r ≤ z ∧ z < min (q i.succ) r at hz
    have hzr : z  <  r := (lt_min_iff.mp hz.2).2
    have hzq : z < q i.succ := (lt_min_iff.mp hz.2).1
    have hl : q i.castSucc ≤ z := by
      by_cases h : q i.castSucc ≤  r
      · simpa only [min_eq_left h] using hz.1
      · rw [min_eq_right (le_of_not_ge h)] at hz
        linarith [hz.1]
    exact ⟨hl,hzq⟩
  have hms (i : Fin n) (z : ℝ) (hz : z∈Ico (s i.castSucc) (s i.succ)) : α z=m i := by
    apply hmodel i z
    change max (q i.castSucc) r ≤ z ∧ z < max (q i.succ) r at hz
    have hzr : r ≤ z := (max_le_iff.mp hz.1).2
    have hl : q i.castSucc ≤ z := (max_le_iff.mp hz.1).1
    have hu : z < q i.succ := by
      rcases lt_max_iff.mp hz.2 with h|h
      · exact h
      · linarith
    exact ⟨hl,hu⟩
  have H := scalarCDFSusceptibilityAverage_eq_partition β hα hαm n n p s hp hs hp0 hs1
    (hp1.trans hs0.symm) m m hm hm hmm hmp hms
  rwa [hs0] at H

theorem scalarCDFSusceptibilityAverage_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β (quantileCDF k Q) r=
      1-(1/(k+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF k Q) (max (Q j) r) := by
  let q := Fin.snoc (α := fun _ => ℝ) (Fin.cons (α := fun _ => ℝ) 0 Q) (1:ℝ)
  let m := Fin.snoc (α := fun _ => ℝ) (quantileMass k) (1:ℝ)
  have hq : Monotone q := monotone_snoc_one _
    (monotone_cons_zero_quantiles Q hQ.1 (hQ.2 0).1) (by simpa using (hQ.2 (Fin.last k)).2)
  have hq0 : q 0=0 := by simp [q]
  have hq1 : q (Fin.last (k+2))=1 := by simp [q]
  have hm (i : Fin (k+2)) : m i ∈ Icc (0:ℝ) 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [m]
    · simpa [m] using quantileMass_bounds k i
  have hmm : Monotone m := monotone_snoc_one _ (monotone_quantileMass k)
    (quantileMass_bounds k (Fin.last k)).2
  have hmodel (i : Fin (k+2)) (z : ℝ) (hz : z ∈ Ico (q i.castSucc) (q i.succ)) :
      quantileCDF k Q z=m i := by
    revert hz
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hz
      simp only [m,Fin.snoc_last]
      apply quantileCDF_of_last_le Q hQ.1
      simpa [q] using hz.1
    · intro hz
      simpa [m] using quantileCDF_on_interval Q hQ.1 i z (by
        simpa only [q,← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.cons_succ] using hz)
  rw [scalarCDFSusceptibilityAverage_eq_clipped_partition β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) (k+2) q hq hq0 hq1 m hm hmm hmodel hr]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hA (j : Fin (k+2)) : hierarchyAtom (k+2) m 1 j.castSucc=
      hierarchyAtom (k+1) (quantileMass k) 1 j := by
    rw [hierarchyAtom,Fin.lastCases_castSucc]
    simp only [m,Fin.snoc_castSucc,Fin.snoc_last]
  have hlast : hierarchyAtom (k+2) m 1 (Fin.last (k+2))=0 := by
    rw [hierarchyAtom,Fin.lastCases_last]
    simp only [m,Fin.snoc_last,sub_self]
  simp only [hA,hlast,zero_mul,add_zero]
  rw [Fin.sum_univ_succ,hierarchyAtom_zero_coordinate]
  simp only [quantileMass,Fin.val_zero,Nat.cast_zero,zero_div,zero_mul,zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hierarchyAtom_quantile_succ]
  simp only [q,Fin.snoc_castSucc,Fin.cons_succ]

end SK.Analytic

end
end

end OAI
