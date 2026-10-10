import OAI.NumberTheory.CubicMoment.Estimates.PrimeGrouping

namespace OAI

/-! The uniform ordinary-block grouping gap away from the exceptional
three-prime configuration. All bounds come from finite-dimensional
compactness applied to the proved subset-sum alternative. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeGroupingGap (a : ι → ℝ) : ℝ :=
  (Finset.univ.powerset).sup' ⟨∅,by simp⟩
    (fun s => min ((∑ i ∈ s, a i)-1/3) (2/3-∑ i ∈ s, a i))

omit [DecidableEq ι] in
lemma continuous_primeGroupingGap : Continuous (primeGroupingGap (ι := ι)) := by
  apply Continuous.finset_sup'_apply
  intro s _hs
  apply Continuous.min <;> fun_prop

lemma primeGroupingGap_pos {a : ι → ℝ}
    (ha : ∀ i, 0 < a i ∧ a i < 2/3) (hsum : ∑ i, a i = 1)
    (hex : ¬(Fintype.card ι = 3 ∧ ∀ i, a i = 1/3)) : 0 < primeGroupingGap a := by
  obtain ⟨s,hs,hlo,hhi⟩ := (prime_exponent_partition Finset.univ a (fun i _ => ha i) hsum).resolve_right
    (by simpa using hex)
  apply lt_of_lt_of_le (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi))
  change min ((∑ i ∈ s, a i)-1/3) (2/3-∑ i ∈ s, a i) ≤
    (Finset.univ.powerset).sup' _ _
  exact Finset.le_sup' (fun t : Finset ι => min ((∑ i ∈ t, a i)-1/3)
    (2/3-∑ i ∈ t, a i)) (Finset.mem_powerset.mpr hs)

/-- The ordinary-configuration compactness argument, with an
explicit fixed neighborhood of the exceptional triple removed. -/
theorem uniform_prime_grouping_gap {ξ b δ : ℝ} (hξ : 0 < ξ)
    (hb : b < 2/3) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ι → ℝ,
      (∀ i, ξ ≤ a i ∧ a i ≤ b) → (∑ i, a i) = 1 →
      (Fintype.card ι = 3 → δ ≤ ∑ i, |a i-1/3|) →
      ∃ s : Finset ι, 1/3+ε ≤ ∑ i ∈ s, a i ∧ ∑ i ∈ s, a i ≤ 2/3-ε := by
  let K : Set (ι → ℝ) := {a | ∀ i, a i ∈ Icc ξ b} ∩
    {a | (∑ i, a i) = 1 ∧ (Fintype.card ι = 3 → δ ≤ ∑ i, |a i-1/3|)}
  have hsumClosed : IsClosed {a : ι → ℝ | (∑ i, a i) = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hdistClosed : IsClosed {a : ι → ℝ | Fintype.card ι = 3 → δ ≤ ∑ i, |a i-1/3|} := by
    by_cases hcard : Fintype.card ι = 3
    · simp only [hcard,true_implies]
      exact isClosed_le continuous_const (by fun_prop)
    · simp [hcard]
  have hK : IsCompact K :=
    (isCompact_pi_infinite (fun _ : ι => isCompact_Icc)).inter_right (hsumClosed.inter hdistClosed)
  have hpos : ∀ a ∈ K, 0 < primeGroupingGap a := by
    rintro a ⟨ha,hs,hd⟩
    apply primeGroupingGap_pos (fun i => ⟨hξ.trans_le (ha i).1,(ha i).2.trans_lt hb⟩) hs
    rintro ⟨hc,hthird⟩
    have hh := hd hc
    simp only [hthird,sub_self,abs_zero,Finset.sum_const_zero] at hh
    linarith
  obtain ⟨ε,hε,hbound⟩ := hK.exists_forall_le' continuous_primeGroupingGap.continuousOn hpos
  refine ⟨ε,hε,?_⟩
  intro a ha hs hd
  have h := hbound a ⟨ha,hs,hd⟩
  change ε ≤ (Finset.univ.powerset).sup' _ _ at h
  obtain ⟨s,_hs,hmin⟩ := (Finset.le_sup'_iff _).mp h
  exact ⟨s,by linarith [le_trans hmin (min_le_left _ _)],
    by linarith [le_trans hmin (min_le_right _ _)]⟩

end CubicFirstMoment

end

end OAI
