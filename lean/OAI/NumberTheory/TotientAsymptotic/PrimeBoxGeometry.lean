import OAI.NumberTheory.TotientAsymptotic.WitnessPrefix
import OAI.NumberTheory.TotientAsymptotic.GridVolume

namespace OAI

/-! The arithmetic prime boxes and their real double-logarithmic cells agree. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_unitPrimeBox_iff {p m : ℕ} :
    p ∈ unitPrimeBox m ↔ p.Prime ∧
      (m : ℝ)-1 ≤ Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) < m := by
  have hlog {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  constructor
  · intro hp
    obtain ⟨_, hp, hlo, hhi⟩ := Finset.mem_filter.mp hp
    refine ⟨hp, ?_, ?_⟩
    · have h1 := Real.log_le_log (Real.exp_pos _) hlo
      have h2 := Real.log_le_log (Real.exp_pos _) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
    · have h1 := Real.log_lt_log (by exact_mod_cast hp.pos) hhi
      have h2 := Real.log_lt_log (hlog hp) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
  · rintro ⟨hp, hlo, hhi⟩
    have hlo' : Real.exp (Real.exp ((m : ℝ)-1)) ≤ p := by
      have h1 := Real.exp_le_exp.mpr hlo
      have h2 := Real.exp_le_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    have hhi' : (p : ℝ) < Real.exp (Real.exp (m : ℝ)) := by
      have h1 := Real.exp_lt_exp.mpr hhi
      have h2 := Real.exp_lt_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hp, hlo', hhi'⟩
    exact_mod_cast hhi'.le.trans (Nat.le_ceil _)

lemma mem_primeBoxTuples_iff {N : ℕ} {p m : Fin N → ℕ} :
    p ∈ primeBoxTuples m ↔ (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ unitGridCell m := by
  simp only [primeBoxTuples, Fintype.mem_piFinset, mem_unitPrimeBox_iff,
    unitGridCell, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico,
    primePrefixCoord]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨hp, hu⟩ i
    exact ⟨hp i, hu i⟩

lemma mem_gridPrimeTuples_iff {N : ℕ} {K : Finset (Fin N → ℕ)} {p : Fin N → ℕ} :
    p ∈ gridPrimeTuples K ↔ (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ gridRegion K := by
  simp only [gridPrimeTuples, Finset.mem_biUnion, mem_primeBoxTuples_iff,
    gridRegion, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm, hp, hu⟩
    exact ⟨hp, m, hm, hu⟩
  · rintro ⟨hp, m, hm, hu⟩
    exact ⟨m, hm, hp, hu⟩

def gridInner {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    Finset (Fin N → ℕ) := K.filter (fun m => unitGridCell m ⊆ S)

def gridOuter {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    Finset (Fin N → ℕ) := K.filter (fun m => (unitGridCell m ∩ S).Nonempty)

def gridRestrictedPrimeMass {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) : ℝ :=
  ∑ p ∈ (gridPrimeTuples K).filter (fun p => primePrefixCoord p ∈ S), reciprocalShiftWeight p

lemma gridInner_subset_outer {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    gridInner K S ⊆ gridOuter K S := by
  intro m hm
  obtain ⟨hm, hs⟩ := Finset.mem_filter.mp hm
  have hc : (fun i => (m i : ℝ)-1) ∈ unitGridCell m := by
    intro i _
    constructor <;> linarith
  exact Finset.mem_filter.mpr ⟨hm, _, hc, hs hc⟩

lemma grid_prime_mass_sandwich {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    gridPrimeMass (gridInner K S) ≤ gridRestrictedPrimeMass K S ∧
      gridRestrictedPrimeMass K S ≤ gridPrimeMass (gridOuter K S) := by
  constructor
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨m, hm, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨hm, hs⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨m, hm, hp⟩,
        hs (mem_primeBoxTuples_iff.mp hp).2⟩
    · intro p _ _
      exact reciprocalShiftWeight_nonneg p
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨m, hm, hp⟩ := Finset.mem_biUnion.mp hp
      refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩, hp⟩
      exact ⟨primePrefixCoord p, (mem_primeBoxTuples_iff.mp hp).2, hs⟩
    · intro p _ _
      exact reciprocalShiftWeight_nonneg p

end TotientAsymptotic

end

end OAI
