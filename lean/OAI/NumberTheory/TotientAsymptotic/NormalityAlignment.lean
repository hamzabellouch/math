import OAI.NumberTheory.TotientAsymptotic.PublishedComparison

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeFactor_le_largest {n p : ℕ} (hp : p ∈ n.primeFactorsList) :
    p ≤ largestPrimeFactor n := by
  have hm : p ∈ n.primeFactors := by
    change p ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hp
  exact (Finset.le_sup (f := id) hm).trans (le_max_right _ _)

lemma omegaIn_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (U T : ℝ) :
    omegaIn (n*m) U T = omegaIn n U T + omegaIn m U T := by
  unfold omegaIn
  have h := (Nat.perm_primeFactorsList_mul hn hm).filter
    (fun p : ℕ => decide (U < (p : ℝ) ∧ (p : ℝ) ≤ T))
  simpa using h.length_eq

lemma omegaIn_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (U T : ℝ) :
    omegaIn (∏ i ∈ s, f i) U T = ∑ i ∈ s, omegaIn (f i) U T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omegaIn]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      omegaIn_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma omegaIn_eq_zero_of_largest_le {n : ℕ} {U T : ℝ}
    (hn : (largestPrimeFactor n : ℝ) ≤ U) : omegaIn n U T = 0 := by
  unfold omegaIn
  have he : n.primeFactorsList.filter
      (fun p : ℕ => decide (U < (p : ℝ) ∧ (p : ℝ) ≤ T)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    intro h
    have hle : (p : ℝ) ≤ largestPrimeFactor n := by exact_mod_cast primeFactor_le_largest hp
    linarith [h.1]
  rw [he]
  rfl

lemma normality_interval_bounds {S U T ε : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hSU : S ≤ U) (hUT : U < T)
    (hTp : T ≤ (p-1 : ℕ)) (hε : Real.sqrt (B S * B T) ≤ ε) :
    B T-B U-ε ≤ (omegaIn (p-1) U T : ℝ) ∧
      (omegaIn (p-1) U T : ℝ) ≤ B T-B U+ε := by
  have h := abs_lt.mp (hp.2.2 U T hSU hUT hTp)
  constructor <;> linarith

/-- Equal products force close largest-factor locations. The left side has
`j+1` normal shifts reaching the interval, while only `j` right shifts can
reach it. Smooth residual factors contribute nothing. -/
theorem normality_alignment {k D D' : ℕ} (p q : Fin k → ℕ) (j : Fin k)
    {S U T ε : ℝ} (hD : D ≠ 0) (hD' : D' ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hprod : D * shiftedProduct p = D' * shiftedProduct q)
    (hDs : (largestPrimeFactor D : ℝ) ≤ U)
    (hD's : (largestPrimeFactor D' : ℝ) ≤ U)
    (hSU : S ≤ U) (hUT : U < T) (hε : Real.sqrt (B S * B T) ≤ ε)
    (hpT : ∀ i ≤ j, T ≤ (p i-1 : ℕ))
    (hqT : ∀ i < j, T ≤ (q i-1 : ℕ))
    (hqsmall : ∀ i, j ≤ i → (largestPrimeFactor (q i-1) : ℝ) ≤ U) :
    B T-B U ≤ (2*(j.val : ℝ)+1)*ε := by
  have hp0 (i : Fin k) : p i-1 ≠ 0 := by have := (hp i).1.two_le; omega
  have hq0 (i : Fin k) : q i-1 ≠ 0 := by have := (hq i).1.two_le; omega
  have hcount : (∑ i : Fin k, omegaIn (p i-1) U T) =
      ∑ i : Fin k, omegaIn (q i-1) U T := by
    have h := congrArg (fun n => omegaIn n U T) hprod
    unfold shiftedProduct at h
    rw [omegaIn_mul hD (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)),
      omegaIn_mul hD' (Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i)),
      omegaIn_eq_zero_of_largest_le hDs, omegaIn_eq_zero_of_largest_le hD's,
      zero_add, zero_add] at h
    simpa only [shiftedProduct, omegaIn_prod _ _ (fun i _ => hp0 i),
      omegaIn_prod _ _ (fun i _ => hq0 i)] using h
  have hcountR : (∑ i : Fin k, (omegaIn (p i-1) U T : ℝ)) =
      ∑ i : Fin k, (omegaIn (q i-1) U T : ℝ) := by exact_mod_cast hcount
  have hlo : ((j.val+1 : ℕ) : ℝ) * (B T-B U-ε) ≤
      ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) := by
    calc
      _ = ∑ _i ∈ Finset.Iic j, (B T-B U-ε) := by simp [Fin.card_Iic]; ring
      _ ≤ ∑ i ∈ Finset.Iic j, (omegaIn (p i-1) U T : ℝ) := by
        exact Finset.sum_le_sum (fun i hi =>
          (normality_interval_bounds (hp i) hSU hUT (hpT i (Finset.mem_Iic.mp hi)) hε).1)
      _ ≤ ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => Nat.cast_nonneg _)
  have hhi : (∑ i : Fin k, (omegaIn (q i-1) U T : ℝ)) ≤
      (j.val : ℝ) * (B T-B U+ε) := by
    calc
      _ = ∑ i ∈ Finset.Iio j, (omegaIn (q i-1) U T : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hji : j ≤ i := le_of_not_gt (by simpa using hi)
        rw [omegaIn_eq_zero_of_largest_le (hqsmall i hji), Nat.cast_zero]
      _ ≤ ∑ _i ∈ Finset.Iio j, (B T-B U+ε) :=
        Finset.sum_le_sum (fun i hi =>
          (normality_interval_bounds (hq i) hSU hUT (hqT i (Finset.mem_Iio.mp hi)) hε).2)
      _ = _ := by simp [Fin.card_Iio]; ring
  rw [hcountR] at hlo
  push_cast at hlo
  nlinarith

end TotientAsymptotic

end

end OAI
