import OAI.NumberTheory.Ostmann.Preliminaries.SieveWeightMoment

namespace OAI

/-! # Retaining short squarefree products in the fixed-shift sieve -/

namespace Ostmann

open scoped Classical BigOperators

 theorem finite_weight_truncation {ι : Type*} (S : Finset ι) (w cost : ι → ℝ)
    (L : ℝ) (hL : 0 < L) (hw : ∀ s ∈ S, 0 ≤ w s) (hc : ∀ s ∈ S, 0 ≤ cost s)
    (hmean : (∑ s ∈ S, w s * cost s) ≤ (L / 2) * ∑ s ∈ S, w s) :
    (∑ s ∈ S, w s) / 2 ≤ ∑ s ∈ S.filter (fun s => cost s ≤ L), w s := by
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun s => cost s ≤ L) w
  have hbad : L * (∑ s ∈ S.filter (fun s => ¬ cost s ≤ L), w s) ≤
      ∑ s ∈ S, w s * cost s := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ s ∈ S.filter (fun s => ¬ cost s ≤ L), w s * cost s := by
        apply Finset.sum_le_sum
        intro s hs
        have hs' := Finset.mem_filter.mp hs
        have hlt : L < cost s := lt_of_not_ge hs'.2
        nlinarith [hw s hs'.1]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun s hs _ => mul_nonneg (hw s hs) (hc s hs))
  nlinarith

 theorem fixed_shift_short_weight (P : Finset ℕ) (j Q : ℝ)
    (hj : 0 ≤ j) (hQ : 1 < Q) (hP : ∀ p ∈ P, j < (p : ℝ))
    (hmean : j * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ Real.log Q / 2) :
    ((∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j)) / 2) ≤
      ∑ U ∈ P.powerset.filter (fun U : Finset ℕ => (∑ p ∈ U, Real.log (p : ℝ)) ≤ Real.log Q),
        ∏ p ∈ U, j / ((p : ℝ) - j) := by
  have hfactor (p : ℕ) (hp : p ∈ P) :
      1 + j / ((p : ℝ) - j) = (p : ℝ) / ((p : ℝ) - j) := by
    have hn : (p : ℝ) - j ≠ 0 := ne_of_gt (sub_pos.mpr (hP p hp))
    field_simp [hn]
    ring
  have hmass : (∑ U ∈ P.powerset, ∏ p ∈ U, j / ((p : ℝ) - j)) =
      ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) := by
    rw [sieve_weight_mass]
    exact Finset.prod_congr rfl hfactor
  have hweight (U : Finset ℕ) (hU : U ∈ P.powerset) :
      0 ≤ ∏ p ∈ U, j / ((p : ℝ) - j) := by
    exact Finset.prod_nonneg (fun p hp => div_nonneg hj
      (sub_pos.mpr (hP p (Finset.mem_powerset.mp hU hp))).le)
  have hcost (U : Finset ℕ) (hU : U ∈ P.powerset) :
      0 ≤ ∑ p ∈ U, Real.log (p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    have hp' : (0 : ℝ) < p := lt_of_le_of_lt hj (hP p (Finset.mem_powerset.mp hU hp))
    have hpN : 1 ≤ p := by
      have hpNat : 0 < p := by exact_mod_cast hp'
      omega
    exact Real.log_nonneg (by exact_mod_cast hpN)
  have hmass0 : 0 ≤ ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) :=
    Finset.prod_nonneg (fun p hp => div_nonneg (Nat.cast_nonneg p) (sub_pos.mpr (hP p hp)).le)
  have hm : (∑ U ∈ P.powerset,
      (∏ p ∈ U, j / ((p : ℝ) - j)) * ∑ p ∈ U, Real.log (p : ℝ)) ≤
      (Real.log Q / 2) * ∑ U ∈ P.powerset, ∏ p ∈ U, j / ((p : ℝ) - j) := by
    rw [fixed_shift_weight_moment P j hj hP, hmass]
    nlinarith [mul_le_mul_of_nonneg_left hmean hmass0]
  have h := finite_weight_truncation P.powerset
    (fun U => ∏ p ∈ U, j / ((p : ℝ) - j)) (fun U => ∑ p ∈ U, Real.log (p : ℝ))
    (Real.log Q) (Real.log_pos hQ) hweight hcost hm
  rwa [hmass] at h

end Ostmann

end OAI
