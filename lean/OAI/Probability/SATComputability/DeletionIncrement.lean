import OAI.Probability.SATComputability.VariableDeletion
import OAI.Probability.DilutedSpin.FiniteLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open DilutedSpinGlass
open scoped BigOperators

def allowedDeletions (n r : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter (fun D => D.card ≤ r)

theorem allowedDeletions_nonempty (n r : ℕ) : (allowedDeletions n r).Nonempty :=
  ⟨∅, by simp [allowedDeletions]⟩

noncomputable def bestDeletionTime {n : ℕ} (t : Finset (Fin n) → ℝ) (r : ℕ) : ℝ :=
  (allowedDeletions n r).sup' (allowedDeletions_nonempty n r) t

noncomputable def freeDeletionTime {n : ℕ} (t : Finset (Fin n) → ℝ)
    (r : ℕ) (v : Fin n) : ℝ :=
  (allowedDeletions n r).sup' (allowedDeletions_nonempty n r) (fun D => t (insert v D))

theorem bestDeletionTime_mono {n : ℕ} (t : Finset (Fin n) → ℝ) :
    Monotone (bestDeletionTime t) := by
  intro r s hrs
  apply Finset.sup'_le
  intro D hD
  apply Finset.le_sup'
  simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
  exact hD.trans hrs

theorem bestDeletionTime_le_free {n : ℕ} {t : Finset (Fin n) → ℝ}
    (ht : Monotone t) (r : ℕ) (v : Fin n) :
    bestDeletionTime t r ≤ freeDeletionTime t r v := by
  apply Finset.sup'_le
  intro D hD
  apply (ht (Finset.subset_insert v D)).trans
  exact Finset.le_sup' (fun E => t (insert v E)) hD

theorem freeDeletionTime_le_next {n : ℕ} (t : Finset (Fin n) → ℝ)
    (r : ℕ) (v : Fin n) :
    freeDeletionTime t r v ≤ bestDeletionTime t (r+1) := by
  apply Finset.sup'_le
  intro D hD
  apply Finset.le_sup'
  simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hD 1)

theorem freeDeletionTime_eq_at_max {n r : ℕ} (t : Finset (Fin n) → ℝ)
    (hr : 1 ≤ r) {D : Finset (Fin n)} (hD : D.card = r)
    (hmax : bestDeletionTime t r = t D) {v : Fin n} (hv : v ∈ D) :
    freeDeletionTime t (r-1) v = bestDeletionTime t r := by
  apply le_antisymm
  · simpa only [Nat.sub_add_cancel hr] using freeDeletionTime_le_next t (r-1) v
  · rw [hmax]
    have he : D.erase v ∈ allowedDeletions n (r-1) := by
      simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.card_erase_of_mem hv, hD, le_refl]
    have h := Finset.le_sup' (fun E => t (insert v E)) he
    simpa only [freeDeletionTime, Finset.insert_erase hv] using h

theorem deletion_increment_rpow {n r : ℕ} {t : Finset (Fin n) → ℝ}
    (ht : Monotone t) (hr : 1 ≤ r) {p : ℝ} (hp : 0 < p) :
    (r : ℝ) * (bestDeletionTime t r - bestDeletionTime t (r-1))^p ≤
      ∑ v : Fin n, (freeDeletionTime t (r-1) v - bestDeletionTime t (r-1))^p := by
  obtain ⟨D, hD, hmax⟩ := Finset.exists_mem_eq_sup'
    (allowedDeletions_nonempty n r) t
  change bestDeletionTime t r = t D at hmax
  have hcard : D.card ≤ r := by simpa only [allowedDeletions, Finset.mem_filter,
    Finset.mem_univ, true_and] using hD
  have hnonneg (v : Fin n) :
      0 ≤ freeDeletionTime t (r-1) v - bestDeletionTime t (r-1) :=
    sub_nonneg.mpr (bestDeletionTime_le_free ht (r-1) v)
  by_cases hsmall : D.card < r
  · have he : D ∈ allowedDeletions n (r-1) := by
      simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hle : bestDeletionTime t r ≤ bestDeletionTime t (r-1) := by
      rw [hmax]
      exact Finset.le_sup' t he
    have heq := le_antisymm hle (bestDeletionTime_mono t (Nat.sub_le r 1))
    rw [heq, sub_self, Real.zero_rpow hp.ne', mul_zero]
    exact Finset.sum_nonneg (fun v _ => Real.rpow_nonneg (hnonneg v) _)
  · have hcard' : D.card = r := by omega
    calc
      _ = ∑ v ∈ D, (bestDeletionTime t r - bestDeletionTime t (r-1))^p := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard']
      _ = ∑ v ∈ D, (freeDeletionTime t (r-1) v - bestDeletionTime t (r-1))^p := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [freeDeletionTime_eq_at_max t hr hcard' hmax hv]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        (fun v _ _ => Real.rpow_nonneg (hnonneg v) _)

theorem mean_deletion_increment {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {n r : ℕ} (t : Ω → Finset (Fin n) → ℝ) (ht : ∀ ω, Monotone (t ω))
    (hr : 1 ≤ r) {p C : ℝ} (hp : 1 ≤ p)
    (hmoment : ∀ v : Fin n, P.expect (fun ω =>
      (freeDeletionTime (t ω) (r-1) v - bestDeletionTime (t ω) (r-1))^p) ≤ C) :
    P.expect (fun ω => bestDeletionTime (t ω) r - bestDeletionTime (t ω) (r-1)) ≤
      ((n : ℝ) * C / r) ^ (1/p) := by
  let delta := fun ω => bestDeletionTime (t ω) r - bestDeletionTime (t ω) (r-1)
  have hd (ω : Ω) : 0 ≤ delta ω :=
    sub_nonneg.mpr (bestDeletionTime_mono (t ω) (Nat.sub_le r 1))
  have hpow : (r : ℝ) * P.expect (fun ω => (delta ω)^p) ≤ n*C := by
    have hi := P.expect_mono (fun ω => deletion_increment_rpow (ht ω) hr
      (show 0 < p by linarith))
    rw [FiniteLaw.expect_mul_left, FiniteLaw.expect_fintype_sum] at hi
    apply hi.trans
    have hs := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) =>
      hmoment v)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hi : P.expect (fun ω => (delta ω)^p) ≤ (n : ℝ)*C/r :=
    (le_div_iff₀ hr0).mpr (by simpa only [mul_comm] using hpow)
  have hm := Real.arith_mean_le_rpow_mean Finset.univ P.weight delta
    (fun ω _ => P.nonneg ω) P.total (fun ω _ => hd ω) hp
  change P.expect delta ≤ _ at hm
  apply hm.trans
  exact Real.rpow_le_rpow (P.expect_nonneg (fun ω => Real.rpow_nonneg (hd ω) p)) hi
    (by positivity)

end FixedClauseThreshold.Computability

end OAI
