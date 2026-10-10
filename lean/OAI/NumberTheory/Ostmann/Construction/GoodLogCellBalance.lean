import OAI.NumberTheory.Ostmann.Construction.BadLogCellCount
import OAI.NumberTheory.Ostmann.Construction.LogCellEvent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

lemma logCellWeight_active_le_cutoff {c : ℝ} {Q p : ℕ} (hp : p.Prime) (hQ : 0<Q)
    (hc : c+1≤Real.log (Q:ℝ)) (hw : logCellWeight c p≠0) : p≤Q := by
  have hφ : Ostmann.smoothPartition (Real.log p-c)≠0 := by
    intro hz
    exact hw (by simp only [logCellWeight,hz,zero_div])
  have hs := Ostmann.smoothPartition_support_subset hφ
  have hl : Real.log p≤Real.log (Q:ℝ) := by linarith [hs.2]
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (by exact_mod_cast hp.pos : (0:ℝ)<p),
    Real.exp_log (by exact_mod_cast hQ : (0:ℝ)<Q)] at he
  exact_mod_cast he

def unbalancedLogCellPrimes (d : Decomposition) (c : ℝ) (E : Finset ℕ) : Finset ℕ := by
  classical
  exact (logCellPrimes c\E).filter (fun p => ¬Supply.balancedDensity d p)

theorem logCell_bad_mass_le (d : Decomposition) (c : ℝ) (E : Finset ℕ) (Q : ℕ)
    (hQ : 0<Q) (hc : c+1≤Real.log (Q:ℝ)) :
    (c-1)*(∑p∈unbalancedLogCellPrimes d c E,logCellWeight c p)≤
      badLogCellMass d Q c := by
  classical
  let P := (logCellPrimes c\E).filter (fun p => ¬Supply.balancedDensity d p)
  let R := P.filter (fun p => logCellWeight c p≠0)
  have hsub : R⊆Supply.unbalancedPrimePrefix d Q := by
    intro p hp
    obtain ⟨hp,hw⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨logCellWeight_active_le_cutoff hprime hQ hc hw,hprime⟩,hbad⟩
  have heq : (∑p∈R,Real.log p*logCellWeight c p)=∑p∈P,Real.log p*logCellWeight c p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hz : logCellWeight c p=0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hp,hn⟩)
    rw [hz,mul_zero]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑p∈P,Real.log p*logCellWeight c p := Finset.sum_le_sum
      (fun p _ => (logCellWeight_log_sandwich c p).1)
    _ = ∑p∈R,Real.log p*logCellWeight c p := heq.symm
    _ ≤ ∑p∈Supply.unbalancedPrimePrefix d Q,Real.log p*logCellWeight c p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (Real.log_natCast_nonneg p) (logCellWeight_nonneg c p)
    _ = badLogCellMass d Q c := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold logCellWeight
      ring

theorem good_logCell_balanced_probability (d : Decomposition) (c : ℝ) (E : Finset ℕ)
    (Q : ℕ) (hQ : 0<Q) (hc : 2≤c) (hcover : c+1≤Real.log (Q:ℝ))
    (hZ : 0<logCellMass c E) (hinv : (logCellMass c E)⁻¹≤2*c)
    (hbad : badLogCellMass d Q c≤(1/8:ℝ)) :
    (1/2:ℝ)≤(logCellPrior c E hZ).mean (fun p => balancedPrimeIndicator d p) := by
  classical
  let B := ∑p∈(logCellPrimes c\E).filter (fun p => ¬Supply.balancedDensity d p),logCellWeight c p
  let A := ∑p∈(logCellPrimes c\E).filter (fun p => Supply.balancedDensity d p),logCellWeight c p
  have hB : 0≤B := Finset.sum_nonneg (fun p _ => logCellWeight_nonneg c p)
  have hb : (c-1)*B≤1/8 := (logCell_bad_mass_le d c E Q hQ hcover).trans hbad
  have hdiv : B/logCellMass c E≤(1/2:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hinv hB
    have hfactor : 2*c*B≤4*((c-1)*B) := by nlinarith
    rw [← div_eq_mul_inv] at hmul
    nlinarith
  have hsum : A+B=logCellMass c E := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  change (1/2:ℝ)≤(logCellPrior c E hZ).mean
    (fun p => if Supply.balancedDensity d p then 1 else 0)
  rw [logCellPrior_event_mean]
  apply (le_div_iff₀ hZ).mpr
  have hbZ := (div_le_iff₀ hZ).mp hdiv
  change (1/2:ℝ)*logCellMass c E≤A
  linarith

end Ostmann.Construction

end

end OAI
