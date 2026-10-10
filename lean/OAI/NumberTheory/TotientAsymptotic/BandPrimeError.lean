import OAI.NumberTheory.TotientAsymptotic.GridVolume
import OAI.NumberTheory.TotientAsymptotic.TailRenewal

namespace OAI

/-! A dimension-independent prime-box error from the retained lower bands. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma bandScale_lower {x : ℝ} (hs : 0 ≤ theta x) (i : ℕ) :
    lam*(m x-i : ℕ) ≤ bandScale x i := by
  have hα := alpha_ge_lam hs
  have hp : 1 ≤ (rho^(m x-i))⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  unfold bandScale
  calc
    _ ≤ alpha (theta x)*(m x-i : ℕ) :=
      mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _)) hp

lemma sum_reverse_geometric {m H : ℕ} (hHm : H ≤ m) (q : ℝ) :
    (∑ i : Fin (m-H), q^(m-(i.val+1))) =
      ∑ j ∈ Finset.range (m-H), q^(H+j) := by
  apply Finset.sum_bij (fun i _ => m-H-1-i.val)
  · intro i _
    exact Finset.mem_range.mpr (by omega)
  · intro i _ j _ hij
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨m-H-1-j, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro i _
    congr 1
    have := i.isLt
    omega

lemma sum_exp_neg_bandScale_le {x c : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hc : 0 < c) (hHm : H ≤ m x) :
    (∑ i : Fin (R x H), Real.exp (-c*bandScale x (i.val+1))) ≤
      Real.exp (-c*lam)^H/(1-Real.exp (-c*lam)) := by
  let q := Real.exp (-c*lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have hg := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑ i : Fin (R x H), q^(m x-(i.val+1)) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [q]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (bandScale_lower hs (i.val+1)) hc.le
      nlinarith
    _ = ∑ j ∈ Finset.range (m x-H), q^(H+j) := sum_reverse_geometric hHm q
    _ ≤ ∑' j : ℕ, q^(H+j) := (hg.comp_injective (fun _ _ h => by omega)).sum_le_tsum
      _ (fun _ _ => pow_nonneg hq0 _)
    _ = q^H/(1-q) := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rfl

def bandPrimeError (C c : ℝ) (H : ℕ) : ℝ :=
  Real.exp (C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))))-1

lemma bandPrimeError_tendsto (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (bandPrimeError C c) atTop (nhds 0) := by
  have hq : Real.exp (-c*lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq).div_const
    (1-Real.exp (-c*lam))
  have hh := ((Real.continuous_exp.tendsto (0 : ℝ)).comp (by
    simpa only [mul_zero, zero_div] using ht.const_mul C)).sub_const 1
  change Tendsto (fun H => Real.exp (C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))))-1)
    atTop (nhds 0)
  simpa only [Real.exp_zero, sub_self, Function.comp_def] using hh

/-- On any finite union of boxes above the retained lower bands, prime mass
and volume have a relative error tending to zero with the tail cut. The
bound is uniform in `x`, the number of prefix coordinates, and the phase. -/
theorem banded_grid_prime_mass_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x c : ℝ} {H : ℕ}, 0 ≤ theta x → 0 < c → H ≤ m x →
      ∀ K : Finset (Fin (R x H) → ℕ),
        (∀ b ∈ K, ∀ i, 1 ≤ b i ∧ c*bandScale x (i.val+1) ≤ b i) →
        |gridPrimeMass K-(MeasureTheory.volume (gridRegion K)).toReal| ≤
          (MeasureTheory.volume (gridRegion K)).toReal*bandPrimeError C c H := by
  obtain ⟨C, hC, hc⟩ := grid_prime_mass_error_of_sum hford
  refine ⟨C, hC, ?_⟩
  intro x c H hs hpos hHm K hK
  have he (b) (hb : b ∈ K) : (∑ i, Real.exp (-(b i : ℝ))) ≤
      Real.exp (-c*lam)^H/(1-Real.exp (-c*lam)) := by
    apply le_trans _ (sum_exp_neg_bandScale_le hs hpos hHm)
    exact Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by
      have := (hK b hb i).2
      linarith))
  simpa only [gridRegion_volume_real, bandPrimeError] using
    hc K (Real.exp (-c*lam)^H/(1-Real.exp (-c*lam)))
      (fun b hb i => (hK b hb i).1) he

end TotientAsymptotic

end

end OAI
