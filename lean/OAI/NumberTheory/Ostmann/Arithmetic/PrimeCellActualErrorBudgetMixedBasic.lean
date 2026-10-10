import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetPrime

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget LogCellPartition Filter

theorem integerDensityMass_abs_le (M : ℕ) (hM : 0 < M)
    {lo hi G B : ℝ} (φ : ℝ → ℝ) (horder : lo ≤ hi) (hwidth : hi-lo ≤ 1)
    (hwindow : hi ≤ G+1) (hB : 0 ≤ B)
    (hφ : ∀ t ∈ Set.Icc lo hi, |φ (t-G)| ≤ B) :
    |IntegerCell.integerDensityMass M lo hi G φ| ≤ Real.exp 1*B := by
  have hbound (t : ℝ) (ht : t ∈ Set.uIoc lo hi) :
      ‖Real.exp (t-G)*φ (t-G)‖ ≤ Real.exp 1*B := by
    rw [Set.uIoc_of_le horder] at ht
    rw [Real.norm_eq_abs,abs_mul,Real.abs_exp]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht.2]))
      (hφ t ⟨ht.1.le,ht.2⟩) (abs_nonneg _) (Real.exp_nonneg _)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr horder)] at hh
  have hh' : |∫ t in lo..hi, Real.exp (t-G)*φ (t-G)| ≤ Real.exp 1*B :=
    hh.trans (by simpa using mul_le_mul_of_nonneg_left hwidth (mul_nonneg (Real.exp_nonneg _) hB))
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
  rw [IntegerCell.integerDensityMass,abs_div,abs_of_pos hMp]
  apply (div_le_iff₀ hMp).mpr
  exact hh'.trans (le_mul_of_one_le_right (mul_nonneg (Real.exp_nonneg _) hB) hM1)

def primeEnvelope (r : Row) (k : ℕ) (C K d L : ℝ) : ℝ :=
  (K+1)*Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)-min d 1*Real.exp ((r.a₀/3)*L))

theorem correctedPrimeError_le_envelope (r : Row) (k : ℕ) {C K d L lower Z : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hL : 0 ≤ L)
    (hlower : Real.exp (r.a₀*L) ≤ lower) (hZ : 0 < Z)
    (hZi : Z⁻¹ ≤ Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1))) :
    correctedPrimeError K d lower Z ≤ primeEnvelope r k C K d L :=
  correctedPrimeError_le hK (le_min hd.le (by norm_num)) (min_le_left d 1) (min_le_right d 1)
    (row_a₀_pos r).le hL hlower hZ hZi

def dimensionCoefficient (k : ℕ) : ℝ := 2*((2:ℝ)^k+2)

theorem tensor_two_factors_le (k n : ℕ) (L σ : ℝ)
    (hn : n ≤ 2^k*Conclusion.bulkSize k L+2) :
    (2:ℝ)^n ≤ smoothGrowthFactor k (dimensionCoefficient k) σ L ∧
      (n:ℝ)*2^n ≤ smoothGrowthFactor k (dimensionCoefficient k) σ L := by
  have hn' : (n:ℝ) ≤ ((2:ℝ)^k+2)*((Conclusion.bulkSize k L:ℝ)+1) := by
    have hh : (n:ℝ) ≤ (2:ℝ)^k*(Conclusion.bulkSize k L:ℝ)+2 := by exact_mod_cast hn
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) k]
  have htwo : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
      (by linarith [Real.add_one_le_exp 1] : (2:ℝ)≤Real.exp 1) n
    simpa only [← Real.exp_nat_mul,mul_one] using hh
  have hnexp : (n:ℝ) ≤ Real.exp (n:ℝ) := by linarith [Real.add_one_le_exp (n:ℝ)]
  have hfinal : Real.exp (2*(n:ℝ)) ≤ smoothGrowthFactor k (dimensionCoefficient k) σ L := by
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ dimensionCoefficient k*((Conclusion.bulkSize k L:ℝ)+1) := by
      unfold dimensionCoefficient
      positivity
    have he := mul_nonneg hc (Real.exp_nonneg (σ*L))
    unfold dimensionCoefficient at *
    nlinarith
  constructor
  · exact htwo.trans ((Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg n (α:=ℝ)] : (n:ℝ)≤2*(n:ℝ))).trans hfinal)
  · apply le_trans (mul_le_mul hnexp htwo (by positivity) (Real.exp_nonneg _))
    rw [← Real.exp_add]
    simpa only [two_mul] using hfinal

lemma smoothGrowthFactor_mul (k : ℕ) (C D σ L : ℝ) :
    smoothGrowthFactor k C σ L*smoothGrowthFactor k D σ L = smoothGrowthFactor k (C+D) σ L := by
  unfold smoothGrowthFactor
  rw [← Real.exp_add]
  congr 1
  ring

lemma smoothGrowth_mul_normalizer_le_add (k : ℕ) {C D σ L : ℝ} (hC : 0 ≤ C) :
    smoothGrowthFactor k D σ L*Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)) ≤
      smoothGrowthFactor k (D+C) σ L := by
  unfold smoothGrowthFactor
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : 0 ≤ C*((Conclusion.bulkSize k L:ℝ)+1)*Real.exp (σ*L) := by positivity
  nlinarith only [hh]

theorem eventually_primeEnvelope_budget (r : Row) (k : ℕ)
    {C D A K d σ : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hK : 0 ≤ K) (hd : 0 < d)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ r.δ) :
    ∀ᶠ L : ℝ in atTop, ∀ n M : ℕ,
      n ≤ 2^k*Conclusion.bulkSize k L+2 → 0 < M → Real.log (M:ℝ) ≤ Real.exp (r.μ*L) →
      jointMeshFactor r L n M*smoothGrowthFactor k D σ L*A*primeEnvelope r k C K d L ≤
        Real.exp (-Real.exp (r.target*L)) := by
  filter_upwards [eventually_weighted_progression_decay r k (D+C) (A*(K+1))
    hσ0 hσ (show 0 < min d 1 from lt_min hd (by norm_num))] with L hL
  intro n M hn hM hmod
  have hfac : 0 ≤ jointMeshFactor r L n M := by unfold jointMeshFactor; positivity
  calc
    _ = jointMeshFactor r L n M*
        (smoothGrowthFactor k D σ L*Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)))*
        (A*(K+1))*Real.exp (-min d 1*Real.exp ((r.a₀/3)*L)) := by
      unfold primeEnvelope
      rw [sub_eq_add_neg,Real.exp_add,← neg_mul]
      ring
    _ ≤ jointMeshFactor r L n M*smoothGrowthFactor k (D+C) σ L*
        (A*(K+1))*Real.exp (-min d 1*Real.exp ((r.a₀/3)*L)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (smoothGrowth_mul_normalizer_le_add k hC) hfac) (by positivity)
    _ ≤ _ := hL n M hn hM hmod

end Ostmann.Arithmetic.PrimeCellActualErrorBudget

end

end OAI
