import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetMixedBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget LogCellPartition Filter

theorem mixedGridError_le_two_parts {ι : Type*} [Fintype ι]
    (M : ℕ) (hM : 0 < M) {lo hi η G B D a L ε : ℝ} (φ : ℝ → ℝ)
    (j : Fin (gridCount lo hi η)) (horder : lo ≤ hi) (hη : 0 < η) (hη1 : η ≤ 1)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hwindow : hi ≤ G+1) (hG : Real.exp (a*L) ≤ G)
    (hφ : ∀ t ∈ Set.Icc lo hi, |φ (t-G)| ≤ B) (hε : 0 ≤ ε) :
    mixedGridError (ι:=ι) M lo hi η G B D φ ε 2 j ≤
      (6*B+2*D)*Real.exp (-Real.exp (a*L))*2^Fintype.card ι+
      (Real.exp 1*B+(6*B+2*D))*((Fintype.card ι:ℝ)*2^Fintype.card ι)*ε := by
  have hl := gridPoint_mem (η:=η) horder j.isLt.le
  have hu := gridPoint_mem (η:=η) horder (show j.val+1≤gridCount lo hi η by omega)
  have hwidth : gridPoint lo hi η (j.val+1)-gridPoint lo hi η j.val ≤ 1 :=
    (gridPoint_width lo hi η j.val).trans_le ((gridStep_le horder hη).trans hη1)
  have hJ := integerDensityMass_abs_le M hM φ (gridPoint_mono horder (Nat.le_succ _)) hwidth
    (hu.2.trans hwindow) hB (fun t ht => hφ t ⟨hl.1.trans ht.1,ht.2.trans hu.2⟩)
  have hEI := mixedGridIntegerError_le j hB hD hwidth hG
  have hq : Real.exp (-Real.exp (a*L)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _))
  have hsmall : mixedGridIntegerError lo hi η G B D j ≤ 6*B+2*D :=
    hEI.trans (by simpa using mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 6*B+2*D))
  unfold mixedGridError
  calc
    _ ≤ ((6*B+2*D)*Real.exp (-Real.exp (a*L))+
        (Real.exp 1*B+(6*B+2*D))*(Fintype.card ι:ℝ)*ε)*2^Fintype.card ι := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add hEI (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add hJ hsmall) (Nat.cast_nonneg _)) hε)
    _ = _ := by ring

theorem eventually_mixedGridError_budget (r : Row) (k : ℕ)
    {C K d B D σ : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : 0 < d)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hσ0 : 0 ≤ σ) (hσ : σ ≤ r.δ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (ι : Type*) [Fintype ι] (M : ℕ) (lo hi η G : ℝ) (φ : ℝ → ℝ)
        (j : Fin (gridCount lo hi η)),
        Fintype.card ι+1 ≤ 2^k*Conclusion.bulkSize k L+2 → 0 < M →
        Real.log (M:ℝ) ≤ Real.exp (r.μ*L) → lo ≤ hi → 0 < η → η ≤ 1 →
        hi ≤ G+1 → Real.exp (r.a₀*L) ≤ G →
        (∀ t ∈ Set.Icc lo hi, |φ (t-G)| ≤ B) →
        jointMeshFactor r L (Fintype.card ι+1) M*smoothGrowthFactor k C σ L*
          mixedGridError (ι:=ι) M lo hi η G B D φ (primeEnvelope r k C K d L) 2 j ≤
          Real.exp (-Real.exp (r.target*L)) := by
  let I : ℝ := 6*B+2*D
  let J : ℝ := Real.exp 1*B+I
  let C' : ℝ := C+dimensionCoefficient k
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  filter_upwards [eventually_weighted_integer_decay r k C' (2*I) hσ0 hσ (by norm_num : (0:ℝ)<1),
    eventually_primeEnvelope_budget r k (D:=C') hC (show 0 ≤ 2*J by positivity) hK hd hσ0 hσ]
    with L hInteger hPrime
  intro ι _ M lo hi η G φ j hn hM hmod horder hη hη1 hwindow hG hφ
  let n : ℕ := Fintype.card ι
  let Q : ℝ := jointMeshFactor r L (n+1) M
  let q : ℝ := Real.exp (-Real.exp (r.a₀*L))
  let ε : ℝ := primeEnvelope r k C K d L
  have hQ : 0 ≤ Q := by dsimp [Q,jointMeshFactor]; positivity
  have hε : 0 ≤ ε := by dsimp [ε,primeEnvelope]; positivity
  have hn0 : n ≤ 2^k*Conclusion.bulkSize k L+2 := (Nat.le_succ n).trans hn
  have hfactors := tensor_two_factors_le k n L σ hn0
  have hg0 : 0 ≤ smoothGrowthFactor k C σ L := Real.exp_nonneg _
  have hpow : smoothGrowthFactor k C σ L*2^n ≤ smoothGrowthFactor k C' σ L := by
    simpa only [smoothGrowthFactor_mul,C'] using mul_le_mul_of_nonneg_left hfactors.1 hg0
  have hnpow : smoothGrowthFactor k C σ L*((n:ℝ)*2^n) ≤ smoothGrowthFactor k C' σ L := by
    simpa only [smoothGrowthFactor_mul,C'] using mul_le_mul_of_nonneg_left hfactors.2 hg0
  have hsplit := mixedGridError_le_two_parts (ι:=ι) M hM φ j horder hη hη1 hB hD hwindow hG hφ hε
  have hsplit' : Q*smoothGrowthFactor k C σ L*
      mixedGridError (ι:=ι) M lo hi η G B D φ ε 2 j ≤
      Q*smoothGrowthFactor k C' σ L*I*q+Q*smoothGrowthFactor k C' σ L*J*ε := by
    calc
      _ ≤ Q*smoothGrowthFactor k C σ L*(I*q*2^n+J*((n:ℝ)*2^n)*ε) :=
        mul_le_mul_of_nonneg_left hsplit (mul_nonneg hQ hg0)
      _ = Q*(smoothGrowthFactor k C σ L*2^n)*I*q+
          Q*(smoothGrowthFactor k C σ L*((n:ℝ)*2^n))*J*ε := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hQ) hI) (Real.exp_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnpow hQ) hJ) hε)
  have hi' := hInteger (n+1) M hn hM hmod
  have hp' := hPrime (n+1) M hn hM hmod
  simp only [neg_one_mul] at hi'
  change Q*smoothGrowthFactor k C' σ L*(2*I)*q ≤ _ at hi'
  change Q*smoothGrowthFactor k C' σ L*(2*J)*ε ≤ _ at hp'
  change Q*smoothGrowthFactor k C σ L*mixedGridError (ι:=ι) M lo hi η G B D φ ε 2 j ≤ _
  nlinarith only [hsplit',hi',hp']

end Ostmann.Arithmetic.PrimeCellActualErrorBudget

end

end OAI
