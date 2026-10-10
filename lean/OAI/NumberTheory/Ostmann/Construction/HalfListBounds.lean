import OAI.NumberTheory.Ostmann.Construction.ActualTestBounds
import OAI.NumberTheory.Ostmann.Construction.HalfListTest
import OAI.NumberTheory.Ostmann.Construction.SmoothedStatistic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

lemma FinitePrior.abs_mean_le {ι : Type*} [Fintype ι] (μ : FinitePrior ι)
    (f : ι → ℝ) {M : ℝ} (hf : ∀ i, |f i|≤M) : |μ.mean f|≤M := by
  calc
    _ ≤ ∑i,|μ.mass i*f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑i,μ.mass i*|f i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul,abs_of_nonneg (μ.mass_nonneg i)]
    _ ≤ ∑i,μ.mass i*M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (μ.mass_nonneg i)
    _ = M := μ.mean_const M

lemma primeSourceTestMean_abs_le (d : Decomposition) (S : PrimeSource) (n : ℤ) :
    |primeSourceTestMean d S n|≤primeSourceBound S :=
  S.law.abs_mean_le _ (fun p => residueTest_re_abs_le_source d S p n)

lemma giantTestMean_abs_le (d : Decomposition) (P : Finset ℕ) (S : PrimeSource) (n : ℤ) :
    |giantTestMean d P S n|≤primeSourceBound S :=
  S.law.abs_mean_le _ (fun p => favorableGiantResidueTest_re_abs_le_source d P S p n)

lemma primeGroupTestMean_abs_le (d : Decomposition) (S : PrimeSource) (b : ℕ)
    (t n : ℤ) : |primeGroupTestMean d S b t n|≤(primeSourceBound S)^b := by
  apply FinitePrior.abs_mean_le
  intro x
  rw [abs_mul,abs_of_nonneg (Ostmann.smoothPartition_nonneg _),Finset.abs_prod]
  have hp : (∏i,|(residueTest d (x i) (n:ZMod (x i:ℕ))).re|) ≤ (primeSourceBound S)^b := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun i : Fin b => |(residueTest d (x i) (n:ZMod (x i:ℕ))).re|)
        (g := fun _ => primeSourceBound S) (fun _ _ => abs_nonneg _)
        (fun i _ => residueTest_re_abs_le_source d S (x i) n))
  calc
    _ ≤ 1*(primeSourceBound S)^b := mul_le_mul (Ostmann.smoothPartition_le_one _) hp
      (Finset.prod_nonneg fun _ _ => abs_nonneg _) zero_le_one
    _ = _ := one_mul _

def halfListBound (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) : ℝ :=
  primeSourceBound giant*(primeSourceBound bulk)^b*(primeSourceBound spectator)^s*
    ∏i,primeSourceBound (aux i)

lemma halfListBound_nonneg (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) : 0≤halfListBound giant bulk spectator aux b s := by
  unfold halfListBound
  exact mul_nonneg (mul_nonneg (mul_nonneg (primeSourceBound_nonneg giant)
    (pow_nonneg (primeSourceBound_nonneg bulk) _)) (pow_nonneg (primeSourceBound_nonneg spectator) _))
    (Finset.prod_nonneg fun i _ => primeSourceBound_nonneg (aux i))

theorem halfListTest_abs_le (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td n : ℤ) :
    |halfListTest d P giant bulk spectator aux b s tb td n|≤halfListBound giant bulk spectator aux b s := by
  classical
  unfold halfListTest halfListBound
  rw [abs_mul,abs_mul,abs_mul,Finset.abs_prod]
  apply mul_le_mul
  · apply mul_le_mul
    · exact mul_le_mul (giantTestMean_abs_le d P giant n)
        (primeGroupTestMean_abs_le d bulk b tb n) (abs_nonneg _) (primeSourceBound_nonneg _)
    · exact primeGroupTestMean_abs_le d spectator s td n
    · exact abs_nonneg _
    · exact mul_nonneg (primeSourceBound_nonneg _) (pow_nonneg (primeSourceBound_nonneg _) _)
  · exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => primeSourceTestMean_abs_le d (aux i) n)
  · exact Finset.prod_nonneg fun _ _ => abs_nonneg _
  · exact mul_nonneg (mul_nonneg (primeSourceBound_nonneg _)
      (pow_nonneg (primeSourceBound_nonneg _) _)) (pow_nonneg (primeSourceBound_nonneg _) _)

theorem halfListTest_statistic_summable (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) {X : ℝ} (hX : 0<X) :
    Summable (fun n : ℤ => (SchwartzCutoff.psi ((n:ℝ)/X)).re*
      (halfListTest d P giant bulk spectator aux b s tb td n)^2) :=
  smoothedStatistic_summable hX (halfListBound_nonneg giant bulk spectator aux b s) _
    (halfListTest_abs_le d P giant bulk spectator aux b s tb td)

end Ostmann.Construction

end

end OAI
