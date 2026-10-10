import OAI.NumberTheory.Ostmann.Construction.BinExponential
import OAI.NumberTheory.Ostmann.Construction.ExactSourceValue
import OAI.NumberTheory.Ostmann.Construction.PrimeGroupBins

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def primeSourceScalar (d : Decomposition) (S : PrimeSource) : ℝ :=
  S.law.mean (fun p => exactSourceValue d p)

def primeGroupScalar (d : Decomposition) (S : PrimeSource) (b : ℕ) (t : ℤ) : ℝ :=
  (primeGroupPrior S b).mean (fun x =>
    Ostmann.smoothPartition (primeGroupLog S b x-t)*∏i,exactSourceValue d (x i))

lemma balancedPrimeIndicator_nonneg (d : Decomposition) (p : ℕ) :
    0 ≤ balancedPrimeIndicator d p := by
  classical
  unfold balancedPrimeIndicator
  split_ifs <;> norm_num

theorem primeSourceScalar_nonneg (d : Decomposition) (S : PrimeSource) :
    0 ≤ primeSourceScalar d S :=
  S.law.mean_nonneg (fun p => (exactSourceValue_pos d (S.prime _ p.property)).le)

theorem primeSourceScalar_balanced_lower (d : Decomposition) (S : PrimeSource)
    (hS : (1/2:ℝ) ≤ S.law.mean (fun p => balancedPrimeIndicator d p)) :
    (1/4:ℝ) ≤ primeSourceScalar d S := by
  have hm : (1/2:ℝ)*S.law.mean (fun p => balancedPrimeIndicator d p) ≤ primeSourceScalar d S := by
    unfold FinitePrior.mean primeSourceScalar
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_left (exactSourceValue_indicator_lower d (S.prime _ p.property))
      (S.law.mass_nonneg p)
    nlinarith
  linarith

theorem primeGroupScalar_nonneg (d : Decomposition) (S : PrimeSource) (b : ℕ) (t : ℤ) :
    0 ≤ primeGroupScalar d S b t := by
  apply FinitePrior.mean_nonneg
  intro x
  exact mul_nonneg (Ostmann.smoothPartition_nonneg _)
    (Finset.prod_nonneg (fun i _ => (exactSourceValue_pos d (S.prime _ (x i).property)).le))

theorem primeGroupScalar_lower (d : Decomposition) (S : PrimeSource) (b : ℕ) (t : ℤ) :
    (1/2:ℝ)^b*primeGroupBinMass d S b t ≤ primeGroupScalar d S b t := by
  unfold primeGroupBinMass primeGroupScalar FinitePrior.mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  have hp : (1/2:ℝ)^b*primeGroupBalanced d S b x ≤ ∏i,exactSourceValue d (x i) := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i : Fin b => (1/2:ℝ)*balancedPrimeIndicator d (x i))
      (g := fun i => exactSourceValue d (x i))
      (fun i _ => mul_nonneg (by norm_num) (balancedPrimeIndicator_nonneg d (x i)))
      (fun i _ => exactSourceValue_indicator_lower d (S.prime _ (x i).property))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
      Fintype.card_fin,primeGroupBalanced] using h
  have h := mul_le_mul_of_nonneg_left hp (mul_nonneg
    ((primeGroupPrior S b).mass_nonneg x) (Ostmann.smoothPartition_nonneg (primeGroupLog S b x-t)))
  nlinarith

theorem primeGroupScalar_exp_lower (d : Decomposition) (S : PrimeSource)
    (b m : ℕ) (t : ℤ) (hb : b≤ m)
    (hbin : Real.exp (-3*(m:ℝ)) ≤ primeGroupBinMass d S b t) :
    Real.exp (-4*(m:ℝ)) ≤ primeGroupScalar d S b t := by
  have hb' : (b:ℝ)≤ m := by exact_mod_cast hb
  have he : Real.exp (-(m:ℝ)) ≤ (1/2:ℝ)^b :=
    (Real.exp_le_exp.mpr (neg_le_neg hb')).trans (exp_neg_nat_le_half_pow b)
  have hm := mul_le_mul he hbin (Real.exp_pos _).le (by positivity : (0:ℝ)≤(1/2:ℝ)^b)
  have hx : Real.exp (-(m:ℝ))*Real.exp (-3*(m:ℝ))=Real.exp (-4*(m:ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hx] at hm
  exact hm.trans (primeGroupScalar_lower d S b t)

def nongiantScalar (d : Decomposition) (bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) : ℝ :=
  primeGroupScalar d bulk b tb*primeGroupScalar d spectator s td*
    ∏i,primeSourceScalar d (aux i)

theorem nongiantScalar_exp_lower (d : Decomposition) (bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s m : ℕ) (tb td : ℤ)
    (hb : b≤ m) (hs : s≤ m) (hi : Fintype.card ι≤ m)
    (hbulk : Real.exp (-3*(m:ℝ)) ≤ primeGroupBinMass d bulk b tb)
    (hspec : Real.exp (-3*(m:ℝ)) ≤ primeGroupBinMass d spectator s td)
    (haux : ∀i,(1/2:ℝ) ≤ (aux i).law.mean (fun p => balancedPrimeIndicator d p)) :
    Real.exp (-10*(m:ℝ)) ≤ nongiantScalar d bulk spectator aux b s tb td := by
  classical
  have hb' := primeGroupScalar_exp_lower d bulk b m tb hb hbulk
  have hs' := primeGroupScalar_exp_lower d spectator s m td hs hspec
  have haux' : (1/4:ℝ)^(Fintype.card ι) ≤ ∏i,primeSourceScalar d (aux i) := by
    simpa only [Finset.prod_const,Finset.card_univ] using
      (Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : ι => (1/4:ℝ))
        (g := fun i => primeSourceScalar d (aux i)) (by intros; norm_num)
        (fun i _ => primeSourceScalar_balanced_lower d (aux i) (haux i)))
  have he : Real.exp (-2*(m:ℝ)) ≤ ∏i,primeSourceScalar d (aux i) := by
    have hcard : (Fintype.card ι:ℝ) ≤ m := by exact_mod_cast hi
    have hpow := pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_nat_le_half_pow (Fintype.card ι)) 2
    have heq : Real.exp (-(Fintype.card ι:ℝ))^2=Real.exp (-2*(Fintype.card ι:ℝ)) := by
      rw [pow_two,← Real.exp_add]; congr 1; ring
    have hpq : ((1/2:ℝ)^(Fintype.card ι))^2=(1/4:ℝ)^(Fintype.card ι) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    rw [heq,hpq] at hpow
    exact (Real.exp_le_exp.mpr (by linarith : -2*(m:ℝ)≤-2*(Fintype.card ι:ℝ))).trans
      (hpow.trans haux')
  have hbs := mul_le_mul hb' hs' (Real.exp_pos _).le (primeGroupScalar_nonneg d bulk b tb)
  have hall := mul_le_mul hbs he (Real.exp_pos _).le
    (mul_nonneg (primeGroupScalar_nonneg d bulk b tb) (primeGroupScalar_nonneg d spectator s td))
  have heq : Real.exp (-4*(m:ℝ))*Real.exp (-4*(m:ℝ))*Real.exp (-2*(m:ℝ))=
      Real.exp (-10*(m:ℝ)) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  rw [heq] at hall
  exact hall

end Ostmann.Construction

end

end OAI
