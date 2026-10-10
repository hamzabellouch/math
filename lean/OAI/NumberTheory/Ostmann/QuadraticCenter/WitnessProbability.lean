import Mathlib.Analysis.MeanInequalitiesPow
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductPositive

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def primeProductProbability (P : Finset ℕ) (k : ℕ) (E : ℕ → Prop)
    [DecidablePred E] : ℝ :=
  primeProductMean P k (fun q => if E q then 1 else 0)

theorem primeProductProbability_eq_card (P : Finset ℕ) (k : ℕ) (E : ℕ → Prop)
    [DecidablePred E] :
    primeProductProbability P k E =
      ((primeProductSamples P k).filter E).card / (Nat.choose P.card k:ℝ) := by
  simp only [primeProductProbability,primeProductMean]
  congr 1
  rw [←Finset.sum_filter]
  simp

theorem primeProductMean_nonneg (P : Finset ℕ) (k : ℕ) (f : ℕ → ℝ)
    (hf : ∀q∈primeProductSamples P k,0≤f q) : 0≤primeProductMean P k f :=
  div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)

theorem primeProductProbability_nonneg (P : Finset ℕ) (k : ℕ) (E : ℕ → Prop)
    [DecidablePred E] :
    0≤primeProductProbability P k E := by
  classical
  exact primeProductMean_nonneg P k _ (fun _ _ => by split_ifs <;> norm_num)

theorem primeProductMean_pow_le {P : Finset ℕ} (hP : ∀p∈P,p.Prime)
    {k : ℕ} (hk : k≤P.card) (f : ℕ → ℝ)
    (hf : ∀q∈primeProductSamples P k,0≤f q) (l : ℕ) :
    (primeProductMean P k f)^l ≤ primeProductMean P k (fun q => (f q)^l) := by
  have hc : (Nat.choose P.card k:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hw : (∑q∈primeProductSamples P k,(Nat.choose P.card k:ℝ)⁻¹)=1 := by
    rw [Finset.sum_const, nsmul_eq_mul,primeProductSamples_card hP]
    exact mul_inv_cancel₀ hc
  have h := Real.pow_arith_mean_le_arith_mean_pow (primeProductSamples P k)
    (fun _ => (Nat.choose P.card k:ℝ)⁻¹) f
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hw hf l
  simpa only [primeProductMean,div_eq_mul_inv,←Finset.sum_mul,mul_comm] using h

theorem primeProductMean_event_sq_le (P : Finset ℕ) (k : ℕ) (E : ℕ → Prop)
    [DecidablePred E] (f : ℕ → ℝ) :
    (primeProductMean P k (fun q => if E q then f q else 0))^2 ≤
      primeProductProbability P k E * primeProductMean P k (fun q => (f q)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (primeProductSamples P k)
    (fun q => if E q then (1:ℝ) else 0) f
  have he : ∀q,(if E q then (1:ℝ) else 0)^2=(if E q then (1:ℝ) else 0) := by
    intro q; split_ifs <;> norm_num
  simp only [ite_mul,one_mul,zero_mul,he] at h
  have hh := div_le_div_of_nonneg_right h (sq_nonneg (Nat.choose P.card k:ℝ))
  unfold primeProductProbability primeProductMean
  rw [div_pow,div_mul_div_comm]
  simpa only [pow_two] using hh

theorem primeProductMean_sq_le_of_even_moment {P : Finset ℕ}
    (hP : ∀p∈P,p.Prime) {k l : ℕ} (hk : k≤P.card) (hl : 0<l)
    (f : ℕ → ℝ) {M : ℝ}
    (hmoment : primeProductMean P k (fun q => (f q)^(2*l)) ≤ M^(2*l)) :
    primeProductMean P k (fun q => (f q)^2)≤M^2 := by
  have h := (primeProductMean_pow_le hP hk (fun q => (f q)^2)
    (fun _ _ => sq_nonneg _) l).trans (by simpa only [pow_mul] using hmoment)
  exact le_of_pow_le_pow_left₀ hl.ne' (sq_nonneg M) h

theorem primeProductProbability_lower_of_moment {P : Finset ℕ}
    (hP : ∀p∈P,p.Prime) {k l : ℕ} (hk : k≤P.card) (hl : 0<l)
    (E : ℕ → Prop) [DecidablePred E] (f : ℕ → ℝ) {a M : ℝ}
    (ha : 0≤a) (hM : 0<M)
    (hlower : a≤primeProductMean P k (fun q => if E q then f q else 0))
    (hmoment : primeProductMean P k (fun q => (f q)^(2*l))≤M^(2*l)) :
    a^2/M^2≤primeProductProbability P k E := by
  apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
  have he := pow_le_pow_left₀ ha hlower 2
  have hc := primeProductMean_event_sq_le P k E f
  have hm := primeProductMean_sq_le_of_even_moment hP hk hl f hmoment
  exact (he.trans hc).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm (primeProductProbability_nonneg P k E))

theorem exists_primeProduct_event_of_probability_pos {P : Finset ℕ} {k : ℕ}
    {E : ℕ → Prop} [DecidablePred E] (h : 0<primeProductProbability P k E) :
    ∃q∈primeProductSamples P k,E q := by
  classical
  by_contra hn
  have hz : ∀q∈primeProductSamples P k,¬E q := by simpa using hn
  have he : primeProductProbability P k E=0 := by
    simp only [primeProductProbability,primeProductMean]
    rw [Finset.sum_eq_zero (fun q hq => ite_eq_right (hz q hq)),zero_div]
  rw [he] at h
  exact (lt_irrefl _ h)

end Ostmann.QuadraticCenter

end

end OAI
