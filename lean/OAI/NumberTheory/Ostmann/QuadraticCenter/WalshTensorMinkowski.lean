import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshMoments

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem weighted_sum_power_add_le {α : Type*} [Fintype α]
    (f g : α → ℝ) {w A B : ℝ} (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    {l : ℕ} (hl : 1 ≤ l)
    (hMf : w * ∑ i, f i ^ l ≤ A ^ l)
    (hMg : w * ∑ i, g i ^ l ≤ B ^ l) :
    w * ∑ i, (f i + g i) ^ l ≤ (A + B) ^ l := by
  have hl0 : l ≠ 0 := by omega
  let k : ℝ := w ^ ((l : ℝ)⁻¹)
  have hk : 0 ≤ k := Real.rpow_nonneg hw _
  have hkp : k ^ l = w := Real.rpow_inv_natCast_pow hw hl0
  have hscale (v : α → ℝ) (hv : ∀ i, 0 ≤ v i) :
      (∑ i, |k * v i| ^ (l : ℝ)) = w * ∑ i, v i ^ l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (mul_nonneg hk (hv i)), Real.rpow_natCast, mul_pow, hkp]
  have hscale_add : (∑ i, |k * f i + k * g i| ^ (l : ℝ)) =
      w * ∑ i, (f i + g i) ^ l := by
    simp_rw [← mul_add]
    exact hscale (fun i => f i + g i) (fun i => add_nonneg (hf i) (hg i))
  have hM := Real.Lp_add_le (Finset.univ : Finset α)
    (fun i => k * f i) (fun i => k * g i) (p := (l : ℝ)) (by exact_mod_cast hl)
  rw [hscale f hf, hscale g hg, hscale_add] at hM
  simp only [one_div] at hM
  have hMf0 : 0 ≤ w * ∑ i, f i ^ l := mul_nonneg hw (Finset.sum_nonneg (fun i hi => pow_nonneg (hf i) _))
  have hMg0 : 0 ≤ w * ∑ i, g i ^ l := mul_nonneg hw (Finset.sum_nonneg (fun i hi => pow_nonneg (hg i) _))
  have hfg0 : 0 ≤ w * ∑ i, (f i + g i) ^ l :=
    mul_nonneg hw (Finset.sum_nonneg (fun i hi => pow_nonneg (add_nonneg (hf i) (hg i)) _))
  have hfa : (w * ∑ i, f i ^ l) ^ ((l : ℝ)⁻¹) ≤ A := by
    have hh := Real.rpow_le_rpow hMf0 hMf (by positivity : 0 ≤ (l : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hA hl0] at hh
  have hgb : (w * ∑ i, g i ^ l) ^ ((l : ℝ)⁻¹) ≤ B := by
    have hh := Real.rpow_le_rpow hMg0 hMg (by positivity : 0 ≤ (l : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hB hl0] at hh
  have hh : (w * ∑ i, (f i + g i) ^ l) ^ ((l : ℝ)⁻¹) ≤ A + B :=
    hM.trans (add_le_add hfa hgb)
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hfg0 _) hh l
  rwa [Real.rpow_inv_natCast_pow hfg0 hl0] at hp

theorem signMean_power_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → Bool) → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ ε, 0 ≤ f ε) (hg : ∀ ε, 0 ≤ g ε)
    {l : ℕ} (hl : 1 ≤ l)
    (hMf : signMean (fun ε => f ε ^ l) ≤ A ^ l)
    (hMg : signMean (fun ε => g ε ^ l) ≤ B ^ l) :
    signMean (fun ε => (f ε + g ε) ^ l) ≤ (A + B) ^ l :=
  weighted_sum_power_add_le f g (by positivity) hA hB hf hg hl hMf hMg

end Ostmann.QuadraticCenter

end OAI
