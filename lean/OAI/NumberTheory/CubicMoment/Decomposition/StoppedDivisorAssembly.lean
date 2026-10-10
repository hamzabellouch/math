import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorTailPower
import OAI.NumberTheory.CubicMoment.Estimates.DivisorNoncubeIdentity

namespace OAI

/-! Finite-prefix and absolute-tail assembly for the actual effective
frequency partition of one square divisor. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_divisor_prefix_tail (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (b A u L M C : ℝ) (k : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      2 ≤ b → 0 < L → 0 ≤ M → 0 ≤ C → b^(3/2:ℝ) ≤ A →
      2 ≤ b^(3/5:ℝ) → (norm d)^247*b^(-1:ℝ) ≤ 1/L^k →
      (∀ a ∈ S, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b) →
      (∑ a ∈ S, ‖β a‖^2) ≤ M*b →
      (∀ n : ℕ, (∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ b^(3/5:ℝ)) →
        ‖∑ j ∈ Finset.range n, finiteDivisorPoissonContribution d S
          ((divisorFrequencyDyad d hd j).filter (fun v => ¬∃ z : Eisenstein, z^3 = d*v))
          β u Φ A‖ ≤ C*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k) →
      ‖divisorNoncubePoissonContribution d hd S β u Φ A‖ ≤
        (C+K*M)*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k := by
  obtain ⟨K,hK,htail⟩ := stopped_divisor_poisson_tail_power Φ hΦ hΦ'
  refine ⟨K,hK,?_⟩
  intro S β b A u L M C k d hd hb hL hM hC hA hlarge hinverse hS henergy hprefix
  have hbp : 0 < b := by linarith
  have hdN : 0 ≤ norm d := norm_nonneg d
  have hb1 : 1 ≤ b := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hA
  obtain ⟨n,hn,hn'⟩ := stopped_poisson_cutoff hbp hlarge
  let G := fun j => (divisorFrequencyDyad d hd j).filter (fun v => ¬∃ z : Eisenstein, z^3 = d*v)
  let F := fun j => finiteDivisorPoissonContribution d S (G j) β u Φ A
  have ht : Summable (fun j => F (j+n)) ∧
      ‖∑' j : ℕ, F (j+n)‖ ≤ K*(norm d)^247*b^(-2:ℝ)*(∑ a ∈ S, ‖β a‖^2) :=
    htail S G β A (b/2) b u n d hd (by linarith) (by linarith)
      hA hn hS (fun _ => Finset.filter_subset _ _)
  have hbt : b^(-2:ℝ)*b = b^(-1:ℝ) := by
    nth_rw 2 [←Real.rpow_one b]
    rw [←Real.rpow_add hbp]
    norm_num
  have ht' : ‖∑' j : ℕ, F (j+n)‖ ≤ K*M/L^k := by
    apply ht.2.trans
    calc
      _ ≤ K*(norm d)^247*b^(-2:ℝ)*(M*b) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = (K*M)*((norm d)^247*(b^(-2:ℝ)*b)) := by ring
      _ = (K*M)*((norm d)^247*b^(-1:ℝ)) := by rw [hbt]
      _ ≤ (K*M)*(1/L^k) := mul_le_mul_of_nonneg_left hinverse (by positivity)
      _ = _ := by ring
  have hs : ‖∑ j ∈ Finset.range n, F j‖ ≤ C*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k := hprefix n hn'
  have hscale : 1 ≤ A^(2/3:ℝ)*b^(5/3:ℝ) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hA1 (by norm_num)) (Real.one_le_rpow hb1 (by norm_num))
  change ‖∑' j : ℕ, F j‖ ≤ _
  apply (norm_tsum_prefix_tail n ht.1 hs ht').trans
  calc
    _ ≤ C*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k+(K*M)*(A^(2/3:ℝ)*b^(5/3:ℝ))/L^k := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale (mul_nonneg hK.le hM))
        (pow_nonneg hL.le _)
    _ = _ := by ring

lemma stopped_small_divisor_inverse {b D : ℝ} (hb : 1 ≤ b) (hD : 0 ≤ D)
    (hDb : D ≤ b^(1/1000:ℝ)) : D^247*b^(-1:ℝ) ≤ b^(-(1/2):ℝ) := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  calc
    _ ≤ (b^(1/1000:ℝ))^247*b^(-1:ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD hDb 247) (by positivity)
    _ = b^((1/1000:ℝ)*247-1) := by
      rw [←Real.rpow_mul_natCast hbp.le,←Real.rpow_add hbp]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb (by norm_num)

end CubicFirstMoment

end

end OAI
