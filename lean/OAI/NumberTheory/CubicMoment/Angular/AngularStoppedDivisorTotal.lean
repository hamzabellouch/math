import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedDivisorDyadic
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorTotal
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorDyadic
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorAssembly

namespace OAI

/-! Full early-stopped effective-frequency series for a small square divisor.
The divisor cost in the absolute tail is absorbed by an explicit power bound. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_divisor_noncube_total
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A →
      ∀ (d : Eisenstein) (hd : d ≠ 0), norm d ≤ b^(1/1000:ℝ) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ‖divisorNoncubePoissonContribution d hd (stoppedIntervalSupport ι X (b/2) b e)
        (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₁,hK₁,hshort⟩ := angular_stopped_divisor_noncube_dyadic (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k H
  obtain ⟨K₂,hK₂,hassemble⟩ := stopped_divisor_prefix_tail Φ hΦ hΦ'
  obtain ⟨M,hM,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  refine ⟨K₁+18*K₂*M^2,by positivity,?_⟩
  filter_upwards [hshort,hcoeff,negative_power_log_saving (show 0 < κ/2 by positivity) k,
    (tendsto_rpow_atTop (show 0 < κ*(3/5) by positivity)).eventually_ge_atTop 2,
    eventually_ge_atTop (Real.exp 1)] with X hshort hcoeff hdecay hlargeX hX
  intro δ b u V A hδ hδone hwidth hb2 hb hbX hV hu hVF W hW hWi hWd hAlo
    d hd hdhi e he hNe j₀ k₀ h Z Q early hj hR hRL
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hbp : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hL : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  have hlarge : 2 ≤ b^(3/5:ℝ) := by
    apply hlargeX.trans
    rw [Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)
  let P := stoppedIntervalSupport ι X (b/2) b e
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have hp : ∀ a ∈ P, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b := by
    intro a ha
    have hs := stoppedIntervalSupport_spec X (b/2) b e ha
    exact ⟨hs.1,(Finset.mem_filter.mp ha).2.2.2.1.le,hs.2.2⟩
  have henergy : (∑ a ∈ P, ‖β a‖^2) ≤ (18*M^2)*b := by
    have he := (hcoeff W hW selected 0 (b/2) b e hbp.le hbX).2
    exact he.trans_eq (by ring)
  have hinverse : (norm d)^247*b^(-1:ℝ) ≤ 1/(Real.log X)^k := by
    have ht := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hb
      (by norm_num : (-(1/2):ℝ) ≤ 0)
    rw [←Real.rpow_mul hXp.le] at ht
    have heq : κ*(-(1/2):ℝ) = -(κ/2) := by ring
    rw [heq] at ht
    exact (((stopped_small_divisor_inverse hb1 (norm_nonneg d) hdhi).trans ht).trans hdecay).trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hL.le (by linarith) _))
  have hd1 : 1 ≤ norm d := one_le_norm hd
  let G := fun j => (divisorFrequencyDyad d hd j).filter
    (fun v => ¬∃ z : Eisenstein, z^3 = d*v)
  have hprefix (n : ℕ) (hn : ∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ b^(3/5:ℝ)) :
      ‖∑ j ∈ Finset.range n, finiteDivisorPoissonContribution d P (G j) β u Φ A‖ ≤
        K₁*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
    have hh := hshort δ b u V A hδ hδone hwidth hb2 hb hbX hV hu hVF
      W hW hWi hWd hA (Finset.range n) d G hd
      (fun j hj => hn j (Finset.mem_range.mp hj))
      (fun j _ v hv => ⟨mem_divisorFrequencyDyad.mp (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩)
      e he hNe j₀ k₀ h Z Q early hj hR hRL
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (pow_nonneg hL.le _) hd1))
  have hfinal := hassemble P β b A u (Real.log X) (18*M^2) K₁ k d hd
    hb2 hL (by positivity) hK₁.le hAlo hlarge hinverse hp henergy hprefix
  exact hfinal.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
