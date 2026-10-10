import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedRoughDivisorLog
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedNoncubeMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughDivisorLog
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedNoncubeMass

namespace OAI

/-! Noncube cancellation for the full coprimality expansion of the literal
early-stopped coefficient. Its coefficient bound and roughness are proved
from the actual stopping construction. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_early_divisor_noncube_mass
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S U : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ p ∈ U, primaryPrime p) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) e S U ≤
        K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₀,hK₀,hempty⟩ := angular_stopped_noncube_mass (ι := ι)
    hpnt hEF ℓ hℓ hHuxley hξ hξz hκ hH hF hJ k
  obtain ⟨K₁,hK₁,hdiv⟩ := angular_stopped_rough_divisor_log ℓ (ι := ι) hHuxley hκ k
  obtain ⟨M,hM,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  refine ⟨K₀+K₁*M^2,by positivity,?_⟩
  filter_upwards [hempty,hdiv,hcoeff,stopped_divisor_cutoff_geometry hκ,
    eventually_ge_atTop (1:ℝ)] with X hempty hdiv hcoeff hgeometry hX
  intro δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb W hW hWi hWd
    S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨hb1,hN,hsize⟩ := hgeometry b B hb hBb
  have hD1 : 1 ≤ b^(1/8:ℝ) := Real.one_le_rpow hb1 (by norm_num)
  have hqb : b/b^(1/8:ℝ) ≤ b := div_le_self (zero_le_one.trans hb1) hD1
  have hbmin : 65536 ≤ b := hN.trans hqb
  have hsize' : 8*B ≤ b^(3/4:ℝ) := hsize.trans
    (Real.rpow_le_rpow (by positivity) hqb (by norm_num))
  have hBX : B ≤ X^2 := by
    apply hBb.trans
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow (zero_le_one.trans hb1) hbX (by norm_num : (0:ℝ) ≤ 3/5)).trans
        (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (3/5:ℝ) ≤ 2))
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  have hcoeff' := (hcoeff W hW selected u l b e (zero_le_one.trans hb1) hbX).1
  have hrough : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n ≠ 0 →
      ∀ p, primaryPrime p → p ∣ n →
        min (X^ξ) (geometricBinLower (1+δ) X h) ≤ norm p := by
    intro n _ hn p hp hpn
    exact angularStoppedRowCoefficient_early_roughness ℓ X (X^ξ) (X^(2/5:ℝ)) u
      (1+δ) Z Q W (Real.rpow_pos_of_pos hXp _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j₀ k₀ h early hj hn hp hpn
  have hd := hdiv (X^ξ) (X^(2/5:ℝ)) l b u M B
    (min (X^ξ) (geometricBinLower (1+δ) X h)) W selected e U S
    hb hbX hB hBb hR hRL hU hcoeff' hrough hS
  have he' := hempty δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize' W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  exact hd.trans ((add_le_add he' (le_refl _)).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
