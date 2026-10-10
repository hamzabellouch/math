import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCubeSW
import OAI.NumberTheory.CubicMoment.Estimates.LowCoreSupport

namespace OAI

/-! A genuine small-core noncube mass bound for the stopped coefficient,
deduced from its proved Kummer cancellation and exact cube exclusion. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_low_core_mass (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (a k : ℕ) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V C : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      0 ≤ C → C ≤ X^d →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein), S ⊆ lowNoncubeSupport ((Real.log X)^a) C →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*C*b^2/(Real.log X)^k := by
  have ha' : (0:ℝ) < (a:ℝ) := Nat.cast_pos.mpr ha
  have hD : (0:ℝ) < (a+k+1:ℕ) := by positivity
  obtain ⟨K,hK,hbound⟩ := angular_stopped_sequence_cube_sw (ι := ι)
    (A := (a:ℝ)) (D := (a+k+1:ℕ)) (d := d) (E := E)
    hpnt hEF ℓ hℓ hξ hξz hκ ha' hD hH hF hJ
  refine ⟨324*K^2,by positivity,?_⟩
  filter_upwards [hbound,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with X hbound hlog
  intro δ l b u V C hδ hδone hwidth hl hb hbX hV hu hVF hC hCX W hW hWi hWd
    S hS e he hNe j₀ k₀ h Z Q early
  have hterm (v : Eisenstein) (hv : v ∈ S) :
      ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖ ≤ K*b/(Real.log X)^(a+k+1) := by
    obtain ⟨hnc,v₀,j,hv₀,hj,hNv₀,hNj,heq⟩ := mem_lowNoncubeSupport (hS hv)
    have hvreal : norm v₀ ≤ (Real.log X)^(a:ℝ) := by
      simpa only [Real.rpow_natCast] using hNv₀
    have ht := hbound δ l b u V hδ hδone hwidth hl hb hbX hV hu hVF
      W hW hWi hWd v₀ j e hv₀ hj (by rwa [←heq]) hvreal
      (hNj.trans hCX) he hNe j₀ k₀ h Z Q early
    rw [heq]
    simpa only [Real.rpow_natCast] using ht
  have hcard : (S.card:ℝ) ≤ 324*(Real.log X)^a*C :=
    (Nat.cast_le.mpr (Finset.card_le_card hS)).trans
      (lowNoncubeSupport_card (pow_nonneg (zero_le_one.trans hlog) _) hC)
  have hmass :
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤
      (S.card:ℝ)*(K*b/(Real.log X)^(a+k+1))^2 := by
    calc
      _ ≤ ∑ _v ∈ S, (K*b/(Real.log X)^(a+k+1))^2 := by
        apply Finset.sum_le_sum
        intro v hv
        gcongr
        exact hterm v hv
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  exact low_core_mass_bound (a := a) (k := k) hC hlog hcard hmass

end CubicFirstMoment

end

end OAI
