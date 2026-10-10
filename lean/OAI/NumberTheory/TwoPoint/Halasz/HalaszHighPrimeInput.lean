import OAI.NumberTheory.TwoPoint.Halasz.HalaszModerateCofactor

namespace OAI

/-! The high-frequency part of the published prime-repulsion argument.
The explicit input is the weaker constant 1/10 in (A.5)--(A.6) of
Matomäki--Radziwiłł--Tao, *An averaged form of Chowla's conjecture*,
arXiv:1503.05121v3, proof of Lemma A.4(ii), with the quantitative
Vinogradov--Korobov estimate supplying prime-phase cancellation. -/
namespace TwoPointCorrelations

open Filter Finset

def HalaszHighPrimeInput : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ u : ℝ, (Real.log X)^20 ≤ |u| → |u| ≤ 2*X →
    (1/10:ℝ)*Real.log (Real.log X) ≤
      ∑ p ∈ primesUpTo X, (1-|Real.cos (u*Real.log (p:ℝ)/2)|)/(p:ℝ)

theorem HalaszHighPrimeInput.distance_off_unit (hhigh : HalaszHighPrimeInput) :
    ∀ᶠ X : ℕ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ v τ : ℝ, |v| ≤ X → |τ| ≤ X → 1/2 ≤ |v-τ| →
      squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X →
      (31/500:ℝ)*Real.log (Real.log X) ≤
        squaredDistance F (mrtArchimedeanTwist v) X := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hhigh,halasz_moderate_distance_unit,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hhigh hmoderate hlogX
  intro F hF v τ hv hτ hsep hmin
  by_cases hu : |v-τ| ≤ (Real.log X)^20
  · have hh := hmoderate F hF ∅ v τ hsep hu hmin
    have he : mrtMissingCoefficient F ∅ = F := by
      funext n
      simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
    simpa only [he] using hh
  · have hupper : |v-τ| ≤ 2*X := by
      have hh := abs_sub v τ
      linarith
    have hh := hhigh (v-τ) (le_of_not_ge hu) hupper
    have hd := halasz_distance_from_minimizer F hF X v τ hmin
    have hll : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
    linarith

theorem HalaszHighPrimeInput.distance_cutoff (hhigh : HalaszHighPrimeInput) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), OneBounded F → ∀ v τ : ℝ,
      |v| ≤ X → |τ| ≤ X → 1/2 ≤ |v-τ| →
      squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
  obtain ⟨K₀,hK₀,hcut⟩ := halasz_distance_cutoff_loss
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hhigh.distance_off_unit
  have hll := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (500*(K+K₀)))
  filter_upwards [eventually_ge_atTop n₀,eventually_ge_atTop 2,hll]
    with n hn hn2 hlln
  intro X hnX hX F hF v τ hv hτ hsep hmin
  have hrep := hn₀ X (hn.trans hnX) F hF v τ hv hτ hsep hmin
  have hlogn : 0 < Real.log (n:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlog : Real.log (n:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0<n by omega)) (by exact_mod_cast hnX)
  have hllmono := Real.log_le_log hlogn hlog
  have hc := hcut F hF n X hn2 hnX hX v
  dsimp only [Function.comp_def] at hlln
  linarith

end TwoPointCorrelations

end OAI
