import OAI.NumberTheory.CubicMoment.Estimates.RestrictedNoStopCoefficient

namespace OAI

/-! The additional first-stage predicate does not alter the proved
short support of any surviving no-stop outer coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem restricted_noStop_short_support {κ : ℝ} (hκ : 0 < κ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (R : Finset Eisenstein) (v : Eisenstein → ℂ) (ψ : ℝ → ℝ)
        (w Z : ℝ) (P : Eisenstein → Eisenstein → Prop) (b : Eisenstein),
        restrictedNoStopCoefficient R (primaryElementBall X) v ψ w ρ X Z P b ≠ 0 →
        norm b < X^(κ/4)*Z := by
  obtain ⟨r,hr,hbound⟩ := uniform_prime_bin_distortion hκ (by norm_num : (0:ℝ) < 1)
  let ρ := min (min r cap) 2
  have hρ : 1 < ρ := lt_min (lt_min hr hcap) (by norm_num)
  have hρ₂ : ρ ≤ 2 := min_le_right _ _
  refine ⟨ρ,hρ,hρ₂,(min_le_left _ _).trans (min_le_right _ _),?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hX hXp
  intro R v ψ w Z P b hb
  obtain ⟨a,_,m,hm,hab,hms,hsel⟩ := restrictedNoStop_coefficient_nonzero R
    (primaryElementBall X) v ψ w ρ X Z P hb
  obtain ⟨hmp,hmX⟩ := mem_primaryElementBall.mp hm
  have hc (p : Eisenstein) (hp : p ∈ primaryPrimeFactors m) :
      0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) ∧
      geometricBinLower ρ X (geometricPrimeBin ρ X p) ≤ norm p ∧
      norm p ≤ r*geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
    obtain ⟨hpp,hpd⟩ := primaryPrimeFactor_spec hmp hp
    have hpX := (norm_le_of_dvd (primary_ne_zero hmp) hpd).trans hmX
    have hh := geometricPrimeBin_cell hρ hρ₂ hpp hpX
    have hl : 0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
      unfold geometricBinLower
      positivity
    exact ⟨hl,hh.1,hh.2.le.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hl)⟩
  have hmB := (hX m hmp hms (by simpa only [one_mul] using hmX)
    (primaryPrimeFactors m) (Finset.Subset.refl _) (geometricPrimeBin ρ X)
    (geometricBinLower ρ X) hc).2
  rw [primaryPrimeFactors_prod hmp hms] at hmB
  rw [←hab,norm_mul_eq]
  calc
    _ ≤ norm a*(X^(κ/4)*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) :=
      mul_le_mul_of_nonneg_left hmB (norm_nonneg _)
    _ = X^(κ/4)*(norm a*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) := by ring
    _ < _ := mul_lt_mul_of_pos_left hsel (Real.rpow_pos_of_pos hXp _)

end CubicFirstMoment

end

end OAI
