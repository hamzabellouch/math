import OAI.NumberTheory.CubicMoment.Decomposition.NoStopCoefficient

namespace OAI

/-! The no-stop coefficient is genuinely supported on short outer levels.
This follows from the previously proved geometric distortion estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_ne_zero_squarefree {ψ : ℝ → ℝ} {w : ℝ} {m : Eisenstein}
    (hm : cutoffMoebius ψ w m ≠ 0) : Squarefree m := by
  by_contra hs
  exact hm (by simp [cutoffMoebius,idealMoebius,UniqueFactorizationMonoid.moebius,hs])

lemma noStop_coefficient_nonzero (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ X Z : ℝ) {b : Eisenstein}
    (hb : noStopCoefficient R D v ψ w ρ X Z b ≠ 0) :
    ∃ r ∈ R, ∃ m ∈ D, r*m = b ∧ Squarefree m ∧
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z := by
  unfold noStopCoefficient stoppedBeta primaryPairCoefficient at hb
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr,hm⟩ := Finset.mem_product.mp hp
  have hsel : norm p.1*primeSurrogate (primaryPrimeFactors p.2)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z := by
    by_contra h
    exact hterm (ite_eq_right h)
  rw [ite_eq_left hsel] at hterm
  exact ⟨p.1,hr,p.2,hm,hprod,
    cutoffMoebius_ne_zero_squarefree (mul_ne_zero_iff.mp hterm).2,hsel⟩

theorem noStop_short_support {κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (R : Finset Eisenstein) (v : Eisenstein → ℂ) (ψ : ℝ → ℝ)
        (w Z : ℝ) (b : Eisenstein),
        noStopCoefficient R (primaryElementBall X) v ψ w ρ X Z b ≠ 0 →
        norm b < X^(κ/4)*Z := by
  obtain ⟨r,hr,hbound⟩ := uniform_prime_bin_distortion hκ (by norm_num : (0:ℝ) < 1)
  let ρ := min r 2
  have hρ : 1 < ρ := lt_min hr (by norm_num)
  have hρ₂ : ρ ≤ 2 := min_le_right _ _
  refine ⟨ρ,hρ,hρ₂,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hX hXp
  intro R v ψ w Z b hb
  obtain ⟨a,_,m,hm,hab,hms,hsel⟩ := noStop_coefficient_nonzero R
    (primaryElementBall X) v ψ w ρ X Z hb
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
    exact ⟨hl,hh.1,hh.2.le.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hl)⟩
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
