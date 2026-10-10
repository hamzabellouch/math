import OAI.NumberTheory.JointDickman.Arithmetic.SmoothAmplificationMoments

namespace OAI

/-! # Exact independence from every fixed residue coordinate -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem auxiliarySquarePeriod_eventually_coprime (q : ℕ) (hq : 0 < q) :
    ∀ᶠ B : ℕ in atTop, (auxiliarySquarePeriod B).Coprime q := by
  filter_upwards [auxiliaryCutoff_tendsto.eventually_ge_atTop q] with B hB
  unfold auxiliarySquarePeriod
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.prod_left
  intro p hp
  apply (auxiliaryPrimes_prime B p hp).coprime_iff_not_dvd.mpr
  intro hd
  have hpq := Nat.le_of_dvd hq hd
  have hcut : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
  omega

theorem residueAmplification_mean (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    residueMean (fun a => (residueAmplification B L τ C w a : ℂ)) =
      (arithmeticAmplificationMoment B L τ C w 1 : ℂ) := by
  unfold residueMean arithmeticAmplificationMoment residueAmplification
  simp only [pow_one, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

theorem fixed_residue_amplification_average {q B L : ℕ} [NeZero q] (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (f : ZMod q → ℂ) (hcop : (auxiliarySquarePeriod B).Coprime q) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      f (n : ZMod q) * (arithmeticSubsetAmplification B L τ C w n : ℂ)) / (N : ℂ))
      atTop (nhds (residueMean f * (arithmeticAmplificationMoment B L τ C w 1 : ℂ))) := by
  have h := coprime_residue_average_tendsto (m := q) (q := auxiliarySquarePeriod B) hcop.symm f
    (fun a => (residueAmplification B L τ C w a : ℂ))
  rw [residueAmplification_mean B L τ C w] at h
  have he : (fun N : ℕ => (∑ n ∈ range N, f (n : ZMod q) *
      (residueAmplification B L τ C w (n : ZMod (auxiliarySquarePeriod B)) : ℂ)) / (N : ℂ)) =
      (fun N : ℕ => (∑ n ∈ range N, f (n : ZMod q) *
        (arithmeticSubsetAmplification B L τ C w n : ℂ)) / (N : ℂ)) := by
    funext N
    exact congrArg (fun z : ℂ => z / (N : ℂ)) (sum_congr rfl (fun n _ =>
      congrArg (fun x : ℝ => f (n : ZMod q) * (x : ℂ))
        (residueAmplification_natCast B L n τ C w)))
  rw [he] at h
  exact h

theorem eventually_fixed_residue_amplification_average (q : ℕ) [NeZero q] :
    ∀ᶠ B : ℕ in atTop, ∀ (L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) (f : ZMod q → ℂ),
      Tendsto (fun N : ℕ => (∑ n ∈ range N,
        f (n : ZMod q) * (arithmeticSubsetAmplification B L τ C w n : ℂ)) / (N : ℂ))
        atTop (nhds (residueMean f * (arithmeticAmplificationMoment B L τ C w 1 : ℂ))) := by
  filter_upwards [auxiliarySquarePeriod_eventually_coprime q (NeZero.pos q)] with B hB
  intro L τ C w f
  exact fixed_residue_amplification_average τ C w f hB

end JointDickman

end OAI
