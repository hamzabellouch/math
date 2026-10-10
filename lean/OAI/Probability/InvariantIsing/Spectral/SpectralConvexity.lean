import OAI.Probability.InvariantIsing.Spectral.SpectralCovariance
import Mathlib.Analysis.Convex.Deriv

namespace OAI

/-! Convexity of the spectral energy primitive, including zero. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteR_mem_interval (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteR ρ eig hρ hρsum x ∧ finiteR ρ eig hρ hρsum x ≤ u := by
  by_cases hx : 0 < x
  · simp only [finiteR, ite_eq_left hx]
    have hs := finiteInverse_spec ρ eig hρ hρsum hx
    obtain ⟨a, _⟩ := exists_pos_spectral_weight (fun a => (hρ a).le) hρsum
    have hbl : 0 < finiteInverse ρ eig hρ hρsum x - l := by linarith [hl a, hs.1 a]
    have hlow := le_finiteResolvent (fun a => (hρ a).le) hρsum hl hs.1
    rw [hs.2] at hlow
    have hlow' := (div_le_iff₀ hbl).mp hlow
    have hlow'' : 1 / x ≤ finiteInverse ρ eig hρ hρsum x - l := by
      apply (div_le_iff₀ hx).mpr
      nlinarith
    refine ⟨by linarith, ?_⟩
    by_cases hbu : finiteInverse ρ eig hρ hρsum x ≤ u
    · linarith [one_div_pos.mpr hx]
    · exact (finiteR_bounds (fun a => (hρ a).le) hρsum hl hu
        (lt_of_not_ge hbu) hx hs.2).2
  · simp only [finiteR, ite_eq_right hx]
    constructor
    · calc
        l = ∑ a, ρ a * l := by rw [← Finset.sum_mul, hρsum, one_mul]
        _ ≤ ∑ a, ρ a * eig a := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hl a) (hρ a).le
    · calc
        (∑ a, ρ a * eig a) ≤ ∑ a, ρ a * u := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hu a) (hρ a).le
        _ = u := by rw [← Finset.sum_mul, hρsum, one_mul]

theorem continuousAt_mul_finiteR_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    ContinuousAt (fun x => x * finiteR ρ eig hρ hρsum x) 0 := by
  let K := ∑ a, |eig a|
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    change |eig a| ≤ ∑ a, |eig a|
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hR : ∀ x, |finiteR ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have ht : Tendsto (fun x : ℝ => |x| * K) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const K
  have ht' : Tendsto (fun x => x * finiteR ρ eig hρ hρsum x) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hR x) (abs_nonneg x)
  simpa only [ContinuousAt, zero_mul] using ht'

theorem convexOn_mul_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {c : ℝ} :
    ConvexOn ℝ (Icc 0 c) (fun x => x * finiteR ρ eig hρ hρsum x) := by
  have hcont : ContinuousOn (fun x => x * finiteR ρ eig hρ hρsum x) (Icc 0 c) := by
    intro x hx
    rcases hx.1.eq_or_lt with h | h
    · subst x
      exact (continuousAt_mul_finiteR_zero ρ eig hρ hρsum).continuousWithinAt
    · exact (hasStrictDerivAt_mul_finiteR ρ eig hρ hρsum h).hasDerivAt.continuousAt.continuousWithinAt
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 c) hcont
    (f' := finiteEnergyDerivative ρ eig hρ hρsum)
    (f'' := fun x =>
      2 * (x * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) -
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 2) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3)
  · intro x hx
    have hx' : 0 < x := (show x ∈ Ioo 0 c by simpa only [interior_Icc] using hx).1
    exact (hasStrictDerivAt_mul_finiteR ρ eig hρ hρsum hx').hasDerivAt.hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x := (show x ∈ Ioo 0 c by simpa only [interior_Icc] using hx).1
    exact (hasStrictDerivAt_finiteEnergyDerivative ρ eig hρ hρsum hx').hasDerivAt.hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x := (show x ∈ Ioo 0 c by simpa only [interior_Icc] using hx).1
    exact finiteEnergy_secondDerivative_nonneg ρ eig hρ hρsum hx'

end InvariantIsing

end

end OAI
