import OAI.NumberTheory.Ostmann.Construction.CutoffPoisson
import OAI.NumberTheory.Ostmann.Construction.FiniteStatistic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def smoothedStatistic (X : ℝ) (T : ℤ → ℝ) : ℝ :=
  ∑' n : ℤ, (SchwartzCutoff.psi ((n:ℝ)/X)).re*(T n)^2

theorem smoothedStatistic_summable {X M : ℝ} (hX : 0<X) (_hM : 0≤M)
    (T : ℤ → ℝ) (hT : ∀ n, |T n|≤M) :
    Summable (fun n : ℤ => (SchwartzCutoff.psi ((n:ℝ)/X)).re*(T n)^2) := by
  have ha : X⁻¹≠0 := inv_ne_zero hX.ne'
  have hpsi : Summable (fun n : ℤ => ‖SchwartzCutoff.psi ((n:ℝ)/X)‖) := by
    simpa only [schwartzScale_apply, div_eq_mul_inv] using
      schwartz_int_norm_summable (schwartzScale SchwartzCutoff.psi X⁻¹ ha)
  apply (hpsi.mul_right (M^2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (SchwartzCutoff.psi_nonneg _), abs_pow]
  exact mul_le_mul (Complex.re_le_norm _) (pow_le_pow_left₀ (abs_nonneg _) (hT n) 2)
    (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)

theorem smoothedStatistic_lower {X M a c : ℝ} (hX : 0<X) (hM : 0≤M)
    (T : ℤ → ℝ) (hT : ∀ n, |T n|≤M) (s : Finset ℤ)
    (hc : 0≤c) (ha : 0≤a)
    (hcutoff : ∀ x : ℝ, |x|≤1 → c≤(SchwartzCutoff.psi x).re)
    (hrange : ∀ n∈s, |(n:ℝ)/X|≤1)
    (hmean : (s.card:ℝ)*a≤∑ n∈s, T n) :
    c*(s.card:ℝ)*a^2 ≤ smoothedStatistic X T := by
  have hfinite := finiteStatistic_lower s
    (fun n : ℤ => (SchwartzCutoff.psi ((n:ℝ)/X)).re) T hc ha
    (fun n hn => hcutoff _ (hrange n hn)) hmean
  apply hfinite.trans
  exact Summable.sum_le_tsum s
    (fun n _ => mul_nonneg (SchwartzCutoff.psi_nonneg _) (sq_nonneg _))
    (smoothedStatistic_summable hX hM T hT)

theorem exists_cutoff_statistic_constant : ∃ c : ℝ, 0<c ∧
    ∀ (X M a : ℝ) (T : ℤ → ℝ) (s : Finset ℤ),
      0<X → 0≤M → (∀ n, |T n|≤M) → 0≤a →
      (∀ n∈s, |(n:ℝ)/X|≤1) → ((s.card:ℝ)*a≤∑ n∈s, T n) →
      c*(s.card:ℝ)*a^2 ≤ smoothedStatistic X T := by
  obtain ⟨c,hc,hcutoff⟩ := SchwartzCutoff.psi_uniform_lower
  refine ⟨c,hc,?_⟩
  intro X M a T s hX hM hT ha hrange hmean
  exact smoothedStatistic_lower hX hM T hT s hc.le ha hcutoff hrange hmean

end Ostmann.Construction

end

end OAI
