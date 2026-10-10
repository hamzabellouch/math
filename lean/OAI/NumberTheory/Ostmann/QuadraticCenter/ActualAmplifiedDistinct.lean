import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualAmplifiedMoment
import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedDistinctLower
import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedRepeatScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators FourierTransform

theorem eventually_actual_amplified_distinct_lower (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ (ι : Type*) [Fintype ι] (p : ι → ℕ)
        (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
        (hne : ∀ i, NeZero (p i)),
      ((∏ i,p i : ℕ):ℝ) ≤ (Z:ℝ)^(1/50:ℝ) →
      ∀ S : ∀ i,Finset (ZMod (p i)), ∀ (P : Finset ℕ),
      c*(Z:ℝ)/Real.log Z ≤ P.card → ∀ ε t : ℕ → ℤ,
      (∀ r ∈ P, ε r = -1 ∨ ε r = 1) →
      letI : ∀ i, NeZero (p i) := hne
      Real.sqrt (parameterX T:ℝ)*Real.exp ((2/125:ℝ)*auxiliaryK Z z) ≤
        (∑' n : ℤ, amplifiedMomentTerm p hcop S (1/16) (parameterX T)
          P ε t (evenMomentParameter (parameterX T) Z) n) →
      Real.sqrt (parameterX T:ℝ)*Real.exp ((2/125:ℝ)*auxiliaryK Z z)/2 ≤
        ∑' n : ℤ, amplifierWeight p hcop S (1/16) (parameterX T) n *
          distinctSignAverage P (fun r => ε r * jacobiSym (n-t r) r)
            (evenMomentParameter (parameterX T) Z) := by
  filter_upwards [eventually_amplified_repeat_inputs c (𝓕 SchwartzCutoff.psi 0).re hc
      SchwartzCutoff.fourier_psi_at_zero_re_pos,
    eventually_prime_band_le_sqrt_parameterX, eventually_parameterX_log_bounds,
    parameterX_tendsto.eventually_gt_atTop 0] with T hrepeat hscale hXlog hX
  intro Z z hZl hZu hz hzl hzu ι _ p hcop hne hprod S P hP ε t hε hI
  let : ∀ i, NeZero (p i) := hne
  have hZlog : 0 < Real.log Z := by linarith [hXlog.1]
  have hZp : (0:ℝ)<Z := by
    have hh := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hZlog
    linarith
  have hZn : 1 ≤ Z := by
    have hh : 0 < Z := by exact_mod_cast hZp
    omega
  have hPpos : 0 < P.card := by
    have hh : (0:ℝ)<P.card := (div_pos (mul_pos hc hZp) hZlog).trans_le hP
    exact_mod_cast hh
  have hLp : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne _))
  have hmass := amplifierWeight_total p hcop S (1/16) (parameterX T)
    (by exact_mod_cast hX)
    (auxiliary_product_mass_scale (by omega) hZn hLp (hscale Z hZu) hprod)
  have hr := hrepeat Z z hZl hZu hz hzl hzu P.card hP _ _ hmass hI
  have hratio : 0 ≤ Real.log (parameterX T:ℝ)/Real.log Z :=
    div_nonneg (by linarith [hXlog.2.1]) hZlog.le
  have hk : 2 ≤ evenMomentParameter (parameterX T) Z := by
    have hh := (evenMomentParameter_bounds (parameterX T) Z (by linarith)).1
    have hh' : (2:ℝ) ≤ evenMomentParameter (parameterX T) Z := by linarith
    exact_mod_cast hh'
  exact (div_le_div_of_nonneg_right hI (by norm_num)).trans
    (amplified_distinct_moment_retains_half p hcop S (by norm_num) (by norm_num)
      (by exact_mod_cast hX) P hPpos ε t hε hk (evenMomentParameter_even _ _)
      hr.1 hr.2.1 hr.2.2)

end Ostmann.QuadraticCenter

end

end OAI
