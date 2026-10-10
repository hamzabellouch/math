import OAI.Probability.InvariantIsing.Spectral.SpectralCalculus

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) : ℝ :=
  if 0 < x then ρ a / (finiteInverse ρ eig hρ hρsum x - eig a) else 0

def projectedResolventDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) : ℝ :=
  if 0 < x then ρ a /
    (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
      (finiteInverse ρ eig hρ hρsum x - eig a) ^ 2) else ρ a

theorem sum_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a, projectedResolvent ρ eig hρ hρsum a x) = x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, Finset.sum_const_zero]
  · simp only [projectedResolvent, ite_eq_left h]
    exact (finiteInverse_spec ρ eig hρ hρsum h).2

theorem projectedResolventDerivative_pos (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) :
    0 < projectedResolventDerivative ρ eig hρ hρsum a x := by
  by_cases hx : 0 < x
  · simp only [projectedResolventDerivative, ite_eq_left hx]
    have hs := finiteInverse_spec ρ eig hρ hρsum hx
    exact div_pos (hρ a) (mul_pos
      (finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1)
      (sq_pos_of_pos (sub_pos.mpr (hs.1 a))))
  · simpa only [projectedResolventDerivative, ite_eq_right hx] using hρ a

theorem sum_projectedResolventDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) :
    (∑ a, projectedResolventDerivative ρ eig hρ hρsum a x) = 1 := by
  by_cases hx : 0 < x
  · simp only [projectedResolventDerivative, ite_eq_left hx]
    have hs := finiteInverse_spec ρ eig hρ hρsum hx
    have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
    calc
      _ = (∑ a, ρ a / (finiteInverse ρ eig hρ hρsum x - eig a) ^ 2) /
          finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        rw [div_div]
        congr 1
        ring
      _ = 1 := div_self hm.ne'
  · simpa only [projectedResolventDerivative, ite_eq_right hx] using hρsum

theorem projectedResolventDerivative_le_one (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) :
    projectedResolventDerivative ρ eig hρ hρsum a x ≤ 1 := by
  rw [← sum_projectedResolventDerivative ρ eig hρ hρsum x]
  exact Finset.single_le_sum
    (fun b _ => (projectedResolventDerivative_pos ρ eig hρ hρsum b x).le)
    (Finset.mem_univ a)

theorem hasStrictDerivAt_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hden : HasStrictDerivAt
      (fun y => finiteInverse ρ eig hρ hρsum y - eig a)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
    convert! hd.sub_const (eig a) using 1
  have hquot := (hasStrictDerivAt_const x (ρ a)).fun_div hden
    (ne_of_gt (sub_pos.mpr (hs.1 a)))
  have heq : (fun y => ρ a / (finiteInverse ρ eig hρ hρsum y - eig a)) =ᶠ[𝓝 x]
      projectedResolvent ρ eig hρ hρsum a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [projectedResolvent, ite_eq_left (show 0 < y from hy)]
  convert hquot.congr_of_eventuallyEq heq using 1
  simp only [projectedResolventDerivative, ite_eq_left hx]
  field_simp
  ring

end InvariantIsing

end

end OAI
