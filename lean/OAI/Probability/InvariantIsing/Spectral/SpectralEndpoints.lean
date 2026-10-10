import OAI.Probability.InvariantIsing.Spectral.SpectralContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralPaths
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolventDerivative_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolventDerivative ρ eig hρ hρsum a x = ρ a /
      ((∑ b, ρ b / (1 + x * (finiteR ρ eig hρ hρsum x - eig b)) ^ 2) *
        (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) ^ 2) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolventDerivative, lt_self_iff_false, ite_false,
      zero_mul, add_zero, one_pow, div_one, hρsum, mul_one]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hgap : ∀ b, B - eig b ≠ 0 := fun b => (sub_pos.mpr (hs.1 b)).ne'
    have hM := finiteSecondResolvent_pos (fun b => (hρ b).le) hρsum hs.1
    have hden : ∀ b, 1 + x * (finiteR ρ eig hρ hρsum x - eig b) = x * (B - eig b) := by
      intro b
      simp only [finiteR, ite_eq_left h]
      dsimp [B]
      field_simp
      ring
    have hsum : (∑ b, ρ b / (x * (B - eig b)) ^ 2) =
        finiteSecondResolvent ρ eig B / x ^ 2 := by
      unfold finiteSecondResolvent
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      rw [div_div]
      congr 1
      ring
    simp only [projectedResolventDerivative, ite_eq_left h, hden]
    change ρ a / (finiteSecondResolvent ρ eig B * (B - eig a) ^ 2) = _
    rw [hsum]
    field_simp [h.ne', hM.ne', hgap a]

theorem continuousWithinAt_projectedResolventDerivative_zero
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) :
    ContinuousWithinAt (projectedResolventDerivative ρ eig hρ hρsum a) (Ici 0) 0 := by
  let g := fun b x => 1 + x * (finiteR ρ eig hρ hρsum x - eig b)
  have hg : ∀ b, ContinuousAt (g b) 0 := by
    intro b
    exact continuousAt_const.add
      (continuousAt_id.mul ((continuousAt_finiteR_zero ρ eig hρ hρsum).sub continuousAt_const))
  have hS : ContinuousAt (fun x => ∑ b, ρ b / (g b x) ^ 2) 0 := by
    apply tendsto_finsetSum
    intro b _
    exact continuousAt_const.div ((hg b).pow 2) (by simp [g])
  have hc : ContinuousAt (fun x => ρ a / ((∑ b, ρ b / (g b x) ^ 2) * (g a x) ^ 2)) 0 :=
    continuousAt_const.div (hS.mul ((hg a).pow 2)) (by simp [g, hρsum])
  apply hc.continuousWithinAt.congr
  · intro x hx
    exact projectedResolventDerivative_eq_regular ρ eig hρ hρsum a hx
  · exact projectedResolventDerivative_eq_regular ρ eig hρ hρsum a le_rfl

theorem continuousAt_projectedResolventDerivative_pos
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 < x) :
    ContinuousAt (projectedResolventDerivative ρ eig hρ hρsum a) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun b => (hρ b).le) hρsum hs.1
  have hcB := (hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx).hasDerivAt.continuousAt
  have hcM := ((hasStrictDerivAt_finiteSecondResolvent ρ eig hs.1).hasDerivAt.continuousAt).comp hcB
  have hc : ContinuousAt (fun y => ρ a /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum y) *
        (finiteInverse ρ eig hρ hρsum y - eig a) ^ 2)) x :=
    continuousAt_const.div (hcM.mul ((hcB.sub continuousAt_const).pow 2))
      (mul_ne_zero hm.ne' (pow_ne_zero 2 (sub_pos.mpr (hs.1 a)).ne'))
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [projectedResolventDerivative, ite_eq_left (show 0 < y from hy)]

theorem continuousOn_projectedResolventDerivative
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) {c : ℝ} :
    ContinuousOn (projectedResolventDerivative ρ eig hρ hρsum a) (Icc 0 c) := by
  intro x hx
  rcases hx.1.eq_or_lt with h | h
  · subst x
    exact (continuousWithinAt_projectedResolventDerivative_zero ρ eig hρ hρsum a).mono
      (fun y hy => hy.1)
  · exact (continuousAt_projectedResolventDerivative_pos ρ eig hρ hρsum a h).continuousWithinAt

theorem projectedResolventDerivative_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (c : ℝ) (a : ι) (x : ℝ) :
    projectedResolventDerivative ρ (fun _ => c) hρ hρsum a x = ρ a := by
  by_cases hx : 0 ≤ x
  · rw [projectedResolventDerivative_eq_regular ρ (fun _ => c) hρ hρsum a hx]
    simp only [finiteR_constant, sub_self, mul_zero, add_zero, one_pow,
      div_one, hρsum, mul_one]
  · simp only [projectedResolventDerivative, ite_eq_right (show ¬ 0 < x by linarith)]

theorem projectedResolvent_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolvent ρ eig hρ hρsum a x =
      ρ a * x / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, mul_zero, zero_mul,
      add_zero, zero_div]
  · have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hden : 1 + x * (finiteR ρ eig hρ hρsum x - eig a) =
        x * (finiteInverse ρ eig hρ hρsum x - eig a) := by
      simp only [finiteR, ite_eq_left h]
      field_simp
      ring
    simp only [projectedResolvent, ite_eq_left h, hden]
    field_simp [h.ne', (sub_pos.mpr (hs.1 a)).ne']

/-- The right derivative at the origin is the spectral mass, as asserted
in manuscript `rot:f-derivative`. -/
theorem hasDerivWithinAt_projectedResolvent_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a) (ρ a) (Ioi 0) 0 := by
  have hcR := continuousAt_finiteR_zero ρ eig hρ hρsum
  have hden : ContinuousAt
      (fun x : ℝ => 1 + x * (finiteR ρ eig hρ hρsum x - eig a)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hcR.sub continuousAt_const))
  have hquot : Tendsto
      (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)))
      (𝓝 0) (𝓝 (ρ a)) := by
    have hc : ContinuousAt
        (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a))) 0 :=
      continuousAt_const.div hden (by simp)
    simpa only [zero_mul, add_zero, div_one] using
      hc.tendsto
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  apply Tendsto.congr' _ (hquot.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [slope_def_field, projectedResolvent_eq_regular ρ eig hρ hρsum a hx.le]
  simp only [projectedResolvent, lt_self_iff_false, ite_false, sub_zero]
  field_simp [hx'.ne']

end InvariantIsing

end

end OAI
