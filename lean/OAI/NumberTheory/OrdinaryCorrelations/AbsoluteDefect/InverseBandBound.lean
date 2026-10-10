import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Line
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.IntegralInverseFiveQuarters

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryHorizontalHalasz
open MeasureTheory Set OrdinaryLogDerivative OrdinaryPowerBounds OrdinaryHalaszEnvelopes
open OrdinaryDirichletMeanSquare

lemma inverse_band_bound {A δ u : ℝ} (hA : 0<A) (hδ : 0<δ) (hu : A*δ≤u) :
    1/u≤(A*δ)^(-(1/4:ℝ))*u^(-(3/4:ℝ)) := by
  have hAD : 0<A*δ := mul_pos hA hδ
  have hu0 : 0<u := hAD.trans_le hu
  have he := Real.rpow_le_rpow_of_nonpos hAD hu (by norm_num : -(1/4:ℝ)≤0)
  calc
    1/u = u^(-(1/4:ℝ))*u^(-(3/4:ℝ)) := by
      rw [←Real.rpow_add hu0]
      norm_num [Real.rpow_neg_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hu0.le _)

theorem band_derivative_bound {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖≤1)
    (hm : Complete f) {A δ ε : ℝ} (hA : 0<A) (hδ : 0<δ) (hδ1 : δ≤1)
    (hε : 0≤ε) (l r : ℝ)
    (hband : ∀u : ℝ, δ≤u → u≤δ+1 → u≤A*δ → ∀t∈Icc l r,
      ‖LSeries f (line u t)‖≤ε/u) :
    δ*(∫t in Icc l r, gaussian t*‖deriv (LSeries f) (line δ t)‖) ≤
      10*energyConstant*ε+60*energyConstant*A^(-(1/4:ℝ))+
        2*Real.sqrt (∫t : ℝ, gaussian t)*Real.sqrt (5*energyConstant)*Real.sqrt δ := by
  have hC : 0≤energyConstant := by unfold energyConstant gaussianConstant; positivity
  have hW : 0≤∫t : ℝ, gaussian t := integral_nonneg gaussian_nonneg
  let B := (A*δ)^(-(1/4:ℝ))
  let M := fun x : ℝ => ε/(δ+x)+3*B*(δ+x)^(-(3/4:ℝ))
  have hu (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0<δ+x := by linarith [hx.1]
  have hM : ContinuousOn M (Icc 0 1) :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun x hx => (hu x hx).ne')).add
      (continuousOn_const.mul (continuousOn_shift_rpow hδ))
  have hM0 (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0≤M x := by have hx0 := (hu x hx).le; dsimp [M,B]; positivity
  have hbound (x : ℝ) (hx : x∈Icc (0:ℝ) 1) (t : ℝ) (ht : t∈Icc l r) :
      ‖LSeries f (line (δ+x) t)‖≤M x := by
    by_cases hb : δ+x≤A*δ
    · exact (hband (δ+x) (by linarith [hx.1]) (by linarith [hx.2]) hb t ht).trans
        (le_add_of_nonneg_right (by have hx0 := (hu x hx).le; dsimp [B]; positivity))
    · have hh := LSeries_norm_le hf (s:=line (δ+x) t) (by simp; linarith [hx.1])
      simp only [line_re,add_sub_cancel_left] at hh
      have hi := inverse_band_bound hA hδ (le_of_not_ge hb)
      have h3 : 1+1/(δ+x)≤3/(δ+x) := by
        apply (le_div_iff₀ (hu x hx)).mpr
        have hid : (1+1/(δ+x))*(δ+x)=δ+x+1 := by field_simp [(hu x hx).ne']
        rw [hid]
        linarith [hx.2]
      have he : 0≤ε/(δ+x) := div_nonneg hε (hu x hx).le
      dsimp [M,B]
      have hi' : 3/(δ+x)≤3*(A*δ)^(-(1/4:ℝ))*(δ+x)^(-(3/4:ℝ)) := by
        simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3)
      exact hh.trans (h3.trans (hi'.trans (le_add_of_nonneg_left he)))
  have hh := weighted_derivative_bound hf hm hδ l r hM hM0 hbound
  have he := band_envelope_integral hC hδ hδ1 hε (show 0≤B by dsimp [B]; positivity)
  have hh' := hh.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (energyConstant*(2+1/δ)))))
  exact band_normalized_bound hC hW hA hδ hδ1 hε (by simpa only [mul_assoc] using hh')

end OrdinaryHorizontalHalasz

end

end OAI
