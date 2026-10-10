import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.Whitening

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A I : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [Nonempty I]

def meanDensity (r : I → Matrix A A ℂ) : Matrix A A ℂ :=
  (Fintype.card I : ℂ)⁻¹ • ∑ i, r i

def regularizedMean (r : I → Matrix A A ℂ) (ε : ℝ) : Matrix A A ℂ :=
  (1-ε : ℂ) • meanDensity r + (ε/(Fintype.card A) : ℂ) • 1

omit [Fintype A] [DecidableEq A] [Nonempty A] [Nonempty I] in
lemma meanDensity_psd (r : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef) :
    (meanDensity r).PosSemidef := by
  exact (Matrix.posSemidef_sum _ (fun i _ => hr i)).smul (by positivity)

omit [DecidableEq A] [Nonempty A] in
lemma meanDensity_trace (r : I → Matrix A A ℂ) (ht : ∀ i, (r i).trace = 1) :
    (meanDensity r).trace = 1 := by
  simp [meanDensity,Matrix.trace_sum,Matrix.trace_smul,ht,
    ne_of_gt (Fintype.card_pos : 0 < Fintype.card I)]

lemma regularizedMean_trace (r : I → Matrix A A ℂ) (ht : ∀ i, (r i).trace = 1) (ε : ℝ) :
    (regularizedMean r ε).trace = 1 := by
  simp [regularizedMean,Matrix.trace_smul,meanDensity_trace r ht,Matrix.trace_one,
    ne_of_gt (Fintype.card_pos : 0 < Fintype.card A)]

omit [Nonempty I] in
lemma regularizedMean_posDef (r : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (regularizedMean r ε).PosDef := by
  rw [regularizedMean,add_comm]
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.one.smul
    exact_mod_cast div_pos hε (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A))
  · exact (meanDensity_psd r hr).smul (by exact_mod_cast sub_nonneg.mpr hε1)

omit [Nonempty A] [Nonempty I] in
lemma regularizedMean_even (r : I → Matrix A A ℂ) (p : A → Bool)
    (he : ∀ i a b, p a ≠ p b → r i a b = 0) (ε : ℝ) :
    ∀ a b, p a ≠ p b → regularizedMean r ε a b = 0 := by
  intro a b hab
  have hn : a ≠ b := fun h => hab (congrArg p h)
  simp [regularizedMean,meanDensity,Matrix.smul_apply,Matrix.sum_apply,he,hab,hn]

omit [Nonempty A] in
lemma whitened_column_budget (r : I → Matrix A A ℂ) (v C : Matrix A A ℂ)
    (_hr : ∀ i, (r i).PosSemidef) (hv : v.PosSemidef) (htv : v.trace = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hC : C.IsHermitian)
    (hCMC : C * regularizedMean r ε * C = 1) :
    (1-ε) * (∑ i, (C * r i * C * v).trace.re) ≤ Fintype.card I := by
  have hd : (regularizedMean r ε - (1-ε:ℂ) • meanDensity r).PosSemidef := by
    simp only [regularizedMean,add_sub_cancel_left]
    exact Matrix.PosSemidef.one.smul (by exact_mod_cast div_nonneg hε (Nat.cast_nonneg (Fintype.card A)))
  have hc := hd.mul_mul_conjTranspose_same C
  rw [hC.eq,Matrix.mul_sub,Matrix.sub_mul,hCMC,Matrix.mul_smul,Matrix.smul_mul] at hc
  have ht := trace_product_re_nonneg hc hv
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,htv] at ht
  simp only [Complex.sub_re,Complex.one_re,smul_eq_mul,Complex.mul_re,Complex.sub_im,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,zero_mul] at ht
  have hn : (Fintype.card I : ℝ) > 0 := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (C * meanDensity r * C * v).trace.re =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, (C * r i * C * v).trace.re := by
    simp [meanDensity,Matrix.mul_sum,Matrix.sum_mul,
      Matrix.trace_sum,Matrix.trace_smul,Complex.mul_re]
  rw [hs] at ht
  have := mul_nonneg hn.le ht
  field_simp at this
  nlinarith

end BinaryCoordinateSweeps.Density

end

end OAI
