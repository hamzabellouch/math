import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.DyadicLongScales

namespace OAI

/-! The horizontal derivative bound for arbitrary selected scales above
a lower length cutoff. It is independent of scale count and dimension. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem selected_dyadic_reciprocals (N : ℕ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, r ≤ L/(2:ℝ)^j.val) :
    (∑ j ∈ s, (L/(2:ℝ)^j.val)⁻¹) ≤ 4/r := by
  have hp : 0 < r/2 := by positivity
  calc
    _ ≤ ∑ j : Fin N, if r/2 < L/(2:ℝ)^j.val then (L/(2:ℝ)^j.val)⁻¹ else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun j _ _ => by split_ifs <;> positivity) |>.trans' ?_
      apply Finset.sum_le_sum
      intro j hj
      rw [ite_eq_left (lt_of_lt_of_le (by linarith) (hs j hj))]
    _ ≤ 2/(r/2) := sum_long_dyadic_reciprocals N L (r/2) hL hp
    _ = 4/r := by ring

theorem tile_weighted_vector_derivative_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y C w : ℝ) (hl : 0 < l) (hW : W ≠ 0) (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hc : ∀ i, ‖c i‖ ≤ 1)
    (hf : ∀ i k, w*‖deriv (f i k) x‖ ≤ (C/l)*
      (lineEnvelope (a+l*(index i).1) l 3 x * lineEnvelope (b+W*(index i).2) W 2 y)) :
    w*‖deriv (vectorPacketSynthesis c f) x‖ ≤ (C/l)*(4*Real.pi)^2 := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul]
    positivity
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hscaled (i : ι) (k : κ) : ‖deriv (f i k) x‖ ≤ ((C/w)/l)*
      (lineEnvelope (a+l*(index i).1) l 3 x * lineEnvelope (b+W*(index i).2) W 2 y) := by
    apply (mul_le_mul_iff_right₀ hwp).mp
    calc
      _ ≤ (C/l)*(lineEnvelope (a+l*(index i).1) l 3 x *
          lineEnvelope (b+W*(index i).2) W 2 y) := hf i k
      _ = _ := by field_simp
  have h := tile_vectorPacketSynthesis_deriv_bound c f index hinj a b l W x y (C/w)
    hl hW (div_nonneg hC hw) hc hscaled
  have hh := mul_le_mul_of_nonneg_left h hw
  convert hh using 1
  field_simp


theorem selected_scale_weighted_derivative_bound {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W x y C w r : ℝ) (hL : 0 < L) (hW : W ≠ 0)
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hr : 0 < r)
    (hc : ∀ j i, ‖c j i‖ ≤ 1)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, r ≤ L/(2:ℝ)^j.val)
    (hf : ∀ j i k, w*‖deriv (f j i k) x‖ ≤ (C/(L/(2:ℝ)^j.val))*
      (lineEnvelope (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) 3 x *
        lineEnvelope (b+W*(site j i).2) W 2 y)) :
    w*‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖ ≤
      4*(C*(4*Real.pi)^2)/r := by
  have hd := HasDerivAt.fun_sum (u := s) (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (c j) (f j) x).differentiableAt.hasDerivAt)
  rw [hd.deriv]
  calc
    _ ≤ w*(∑ j ∈ s, ‖deriv (vectorPacketSynthesis (c j) (f j)) x‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ j ∈ s, w*‖deriv (vectorPacketSynthesis (c j) (f j)) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ s, (C/(L/(2:ℝ)^j.val))*(4*Real.pi)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact tile_weighted_vector_derivative_bound (c j) (f j) (site j) (hinj j)
        a b (L/(2:ℝ)^j.val) W x y C w (div_pos hL (by positivity)) hW hC hw (hc j) (hf j)
    _ = (C*(4*Real.pi)^2)*(∑ j ∈ s, (L/(2:ℝ)^j.val)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv]
      ring
    _ ≤ (C*(4*Real.pi)^2)*(4/r) :=
      mul_le_mul_of_nonneg_left (selected_dyadic_reciprocals N L r hL hr s hs) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
