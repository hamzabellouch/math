import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationFibers

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

instance localCorrelation_lcm_neZero {d e : ℕ} [NeZero d] [NeZero e] :
    NeZero (Nat.lcm d e) := ⟨Nat.lcm_ne_zero (NeZero.ne d) (NeZero.ne e)⟩

theorem normalized_transform_correlation_le {d e : ℕ} [NeZero d] [NeZero e]
    (f : ZMod d → ℂ) (g : ZMod e → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (h : ZMod (Nat.lcm d e)) :
    ‖normalizedCoefficient
      (transformCorrelation (Nat.dvd_lcm_left d e) (Nat.dvd_lcm_right d e) f g) h‖ ≤
      (Nat.gcd d e : ℝ) / (Real.sqrt d * Real.sqrt e) := by
  classical
  let P : ZMod d × ZMod e → Prop := fun z =>
    frequencyEmbedding (q := Nat.lcm d e) z.1 -
      frequencyEmbedding (q := Nat.lcm d e) z.2 = -h
  have hnum : ‖∑ x : ZMod d, ∑ y : ZMod e,
      if P (x, y) then f x * conj (g y) else 0‖ ≤ Nat.gcd d e := by
    rw [← Fintype.sum_prod_type (fun z : ZMod d × ZMod e =>
      if P z then f z.1 * conj (g z.2) else 0)]
    calc
      _ ≤ ∑ z : ZMod d × ZMod e, ‖if P z then f z.1 * conj (g z.2) else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ z : ZMod d × ZMod e, if P z then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro z _
        split_ifs with hz
        · rw [norm_mul, Complex.norm_conj]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
        · simp
      _ = ((Finset.univ.filter P).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ Nat.gcd d e := by
        apply Nat.cast_le.mpr
        convert local_frequency_fiber_card_le_gcd (d := d) (e := e) (-h) using 1
        congr 1
  rw [correlation_coefficient_expansion]
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hnum (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem unitaryDFT_unit_dilation {d : ℕ} [NeZero d]
    (f : ZMod d → ℂ) (c : (ZMod d)ˣ) (s : ZMod d) :
    Supply.unitaryDFT f ((c : ZMod d) * s) =
      Supply.unitaryDFT (fun x => f (((c⁻¹ : (ZMod d)ˣ) : ZMod d) * x)) s := by
  unfold Supply.unitaryDFT
  rw [ZMod.dft_comp_unitMul]
  simp

theorem normalized_unit_transform_correlation_le {d e : ℕ} [NeZero d] [NeZero e]
    (f : ZMod d → ℂ) (g : ZMod e → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (c : (ZMod d)ˣ) (c' : (ZMod e)ˣ) (h : ZMod (Nat.lcm d e)) :
    ‖normalizedCoefficient (fun s : ZMod (Nat.lcm d e) =>
      Supply.unitaryDFT f ((c : ZMod d) * ZMod.castHom (Nat.dvd_lcm_left d e) (ZMod d) s) *
      conj (Supply.unitaryDFT g ((c' : ZMod e) *
        ZMod.castHom (Nat.dvd_lcm_right d e) (ZMod e) s))) h‖ ≤
      (Nat.gcd d e : ℝ) / (Real.sqrt d * Real.sqrt e) := by
  simp_rw [unitaryDFT_unit_dilation]
  exact normalized_transform_correlation_le _ _ (fun _ => hf _) (fun _ => hg _) h

end Ostmann.QuadraticCenter

end

end OAI
