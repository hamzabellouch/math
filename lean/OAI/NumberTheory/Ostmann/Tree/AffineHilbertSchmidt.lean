import OAI.NumberTheory.Ostmann.Tree.AffineFourier

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate

theorem norm_sum_mul_sq_le {ι : Type*} (S : Finset ι) (v w : ι → ℂ) :
    ‖∑ i ∈ S, v i*w i‖^2 ≤ (∑ i ∈ S, ‖v i‖^2)*(∑ i ∈ S, ‖w i‖^2) := by
  calc
    _ ≤ (∑ i ∈ S, ‖v i*w i‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ i ∈ S, ‖v i‖*‖w i‖)^2 := by simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖v i‖) (fun i => ‖w i‖)

variable {p : ℕ} [Fact p.Prime]

def affineFrequencyCoefficient (c : (ZMod p)ˣ → ZMod p → ℂ)
    (u : (ZMod p)ˣ) (a : ZMod p) : ℂ :=
  ∑ b, c u b * ZMod.stdAddChar (((u⁻¹:(ZMod p)ˣ):ZMod p)*a*b)

theorem affineFrequencyCoefficient_eq_dft (c : (ZMod p)ˣ → ZMod p → ℂ)
    (u : (ZMod p)ˣ) (a : ZMod p) :
    affineFrequencyCoefficient c u a = ZMod.dft (c u) (-(((u⁻¹:(ZMod p)ˣ):ZMod p)*a)) := by
  simp only [affineFrequencyCoefficient, ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg]
  apply Finset.sum_congr rfl
  intro b _
  have he : (((u⁻¹:(ZMod p)ˣ):ZMod p)*a)*b = b*(((u⁻¹:(ZMod p)ˣ):ZMod p)*a) := by ring
  rw [he, mul_comm]

theorem affineFrequencyCoefficient_energy (c : (ZMod p)ˣ → ZMod p → ℂ)
    (u : (ZMod p)ˣ) :
    ∑ a : ZMod p, ‖affineFrequencyCoefficient c u a‖^2 =
      (p:ℝ) * ∑ b, ‖c u b‖^2 := by
  simp only [affineFrequencyCoefficient_eq_dft]
  have hi : Function.Bijective (fun a : ZMod p => -(((u⁻¹:(ZMod p)ˣ):ZMod p)*a)) :=
    (Equiv.neg (ZMod p)).bijective.comp (u⁻¹).mulLeft_bijective
  rw [hi.sum_comp (fun a => ‖ZMod.dft (c u) a‖^2), Supply.dft_parseval]

theorem unit_frequency_energy_le (f : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) :
    (∑ u : (ZMod p)ˣ, ‖fourier f (((u⁻¹:(ZMod p)ˣ):ZMod p)*a)‖^2) ≤ l2Sq f := by
  rw [← fourier_parseval]
  apply Finset.sum_le_sum_of_injOn
    (fun u : (ZMod p)ˣ => (((u⁻¹:(ZMod p)ˣ):ZMod p)*a))
  · intro u _ v _ h
    apply inv_injective
    exact Units.ext (mul_right_cancel₀ ha h)
  · exact Finset.subset_univ _
  · intro u _
    exact le_rfl
  · intro b _ _
    exact sq_nonneg _

theorem affineAction_l2Sq_le (c : (ZMod p)ˣ → ZMod p → ℂ) (f : ZMod p → ℂ)
    (hf : mean f = 0) :
    l2Sq (affineAction c f) ≤
      ((p:ℝ) * ∑ u, ∑ b, ‖c u b‖^2) * l2Sq f := by
  rw [← fourier_parseval]
  have hpoint (a : ZMod p) :
      ‖fourier (affineAction c f) a‖^2 ≤
        (∑ u, ‖affineFrequencyCoefficient c u a‖^2) * l2Sq f := by
    by_cases ha : a=0
    · subst a
      rw [fourier_affineAction]
      simp only [mul_zero, fourier_zero, hf,
        Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (l2Sq_nonneg f)
    · rw [fourier_affineAction]
      have hc := norm_sum_mul_sq_le Finset.univ
        (fun u => affineFrequencyCoefficient c u a)
        (fun u => fourier f (((u⁻¹:(ZMod p)ˣ):ZMod p)*a))
      exact hc.trans (mul_le_mul_of_nonneg_left (unit_frequency_energy_le f a ha)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ a : ZMod p, (∑ u, ‖affineFrequencyCoefficient c u a‖^2) * l2Sq f :=
      Finset.sum_le_sum (fun a _ => hpoint a)
    _ = ((p:ℝ) * ∑ u, ∑ b, ‖c u b‖^2) * l2Sq f := by
      rw [← Finset.sum_mul, Finset.sum_comm]
      simp only [affineFrequencyCoefficient_energy, Finset.mul_sum]

end
end Ostmann.FiniteField

end OAI
