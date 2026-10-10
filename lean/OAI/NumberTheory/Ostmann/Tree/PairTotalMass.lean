import OAI.NumberTheory.Ostmann.Tree.PairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem pairFourthMass_total (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g ≤ 1) :
    (∑ χ : MulChar (ZMod p) ℂ, pairFourthMass g χ) ≤
      2*(p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hN : 0 < (Fintype.card (ZMod p)ˣ:ℝ) := by exact_mod_cast Fintype.card_pos
  have henergy : (∑ x : ZMod p, ‖g x‖^2) ≤ (p:ℝ) := by
    have hh : (∑ x : ZMod p, ‖g x‖^2)/(p:ℝ) ≤ 1 := by
      simpa only [l2Sq, div_eq_mul_inv, mul_comm] using hg
    simpa only [one_mul] using (div_le_iff₀ hp).mp hh
  have hpair : (∑ d : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, ‖bottomPair g d t‖^2) ≤ (p:ℝ)^2 :=
    (bottomPair_total_energy g hg0).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) henergy 2)
  have hunit (d : (ZMod p)ˣ) :
      (∑ χ : MulChar (ZMod p) ℂ, ‖pairSpectrum g χ d‖^2) =
        (Fintype.card (ZMod p)ˣ:ℝ)⁻¹ * ∑ t : (ZMod p)ˣ, ‖bottomPair g d t‖^2 := by
    simp only [pairSpectrum_unit g _ d hg0]
    exact mellin_parseval _
  have hnonzero : (∑ d : (ZMod p)ˣ, ∑ χ : MulChar (ZMod p) ℂ, ‖pairSpectrum g χ d‖^2) ≤
      (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(p:ℝ)^2 := by
    simp_rw [hunit]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hpair (inv_nonneg.mpr hN.le)
  have hzero : (∑ χ : MulChar (ZMod p) ℂ, ‖pairSpectrum g χ 0‖^2) ≤
      (p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ) := by
    simp only [pairSpectrum_zero g _ hg0, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, mulChar_card, nsmul_eq_mul]
    have hm : ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*l2Sq g ≤
        (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ) := by
      exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _)
    calc
      _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (div_nonneg hp.le hN.le) (l2Sq_nonneg g)) hm 2) hN.le
      _ = _ := by field_simp
  have hsplit : (∑ χ : MulChar (ZMod p) ℂ, pairFourthMass g χ) =
      (p:ℝ)⁻¹ * ((∑ d : (ZMod p)ˣ, ∑ χ : MulChar (ZMod p) ℂ, ‖pairSpectrum g χ d‖^2) +
        ∑ χ : MulChar (ZMod p) ℂ, ‖pairSpectrum g χ 0‖^2) := by
    simp_rw [pairFourthMass_eq_l2Sq, l2Sq]
    rw [← Finset.mul_sum, Finset.sum_comm, ← sum_units_add_zero]
  rw [hsplit]
  calc
    _ ≤ (p:ℝ)⁻¹*((Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(p:ℝ)^2+
        (p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hnonzero hzero) (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp; ring

end
end Ostmann.FiniteField

end OAI
