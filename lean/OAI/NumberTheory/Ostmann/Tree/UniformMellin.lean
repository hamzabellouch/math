import OAI.NumberTheory.Ostmann.Tree.DiagonalMellin

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem uniform_mellin_bound (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (σ : (ZMod p)ˣ) (hσ : (σ:ZMod p)^2=1)
    (hg0 : g 0=0) (hg : l2Sq g ≤ 1) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖fourier (fun d => pairSpectrum g χ ((σ:ZMod p)*d)*χ d*η d) a‖^2) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
        ((correlationBound g:ℝ)^4+Real.sqrt (3/(p:ℝ))) := by
  let G := reciprocalTwist g η (-a*(σ:ZMod p))
  let T : ZMod p → ℂ := weightedAffine (fun r => conj (G r)) G
  have hpoint (lam : (ZMod p)ˣ) :
      ‖mean (diagonalPairValue g η a σ lam)‖^2 = ‖T ((σ:ZMod p)/(lam:ZMod p))‖^2 := by
    rw [diagonalPair_affine_mean g η a σ lam hσ hg0]
    simp only [norm_mul,Complex.norm_conj,mulChar_norm_unit,one_mul]
    rfl
  have hparse := mellin_parseval (fun lam : (ZMod p)ˣ => mean (diagonalPairValue g η a σ lam))
  simp_rw [diagonalPair_mellin g _ η a σ hg0,hpoint] at hparse
  rw [hparse]
  have hi : Function.Bijective (fun lam : (ZMod p)ˣ => σ/lam) :=
    (Equiv.mulLeft σ).bijective.comp inv_involutive.bijective
  have hs : (∑ lam : (ZMod p)ˣ, ‖T ((σ:ZMod p)/(lam:ZMod p))‖^2) =
      ∑ u : (ZMod p)ˣ, ‖T u‖^2 := by
    simpa only [Units.val_div_eq_div_val] using hi.sum_comp (fun u : (ZMod p)ˣ => ‖T u‖^2)
  rw [hs]
  have hT := reciprocalTwist_affine_bound g η (-a*(σ:ZMod p)) hg0 hg
  change l2Sq T ≤ _ at hT
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hN : 0 < (Fintype.card (ZMod p)ˣ:ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(∑ t : ZMod p, ‖T t‖^2) :=
      mul_le_mul_of_nonneg_left (sum_units_le _ (fun _ => sq_nonneg _)) (inv_nonneg.mpr hN.le)
    _ = ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*l2Sq T := by
      dsimp [l2Sq]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hT (div_nonneg hp.le hN.le)

end
end Ostmann.FiniteField

end OAI
