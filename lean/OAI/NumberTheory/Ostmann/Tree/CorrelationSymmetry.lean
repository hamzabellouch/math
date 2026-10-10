import OAI.NumberTheory.Ostmann.Tree.TwistedPairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem mixedCorrelation_conj (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    mixedCorrelation (fun x => conj (g x)) χ a=
      conj (mixedCorrelation g (star χ) (-a)) := by
  unfold mixedCorrelation
  rw [← mean_conj]
  congr 1
  funext x
  simp only [map_mul,MulChar.star_apply,RCLike.star_def,Supply.conj_stdAddChar,
    neg_mul,neg_neg]
  simp

theorem correlationBound_conj_le (g : ZMod p → ℂ) :
    correlationBound (fun x => conj (g x))≤correlationBound g := by
  unfold correlationBound
  apply Finset.sup_le
  intro z _
  have h := norm_mixedCorrelation_le g (star z.1) (-z.2)
  rw [mixedCorrelation_conj]
  have hh : ‖conj (mixedCorrelation g (star z.1) (-z.2))‖≤(correlationBound g:ℝ) := by
    simpa only [Complex.norm_conj] using h
  exact_mod_cast hh

theorem correlationBound_conj (g : ZMod p → ℂ) :
    correlationBound (fun x => conj (g x))=correlationBound g := by
  apply le_antisymm (correlationBound_conj_le g)
  simpa only [starRingEnd_apply,star_star] using correlationBound_conj_le (fun x => conj (g x))

theorem norm_mixedCorrelation_le_one (g : ZMod p → ℂ) (hg : l2Sq g≤1)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ‖mixedCorrelation g χ a‖≤1 := by
  let H : ZMod p → ℂ := fun x => g x*χ x*ZMod.stdAddChar (a*x)
  have hnorm (x : ZMod p) : ‖H x‖≤‖g x‖ := by
    simp only [H,norm_mul,(ZMod.stdAddChar : AddChar (ZMod p) ℂ).norm_apply,mul_one]
    exact (mul_le_mul_of_nonneg_left (mulChar_norm_le_one χ x) (norm_nonneg _)).trans_eq (mul_one _)
  have hH : l2Sq H≤l2Sq g := by
    unfold l2Sq
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hnorm x) 2)
  have hc := meanInner_norm_sq_le (fun _ => (1:ℂ)) H
  have he : meanInner (fun _ => (1:ℂ)) H=mixedCorrelation g χ a := by simp [meanInner,mixedCorrelation,H]
  rw [he,l2Sq_const] at hc
  norm_num at hc
  have h := hc.trans (hH.trans hg)
  nlinarith only [h,norm_nonneg (mixedCorrelation g χ a)]

theorem correlationBound_le_one (g : ZMod p → ℂ) (hg : l2Sq g≤1) :
    (correlationBound g:ℝ)≤1 := by
  have h : correlationBound g≤1 := by
    unfold correlationBound
    apply Finset.sup_le
    intro z _
    exact_mod_cast norm_mixedCorrelation_le_one g hg z.1 z.2
  exact_mod_cast h

end
end Ostmann.FiniteField

end OAI
