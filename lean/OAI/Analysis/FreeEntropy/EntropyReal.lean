import OAI.Analysis.FreeEntropy.HeatAnalysis

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation

 theorem signed_lintegral_toEReal {α : Type u1} [MeasurableSpace α] {μ : Measure α}
    {b f : α → ℝ≥0∞} {r : α → ℝ}
    (hb : ∀ᵐ x ∂μ, b x ≠ ⊤) (hf : ∀ᵐ x ∂μ, f x ≠ ⊤)
    (hr : ∀ᵐ x ∂μ, r x = (b x).toReal - (f x).toReal) (hi : Integrable r μ) :
    (∫⁻ x, b x - f x ∂μ).toEReal - (∫⁻ x, f x - b x ∂μ).toEReal =
      ((∫ x, r x ∂μ : ℝ) : EReal) := by
  have hp : ∫⁻ x, b x - f x ∂μ = ∫⁻ x, ENNReal.ofReal (r x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hb,hf,hr] with x hb hf hr
    rw [hr, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
      ENNReal.ofReal_toReal hf]
  have hn : ∫⁻ x, f x - b x ∂μ = ∫⁻ x, ENNReal.ofReal (-r x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hb,hf,hr] with x hb hf hr
    rw [hr, neg_sub, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
      ENNReal.ofReal_toReal hf]
  have hnf : (∫⁻ x, ENNReal.ofReal (-r x) ∂μ) < ∞ := by
    simpa only [Pi.neg_apply] using lintegral_ofReal_finite hi.neg
  rw [hp,hn, ← EReal.coe_ennreal_toReal (lintegral_ofReal_finite hi).ne,
    ← EReal.coe_ennreal_toReal hnf.ne,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  norm_cast

namespace Model
variable (p : ℕ) [NeZero p]
def gaussianEntropy (a : ℝ) : ℝ :=
  (p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
    (1/2 : ℝ) * ∑ i : Fin (p+1), Real.log (a + variance p i)
 theorem chiStar_integral (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      (((p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
        (1/2 : ℝ) * ∫ s in Ioi (0 : ℝ), (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s) : ℝ) : EReal) := by
  let b : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((p+1 : ℕ)/(1+s))
  let f : ℝ → ℝ≥0∞ := fun s => freeFisher (τ p) (doublyNoised p a s)
  let r : ℝ → ℝ := fun s => (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)
  have hb : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), b s ≠ ⊤ := Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top)
  have hf : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), f s ≠ ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (doublyNoised_fisher_le p a s ha.le hs.le (by linarith [show 0<s from hs]))
  have hr : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), r s = (b s).toReal - (f s).toReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hu : 0 < a+s := by linarith [show 0<s from hs]
    have hs0 : 0 < s := hs
    dsimp [r,b,f,heatFisherReal]
    rw [doublyNoised_fisher_eq p a s ha.le hs.le hu, ENNReal.toReal_ofReal (by positivity)]
  have he := signed_lintegral_toEReal hb hf hr (entropyIntegrand_integrable p hp a ha)
  unfold chiStar
  change (_ : EReal) + (1/2 : EReal) * (∫⁻ s in Ioi (0:ℝ), b s - f s).toEReal -
    (1/2 : EReal) * (∫⁻ s in Ioi (0:ℝ), f s - b s).toEReal = _
  have ht := entropy_parts_finite (f := f) (n := (p+1 : ℕ)) ha (by linarith : 0 < a+4)
    (fun s hs => by simpa [f,add_assoc,add_comm,add_left_comm] using
      doublyNoised_fisher_lower p hp a s ha.le hs.le (by linarith))
    (fun s hs => doublyNoised_fisher_le p a s ha.le hs.le (by linarith))
  rw [← EReal.coe_ennreal_toReal ht.1.ne, ← EReal.coe_ennreal_toReal ht.2.ne] at he ⊢
  have he' : (∫⁻ s in Ioi (0:ℝ), b s - f s).toReal -
      (∫⁻ s in Ioi (0:ℝ), f s - b s).toReal = ∫ s in Ioi (0:ℝ), r s := by
    exact_mod_cast he
  change (((p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
    (1/2 : ℝ)*(∫⁻ s in Ioi (0:ℝ), b s-f s).toReal -
    (1/2 : ℝ)*(∫⁻ s in Ioi (0:ℝ), f s-b s).toReal : ℝ) : EReal) = _
  congr 1
  change _ = (p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
    (1/2 : ℝ)*∫ s in Ioi (0:ℝ), r s
  linarith [he']

 theorem covarianceCorrection_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => ∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) (Ioi 0) :=
  integrable_finsetSum _ (fun i _ => reciprocalDifference_integrable (by linarith [variance_nonneg p i]))
 theorem covarianceCorrection_integral (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), ∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) =
      ∑ i : Fin (p+1), Real.log (a+variance p i) := by
  rw [integral_finsetSum _ (fun i _ => reciprocalDifference_integrable (by linarith [variance_nonneg p i]))]
  apply sum_congr rfl
  intro i _
  exact reciprocalDifference_integral (by linarith [variance_nonneg p i])
 theorem covarianceCorrection_identity (a s : ℝ) :
    (∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) -
      ((p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) = fisherDeficit p (a+s) := by
  simp only [reciprocalDifference, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [fisherDeficit, covarianceFisher, heatFisherReal, one_div]
  have he : (∑ i : Fin (p+1), (a+variance p i+s)⁻¹) = ∑ i : Fin (p+1), (variance p i+(a+s))⁻¹ := by
    apply sum_congr rfl; intro i _; congr 1; ring
  rw [he]
  simp only [div_eq_mul_inv]
  ring
 theorem fisherDeficit_shift_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => fisherDeficit p (a+s)) (Ioi 0) := by
  have hh := (covarianceCorrection_integrable p a ha).sub (entropyIntegrand_integrable p hp a ha)
  change IntegrableOn (fun s => (∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) -
    ((p+1 : ℕ)/(1+s) - heatFisherReal p (a+s))) (Ioi 0) at hh
  simpa only [covarianceCorrection_identity] using hh
 theorem chiStar_covariance_formula (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      ((gaussianEntropy p a - (1/2 : ℝ) * ∫ s in Ioi (0:ℝ), fisherDeficit p (a+s) : ℝ) : EReal) := by
  rw [chiStar_integral p hp a ha]
  congr 1
  have he : (∫ s in Ioi (0:ℝ), fisherDeficit p (a+s)) =
      (∑ i : Fin (p+1), Real.log (a+variance p i)) -
      (∫ s in Ioi (0:ℝ), (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) := by
    simp_rw [← covarianceCorrection_identity p a]
    rw [integral_sub (covarianceCorrection_integrable p a ha) (entropyIntegrand_integrable p hp a ha),
      covarianceCorrection_integral p a ha]
  rw [he]
  unfold gaussianEntropy
  ring
end Model
end FiniteEntropySeparation

end

end OAI
