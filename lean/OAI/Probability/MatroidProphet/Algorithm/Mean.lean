import OAI.Probability.MatroidProphet.GroupConditioning
import OAI.Probability.MatroidProphet.SafeParity
import OAI.Probability.MatroidProphet.Residual.Global

namespace OAI

namespace MatroidProphet
open Finset

lemma fairParityExpectation_mono {f g : Bool → ℝ} (h : ∀ p, f p ≤ g p) :
    fairParityExpectation f ≤ fairParityExpectation g := by
  have h0 := h false
  have h1 := h true
  unfold fairParityExpectation
  linarith

lemma fairParityExpectation_const (c : ℝ) : fairParityExpectation (fun _ => c) = c := by
  unfold fairParityExpectation
  ring

lemma fairParityExpectation_add (f g : Bool → ℝ) :
    fairParityExpectation (fun p => f p + g p) = fairParityExpectation f + fairParityExpectation g := by
  unfold fairParityExpectation
  ring

lemma fairParityExpectation_mul (c : ℝ) (f : Bool → ℝ) :
    fairParityExpectation (fun p => c * f p) = c * fairParityExpectation f := by
  unfold fairParityExpectation
  ring

lemma bitsExpectation_fairParity {α : Type*} [DecidableEq α] (q : α → ℝ)
    (V : Finset α) (f : Finset α → Bool → ℝ) :
    bitsExpectation q V (fun T => fairParityExpectation (f T)) =
      fairParityExpectation (fun p => bitsExpectation q V (fun T => f T p)) := by
  simp only [fairParityExpectation, div_eq_mul_inv]
  rw [bitsExpectation_mul_right, bitsExpectation_add]

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def mainMean (d : MainMasks n) (f : MainMasks n → ℝ) : ℝ :=
  tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
    univ (fun D C T => fairParityExpectation (fun p => f {withMasks d D C T with odd := p}))

lemma mainMean_mono (d : MainMasks n) {f g : MainMasks n → ℝ}
    (h : ∀ d', d'.H = d.H → f d' ≤ g d') : mainMean d f ≤ mainMean d g := by
  apply tripleMaskExpectation_mono _ _ _ (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => constants_positive.2.2.1.le) (fun _ => by norm_num [thinningRate])
    (fun _ => constants_positive.2.2.1.le) (fun _ => by norm_num [thinningRate])
  intro D hD C hC T hT
  exact fairParityExpectation_mono (fun p => h _ rfl)

lemma mainMean_const (d : MainMasks n) (c : ℝ) : mainMean d (fun _ => c) = c := by
  simp only [mainMean, fairParityExpectation_const, tripleMaskExpectation_const]

lemma mainMean_add (d : MainMasks n) (f g : MainMasks n → ℝ) :
    mainMean d (fun d' => f d' + g d') = mainMean d f + mainMean d g := by
  simp only [mainMean, fairParityExpectation_add, tripleMaskExpectation_add]

lemma mainMean_mul (d : MainMasks n) (c : ℝ) (f : MainMasks n → ℝ) :
    mainMean d (fun d' => c * f d') = c * mainMean d f := by
  simp only [mainMean, fairParityExpectation_mul, tripleMaskExpectation_mul]

lemma mainMean_guard_count (d : MainMasks n) (K : Finset (Fin n)) :
    mainMean d (fun d' => ((d'.C ∩ K).card : ℝ)) = thinningRate * K.card := by
  unfold mainMean tripleMaskExpectation MainAlgorithm.withMasks
  simp only [fairParityExpectation_const, bitsExpectation_const]
  have hc : bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun C => ((C ∩ K).card : ℝ)) = thinningRate * K.card := by
    simp_rw [Finset.inter_comm _ K]
    rw [bitsExpectation_card_inter _ univ K (subset_univ _)]
    simp [mul_comm]
  rw [hc]

end MainAlgorithm
end MatroidProphet

end OAI
