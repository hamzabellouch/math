import OAI.Analysis.FreeEntropy.FatouFlow

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
 theorem heatFisher_shift_intervalIntegrable (hp : 2≤p) {h a t : ℝ}
    (hh : 0<h) (ha : 0≤a) (hat : a≤t) :
    IntervalIntegrable (fun s => heatFisherReal p (h+s)) volume a t := by
  have hi := (heatFisherReal_intervalIntegrable p hp (h+a) (h+t) (by linarith) (by linarith)).comp_add_left h
  simpa only [add_sub_cancel_left] using hi
 theorem matrixFlow_limit (hp : 2≤p) {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R : ℝ} (hh : 0<h) (hR : 0≤R)
    (hn : ∀k,(diagonalMicrostates (τ p) (X p h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (p+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (τ p) (X p h) R k (D k))
    {a t β L : ℝ} (ha : 0<a) (hat : a≤t)
    (hinit : ∀k,β≤normalizedMatrixEntropy (μ k) a)
    (hterm : ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) t≤L) :
    β+(1/2:ℝ)*(∫u in (h+a)..(h+t),heatFisherReal p u)≤L := by
  have hnorm k : ∀ᵐy ∂μ k,‖y‖≤Real.sqrt (((p+1:ℕ):ℝ)*D k)*R :=
    FreeTensor.diagonalMicrostates_norm_ae (X p h) hR μ hμ k
  have hl s (hs : s∈Ioc a t) : ENNReal.ofReal (heatFisherReal p (h+s))≤
      liminf (fun k => ENNReal.ofReal (normalizedMatrixFisher (μ k) s)) atTop := by
    have hs0 : 0<s := ha.trans hs.1
    have hb := FreeTensor.freeFisher_le_liminf_matrixFisher hD0 hD (oldNoise p) (X p h)
      (X_mem_background p h) (X_selfAdjoint p h) hR hn (auxiliaryIndex p)
      (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) μ hμ hs0
    change freeFisher (τ p) (doublyNoised p h s)≤_ at hb
    rw [doublyNoised_fisher_eq p h s hh.le hs0.le (by linarith)] at hb
    simpa only [heatFisherReal,ENNReal.ofReal_toReal (heatFisher_ne_top p (h+s) (by linarith))] using hb
  have hb := matrixFlow_limit_bound hD0 μ (fun k => Real.sqrt (((p+1:ℕ):ℝ)*D k)*R)
    (fun k => by positivity) hnorm (fun s => heatFisherReal p (h+s)) ha hat
    (heatFisher_shift_intervalIntegrable p hp hh ha.le hat) (fun _ _ => ENNReal.toReal_nonneg) hl hinit
    (fun ε hε => hterm.mono (fun k hk => by linarith))
  rwa [intervalIntegral.integral_comp_add_left] at hb
 theorem heatFisher_short_bound (hp : 2≤p) {h a : ℝ} (hh : 0<h) (ha : 0≤a) :
    (1/2:ℝ)*(∫u in h..(h+a),heatFisherReal p u)≤((p+1:ℕ):ℝ)*a/(2*h) := by
  have hi := heatFisherReal_intervalIntegrable p hp h (h+a) hh (by linarith)
  have hb := intervalIntegral.integral_mono_on (show h≤h+a by linarith) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ((p+1:ℕ):ℝ)/h) volume h (h+a))
    (fun u hu => (heatFisherReal_upper p u (hh.trans_le hu.1)).trans
      (div_le_div_of_nonneg_left (by positivity) hh hu.1))
  rw [intervalIntegral.integral_const] at hb
  simp only [add_sub_cancel_left,smul_eq_mul] at hb
  calc
    _ ≤ (1/2:ℝ)*(a*(((p+1:ℕ):ℝ)/h)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring
end FiniteEntropySeparation.Model

end

end OAI
