import OAI.Analysis.CircleDomains.Uniformization.LimitHeightBounds

namespace OAI

/-! Uniform compactness for heights when the retained model varies but
the error-energy budgets remain bounded. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem heights_equicontinuous_of_log_bound {ι : Type*} (v : ι → ℂ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hlog : ∀ i c r, 0 < r → r ≤ 1 → ∀ z ∈ closedBall c r,
      |v i c-v i z|^2*Real.log (1/r) ≤
        16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)) :
    Equicontinuous v := by
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let C := 16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let L := (C+1)/ε^2
  have hL : 0 < L := div_pos (by linarith) (sq_pos_of_pos hε)
  let δ := Real.exp (-L)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL.le)
  have hlg : Real.log (1/δ) = L := by
    dsimp only [δ]
    rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hEL : ε^2*L = C+1 := by dsimp only [L]; field_simp
  refine ⟨δ, hδ, ?_⟩
  intro z hz i
  have hh := hlog i c δ hδ hδ1 z (mem_closedBall.mpr hz.le)
  rw [hlg] at hh
  change |v i c-v i z|^2*L ≤ C at hh
  rw [Real.dist_eq]
  by_contra hn
  have hp := pow_le_pow_left₀ hε.le (le_of_not_gt hn) 2
  have hm := mul_le_mul_of_nonneg_right hp hL.le
  nlinarith

 theorem limiting_heights_equicontinuous {ι : Type*}
    (φ : ι → ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ i n, PlaneLocalWeakComplex (fun p => φ i n (complexPlaneCoordinates p)))
    (v : ι → ℂ → ℝ)
    (hv : ∀ i, TendstoLocallyUniformly (fun n z => (φ i n z).im) (v i) atTop)
    {B : ℝ} (hB : 0 ≤ B)
    (hI : ∀ i n, Integrable (fun p => (D i n).imagGradient p 0^2+((D i n).imagGradient p 1-1)^2))
    (hE : ∀ i n, (∫ p, (D i n).imagGradient p 0^2+((D i n).imagGradient p 1-1)^2) ≤ B) :
    Equicontinuous v := by
  apply heights_equicontinuous_of_log_bound v hB
  intro i c r hr hr1 z hz
  exact limit_height_log_bound (φ i) (D i) (hv i) (hI i) (hE i) c hr hr1
    (T := ‖c‖+2) (by linarith) (mem_closedBall_self hr.le) hz

end CircleDomainRigidity

end

end OAI
