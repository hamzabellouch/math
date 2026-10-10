import OAI.Geometry.RCD.Metric.EuclideanGreenIdentity
import OAI.Geometry.RCD.Coordinates.GevreyCutoffConstruction

namespace OAI

/-! # Compact extensions of local Euclidean harmonic functions -/

open Set Metric Filter MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff Topology

noncomputable section
namespace RegularPointCoordinates

/-- A smooth cutoff supported inside the differentiability region produces
a global smooth product, even when the original function is only local. -/
theorem contDiff_mul_of_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f χ : E → ℝ} {k : ℕ∞ω}
    (hf : ContDiffOn ℝ k f Ω) (hχ : ContDiff ℝ k χ) (hs : tsupport χ ⊆ Ω) :
    ContDiff ℝ k (fun x => χ x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ω
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hΩ.mem_nhds hx))
  · have ht : x ∉ tsupport χ := fun h => hx (hs h)
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
    simp only [hy,Pi.zero_apply,zero_mul]

/-- A normalized local harmonic model has a global compact C² extension
which agrees on the half ball and never increases its pointwise magnitude. -/
theorem EuclideanHarmonicModel.compact_extension {n : ℕ} {S : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) :
    ∃ F : Euclidean n → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      tsupport F ⊆ closedBall 0 (3*S/4) ∧
      (∀ x ∈ ball (0 : Euclidean n) (S/2), F x = w.value x) ∧
      (∀ x, |F x| ≤ |w.value x|) := by
  obtain ⟨ψ⟩ := euclideanGevreyCutoffInput n
  let a := 4/S
  have ha : 0 < a := by positivity
  let χ := fun x : Euclidean n => ψ.value (a • x)
  have hc : ContDiff ℝ 2 χ := (ψ.smooth.comp (contDiff_id.const_smul a)).of_le (by simp)
  have hs : tsupport χ ⊆ closedBall 0 (3*S/4) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hx' : a • x ∈ tsupport ψ.value := subset_tsupport ψ.value hx
    have hb := ψ.support hx'
    have hn : a*‖x‖ ≤ 3 := by
      simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ha] using hb
    simp only [mem_closedBall,dist_zero_right]
    dsimp only [a] at hn
    rw [div_mul_eq_mul_div] at hn
    have hh := (div_le_iff₀ hS).mp hn
    linarith
  have hsΩ : tsupport χ ⊆ ball 0 S := hs.trans (closedBall_subset_ball (by linarith))
  let F := fun x => χ x*w.value x
  have hF : ContDiff ℝ 2 F := contDiff_mul_of_tsupport_subset isOpen_ball w.harmonic.contDiffOn hc hsΩ
  have hFs : tsupport F ⊆ closedBall 0 (3*S/4) := tsupport_mul_subset_left.trans hs
  refine ⟨F,hF,(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hFs,hFs,?_,?_⟩
  · intro x hx
    have hx' : ‖x‖ < S/2 := by simpa only [mem_ball,dist_zero_right] using hx
    have hh : ‖a • x‖ ≤ 2 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
      dsimp only [a]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hS).mpr
      linarith
    change ψ.value (a • x)*w.value x = w.value x
    rw [ψ.core _ hh,one_mul]
  · intro x
    change |ψ.value (a • x)*w.value x| ≤ |w.value x|
    rw [abs_mul,abs_of_nonneg (ψ.nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (ψ.le_one _)

/-- The distributional Laplacian has no support outside the original
function's support. -/
theorem laplacian_eq_zero_of_notMem_tsupport {n : ℕ} (g : Euclidean n → ℝ)
    {x : Euclidean n} (hx : x ∉ tsupport g) : (Δ g) x = 0 := by
  have he := laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hx)
  have he' : (Δ g) x = (Δ (fun _ : Euclidean n => (0:ℝ))) x := he.self_of_nhds
  simpa only [laplacian_const,Pi.zero_apply] using he'

/-- Classical harmonicity implies the exact zero compact-test pairing
needed for local smoothing. -/
theorem EuclideanHarmonicModel.integral_mul_laplacian_eq_zero {n : ℕ} {S : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) {g : Euclidean n → ℝ}
    (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 (S/2)) :
    (∫ x, w.value x*(Δ g) x) = 0 := by
  obtain ⟨F,hF,_,_,hEq,_⟩ := w.compact_extension hS
  have hreplace : (∫ x, w.value x*(Δ g) x) = ∫ x, F x*(Δ g) x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport g
    · rw [hEq x (hs hx)]
    · rw [laplacian_eq_zero_of_notMem_tsupport g hx,mul_zero,mul_zero]
  rw [hreplace,integral_laplacian_commute hF hg hgs]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport g
  · have hin := hs hx
    have hn : F =ᶠ[𝓝 x] w.value := by
      filter_upwards [isOpen_ball.mem_nhds hin] with y hy
      exact hEq y hy
    have he := (laplacian_congr_nhds hn).self_of_nhds
    have hz := (w.harmonic x ((ball_subset_ball (by linarith : S/2 ≤ S)) hin)).2.self_of_nhds
    rw [he,hz]
    simp only [Pi.zero_apply,zero_mul]
  · have hg0 : g x = 0 := by
      by_contra hne
      exact hx (subset_tsupport g hne)
    simp only [hg0,mul_zero,Pi.zero_apply]

end RegularPointCoordinates

end

end OAI
