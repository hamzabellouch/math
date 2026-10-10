import OAI.Probability.SLE.Multipoint.MultipointGeometry
import OAI.Probability.SLE.KernelConsistency

namespace OAI

/-! The disk growth estimate controls half-plane maps with moving
normalizations on a fixed compact set. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace SLEExactGauge

def halfPlaneGrowthCost (z w : ℂ) : ℝ :=
  2*z.im*‖halfPlaneToDisk z w‖/(1-‖halfPlaneToDisk z w‖)^2

lemma halfPlaneGrowthCost_nonneg {z w : ℂ} (hz : z∈upperHalfPlane) :
    0≤halfPlaneGrowthCost z w := by
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.le) (norm_nonneg _)) (sq_nonneg _)

lemma univalent_halfPlane_growth (hgrowth : PublishedDiskUnivalentGrowth)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlane) (hi : InjOn f upperHalfPlane)
    {z w : ℂ} (hz : z∈upperHalfPlane) (hw : w∈upperHalfPlane) :
    ‖f w-f z‖ ≤ ‖deriv f z‖*halfPlaneGrowthCost z w := by
  have hdf : DifferentiableOn ℂ (f ∘ diskToHalfPlane z) (ball 0 1) :=
    hf.comp (diskToHalfPlane_differentiable z) (diskToHalfPlane_maps hz)
  have hinj : InjOn (f ∘ diskToHalfPlane z) (ball 0 1) :=
    hi.comp (diskToHalfPlane_injOn hz) (diskToHalfPlane_maps hz)
  have hdfz : HasDerivAt f (deriv f z) (diskToHalfPlane z 0) := by
    simpa only [diskToHalfPlane_zero] using
      (hf.differentiableAt (isOpen_upperHalfPlane.mem_nhds hz)).hasDerivAt
  have hder : deriv (f ∘ diskToHalfPlane z) 0=deriv f z*(z-star z) :=
    (hdfz.comp 0 (diskToHalfPlane_deriv_zero z)).deriv
  have h := hgrowth (f ∘ diskToHalfPlane z) hdf hinj (halfPlaneToDisk z w)
    (halfPlaneToDisk_maps hz hw)
  simp only [Function.comp_apply,diskToHalfPlane_zero,diskToHalfPlane_halfPlaneToDisk hz hw,
    hder,norm_mul,norm_sub_conj_of_im_pos hz] at h
  convert h using 1
  simp only [halfPlaneGrowthCost]
  ring

lemma continuousOn_halfPlaneGrowthCost :
    ContinuousOn (fun q : ℂ × ℂ => halfPlaneGrowthCost q.1 q.2)
      (upperHalfPlane ×ˢ upperHalfPlane) := by
  have hq : ContinuousOn (fun q : ℂ × ℂ => halfPlaneToDisk q.1 q.2)
      (upperHalfPlane ×ˢ upperHalfPlane) := by
    exact (continuous_snd.sub continuous_fst).continuousOn.div
      (continuous_snd.sub (Complex.continuous_conj.comp continuous_fst)).continuousOn
      (fun q hq => halfPlane_denominator_ne hq.1 hq.2)
  exact ((continuous_const.mul (Complex.continuous_im.comp continuous_fst)).continuousOn.mul
    hq.norm).div (continuousOn_const.sub hq.norm |>.pow 2) (fun q hq' => by
      apply pow_ne_zero
      exact sub_ne_zero.mpr (ne_of_gt (mem_ball_zero_iff.mp (halfPlaneToDisk_maps hq'.1 hq'.2))))

lemma univalent_compact_family_bound (hgrowth : PublishedDiskUnivalentGrowth)
    (f : ℕ → ℂ → ℂ) (z : ℕ → ℂ) (K L : Set ℂ) (M : ℝ)
    (hK : IsCompact K) (hL : IsCompact L) (hKH : K⊆upperHalfPlane) (hLH : L⊆upperHalfPlane)
    (hz : ∀ n, z n∈K) (hf : ∀ n, DifferentiableOn ℂ (f n) upperHalfPlane)
    (hi : ∀ n, InjOn (f n) upperHalfPlane)
    (hv : ∀ n, ‖f n (z n)‖≤M) (hd : ∀ n, ‖deriv (f n) (z n)‖≤M) :
    ∃ C : ℝ, ∀ n, ∀ w∈L, ‖f n w‖≤C := by
  have hc := continuousOn_halfPlaneGrowthCost.mono (Set.prod_mono hKH hLH)
  obtain ⟨R,hR⟩ := (hK.prod hL).bddAbove_image hc
  let A : ℝ := max M 0
  let B : ℝ := max R 0
  have hA : 0≤A := le_max_right _ _
  have hB : 0≤B := le_max_right _ _
  refine ⟨A*B+A,fun n w hw => ?_⟩
  have hcost : halfPlaneGrowthCost (z n) w≤B := by
    apply le_trans _ (le_max_left R 0)
    exact hR ⟨(z n,w),⟨hz n,hw⟩,rfl⟩
  calc
    ‖f n w‖ ≤ ‖f n w-f n (z n)‖+‖f n (z n)‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖deriv (f n) (z n)‖*halfPlaneGrowthCost (z n) w+A :=
      add_le_add (univalent_halfPlane_growth hgrowth (hf n) (hi n) (hKH (hz n)) (hLH hw))
        ((hv n).trans (le_max_left _ _))
    _ ≤ A*B+A := add_le_add
      (mul_le_mul ((hd n).trans (le_max_left _ _)) hcost
        (halfPlaneGrowthCost_nonneg (hKH (hz n))) hA) le_rfl

end SLEExactGauge

end

end OAI
