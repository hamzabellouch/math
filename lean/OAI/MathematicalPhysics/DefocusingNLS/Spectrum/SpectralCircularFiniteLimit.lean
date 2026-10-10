import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularFieldDifference
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBackwardStability

namespace OAI

/-! A remote limit of actual circular solutions propagates back to any
fixed point of the exterior annulus. -/

open Set Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularSolutions_backward_uniform_limit
    (νp νm : ℕ → ℂ) (μp μm η : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hn : Tendsto νm atTop (𝓝 μm))
    (m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, 1 ≤ m n) (q : ℕ → ℝ → ℂ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (L R : ℝ) (Z : ℕ → ℝ → E₄) (Y : ℝ → E₄)
    (hc : ∀ᶠ n in atTop, ContinuousOn (Z n) (Icc L R)) (hy : ContinuousOn Y (Icc L R))
    (hd : ∀ᶠ n in atTop, ∀ t ∈ Icc L R, HasDerivAt (Z n)
      (circularLeadingField t (Z n t)+circularBoundedField (νp n) (νm n) η (m n) (q n t) (Z n t)) t)
    (hdy : ∀ t ∈ Icc L R, HasDerivAt Y
      (circularLeadingField t (Y t)+circularBoundedField μp μm η 1 0 (Y t)) t)
    (hq : ∀ᶠ n in atTop, ∀ t ∈ Icc L R,
      ‖spectralDiagonalCoefficient (m n) (q n t)‖+‖spectralCrossCoefficient (m n) (q n t)‖ ≤ ε n)
    (hend : Tendsto (fun n => Z n R) atTop (𝓝 (Y R))) :
    TendstoUniformlyOn Z Y atTop (Icc L R) := by
  obtain ⟨M₀,hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hYM (t : ℝ) (ht : t ∈ Icc L R) : ‖Y t‖ ≤ M :=
    (hM₀ t ht).trans (le_max_left _ _)
  let δ := fun n => circularExponentDifference (νp n) (νm n) μp μm+ε n
  have hδ (n : ℕ) : 0 ≤ δ n :=
    add_nonneg (circularExponentDifference_nonneg _ _ _ _) (hε n)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [zero_add] using (circularExponentDifference_tendsto νp νm μp μm hp hn).add hεlim
  let K := Real.exp (2*R)/2+circularFieldBound μp μm η 1 0+1
  have hK : 0 < K := by
    have hf := circularFieldBound_nonneg μp μm η 1 0
    dsimp [K]
    positivity
  apply spectral_backward_uniform_limit L R K hK Z _ Y _ (fun n => δ n*M)
    (by simpa only [zero_mul] using hδlim.mul_const M) hend hc hy hd hdy
  filter_upwards [hq,hδlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),hm] with n hqn hnδ hmn
  refine ⟨mul_nonneg (hδ n) hM,?_⟩
  intro t ht
  have hb := circularFullField_free_difference_bound (νp n) (νm n) μp μm η (m n) hmn
    (q n t) (ε n) (hqn t ht) t R ht.2 (Z n t) (Y t)
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_right (by dsimp [K,δ]; linarith) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (hYM t ht) (hδ n)))

end DefocusingNLS

end OAI
