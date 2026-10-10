import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FrameMetric

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumLowerBound
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance lowerDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance lowerDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance lowerBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance lowerBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

omit [Nonempty M] in
lemma eventual_lower_bound_of_center_gain {a:M} {q:TangentSpace 𝓘(ℝ,Model n) a}
    {A C:ℝ} (hA:0 ≤ A) (hC:C ≤ 0) {H:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
      C*(inner ℝ q (show TangentSpace 𝓘(ℝ,Model n) a from d))^2-ε*‖d‖^2 ≤ H k d d) :
    ∃CH:ℝ,0 ≤ CH ∧ ∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ H k d d := by
  let f:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (show Model n from q)
  have hneg : 0 ≤ -C := neg_nonneg.mpr hC
  refine ⟨1+(-C)*‖f‖^2,by positivity,?_⟩
  filter_upwards [hH 1 (by norm_num)] with k hk
  intro d
  have hf:|f d| ≤ ‖f‖*‖d‖:=f.le_opNorm d
  have hs:(f d)^2 ≤ ‖f‖^2*‖d‖^2:=by
    have hp:=sq_le_sq₀ (abs_nonneg (f d)) (mul_nonneg (norm_nonneg f) (norm_nonneg d)) |>.mpr hf
    simpa only [sq_abs,mul_pow] using hp
  have hm:=mul_le_mul_of_nonpos_left hs hC
  have hpos:0 ≤ A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2:=mul_nonneg hA (sq_nonneg _)
  have hh:=hk d
  have he:f d=inner ℝ q (show TangentSpace 𝓘(ℝ,Model n) a from d):=frameMetric_center a q d
  rw [he] at hm
  nlinarith only [hm,hh,hpos]

end MaximumLowerBound
end WeakMTWTransport

end
end

end OAI
