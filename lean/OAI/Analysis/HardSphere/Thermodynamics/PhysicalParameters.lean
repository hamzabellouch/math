import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalScaleData

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

theorem source_physical_scale {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop,∀α : ℝ,0 < α → α ≤ A →
      ∀w : Time,t*(w:ℝ)=D⁻¹ →
      PhysicalScaleBounds (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) t (α/D) (D^(1/12:ℝ))
        (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) D⁻¹ (prefixTime midpointTime w) := by
  filter_upwards [source_trial_geometry hA hb ht] with D hD
  intro α hα hαA w hw
  obtain ⟨h1,hn,hr1,hR,hmesh,hceil,hw0,hw1,hwin,hlarge,hdrift,hdrift',hcut,hrelax,hsep⟩ := hD α hα hαA
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one h1
  have hnp : 0 < (⌈t/(α/D)^2⌉₊:ℝ) := by exact_mod_cast hn
  have he : (2*t)/((⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊:ℕ):ℝ)=t/(⌈t/(α/D)^2⌉₊:ℝ) := by
    push_cast
    rw [← two_mul, mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)]
  refine ⟨by omega,ht,by positivity,hr1,by positivity,?_,by positivity,?_,hR,hsep.le,?_,?_,?_,?_,?_⟩
  · have := meanCost_nonneg
    positivity
  · change (1/2:ℝ)*(w:ℝ)=D⁻¹/(2*t)
    apply (eq_div_iff (by positivity : (2*t)≠0)).mpr
    nlinarith [hw]
  · rw [he]; exact hmesh
  · push_cast; nlinarith [hceil]
  · rw [he]; exact hwin
  · push_cast; nlinarith [hlarge]
  · apply (div_le_iff₀ (by push_cast; positivity : (0:ℝ) < ((⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊:ℕ):ℝ))).mpr
    have H := (div_le_iff₀ hnp).mp hdrift
    push_cast
    nlinarith [show (0:ℝ) ≤ α/D*(⌈t/(α/D)^2⌉₊:ℝ) by positivity]

end HardSphere.Groups
end
end

end OAI
