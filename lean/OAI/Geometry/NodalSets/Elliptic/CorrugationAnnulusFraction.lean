import OAI.Geometry.NodalSets.Charts.CorrugationFrameVolume
import OAI.Geometry.NodalSets.Elliptic.CorrugationAnnulusPacking
import OAI.Geometry.NodalSets.Elliptic.CorrugationFixedCutoff
import OAI.Geometry.NodalSets.Elliptic.CorrugationScaledJetsLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory Metric
open scoped ENNReal Topology
noncomputable section

theorem corrugation_annulus_fraction {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ δ l₀ B : ℝ, 0 < δ ∧ 0 < l₀ ∧ 0 < B ∧
      ∀ (g : Coord →L[ℝ] Coord →L[ℝ] ℝ),
      (∀ v : Coord, c*‖v‖^2 ≤ g v v) → ‖g‖ ≤ M →
      ∀ e : Coord ≃L[ℝ] Coord,
      (∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ (y : Coord) (J R : ℝ), 0 < J → 0 < R → B ≤ J*R →
      ∃ A : Set Coord, IsCompact A ∧ A ⊆ closedBall y (R/4) ∧
        ENNReal.ofReal (δ*R^4) ≤ volume A ∧
        ∀ x ∈ A, corrugationFixedCutoff (R⁻¹ • (x-y)) = 1 ∧
          l₀ ≤ corrugationSlope corrugationFixedAmplitude (1/4)
            (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
              (frozenFrameCovector e 3) (x-y))) := by
  let C : ℝ := 16*(1+c⁻¹)
  let K : ℝ := M*(1+c⁻¹)
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨l₀,hl₀,hwell⟩ := corrugation_rectangle_fixed_slope
  refine ⟨1/(1024*C^4*K^4),l₀,2*C,by positivity,hl₀,by positivity,?_⟩
  intro g hg hupper e he y J R hJ hR hlarge
  let r : ℝ := R/C
  have hr : 0 < r := div_pos hR hC
  have hlarge' : 2 ≤ J*r := by
    dsimp [r]
    rw [← mul_div_assoc,le_div_iff₀ hC]
    exact hlarge
  let n : ℕ := ⌊J*r⌋₊
  let P := corrugationAnnulusPacking r J n
  let A := (fun v ↦ y+e v) '' P
  have hP : IsCompact P := corrugationAnnulusPacking_compact r J n
  have hsub : ∀ x ∈ A, ∃ v ∈ P, x=y+e v ∧ ‖v‖ ≤ r := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨v,hv,rfl,?_⟩
    obtain ⟨p,_,hvp⟩ := Set.mem_iUnion₂.mp hv
    exact corrugationAnnulusBox_norm hr.le hJ (Nat.floor_le (mul_pos hJ hr).le) p.1 p.2 hvp
  have hdist : ∀ x ∈ A, ‖x-y‖ ≤ R/4 := by
    intro x hx
    obtain ⟨v,hv,rfl,hvn⟩ := hsub x hx
    simp only [add_sub_cancel_left]
    calc
      ‖e v‖ ≤ (4*(1+c⁻¹))*‖v‖ := frozenFrame_operator_bound g hc hg e he v
      _ ≤ (4*(1+c⁻¹))*r := mul_le_mul_of_nonneg_left hvn (by positivity)
      _ = R/4 := by dsimp [r,C]; field_simp; ring
  refine ⟨A,hP.image (continuous_const.add e.continuous),?_,?_,?_⟩
  · intro x hx
    simpa only [mem_closedBall,dist_eq_norm] using hdist x hx
  · have hv := frozenFrame_volume_lower g hc hM hg hupper e he y P
      (corrugationAnnulusPacking_volume_lower hr hJ hlarge')
    convert hv using 1
    dsimp [r,K]
    congr 1
    field_simp
  · intro x hx
    constructor
    · obtain ⟨_,_,_,_,_,_,hcenter,_⟩ := corrugationFixedCutoff_spec
      apply (hcenter (R⁻¹ • (x-y)) ?_).eq_of_nhds
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      calc
        _ ≤ R⁻¹*(R/4) := mul_le_mul_of_nonneg_left (hdist x hx) (inv_nonneg.mpr hR.le)
        _ = 1/4 := by field_simp
    · obtain ⟨v,hv,rfl,hvn⟩ := hsub x hx
      obtain ⟨p,_,hvp⟩ := Set.mem_iUnion₂.mp hv
      have hh := corrugationAnnulusBox_fast hJ p.1 p.2 hvp
      have heq : corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3)
          (y+e v-y) = (J*v 2,J*v 3) := by
        simp [corrugationFastMap,frozenFrameCovector,ContinuousLinearMap.prod_apply]
      rw [heq]
      exact hwell _ (p.1:ℕ) (p.2:ℕ) hh.1 hh.2

end
end Yau.Geometry

end OAI
