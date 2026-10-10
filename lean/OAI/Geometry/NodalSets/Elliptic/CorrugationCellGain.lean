import Mathlib.MeasureTheory.Function.LocallyIntegrable
import OAI.Geometry.NodalSets.Elliptic.CorrugationAnnulusFraction
import OAI.Geometry.NodalSets.Elliptic.CorrugationCubeMeasure
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldSpeed
import OAI.Geometry.NodalSets.Elliptic.CorrugationSpeed
import OAI.Geometry.NodalSets.Elliptic.IntegratedSpeedGain

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem corrugation_cell_integrated_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
      (D U : Set Coord), IsCompact D → Convex ℝ D → IsOpen U → D ⊆ U →
      ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ S U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ D, metricGradient g S y ≠ 0) →
      (∀ y ∈ D, ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ L : ℝ, 0 < L → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, closedBall y (corrugationScale L k/2) ⊆ D →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let W := localizedCorrugation corrugationFixedCutoff (corrugationPeriodicWell corrugationFixedAmplitude)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
      (1+γ)*(∫ x in closedBall y (corrugationScale L k/2), corrugationOldSlope g S x) ≤
        ∫ x in closedBall y (corrugationScale L k/2), corrugationOldSlope g (S+W) x := by
  obtain ⟨δ,l₀,B,hδ,hl₀,hB,hfrac⟩ := corrugation_annulus_fraction hc hM
  let q : ℝ := Real.sqrt (1+l₀^2)
  have hq : 1 < q := by
    dsimp [q]
    exact (Real.lt_sqrt (by norm_num)).mpr (by nlinarith [sq_pos_of_pos hl₀])
  let γ : ℝ := δ*(q-1)/2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨γ,hγ,?_⟩
  intro g S D U hD hconv hU hDU hg hS hp hn hcmp L hL
  obtain ⟨Cχ,hCχ,hχ,hχc,hχsupp,hχrange,hχcenter,hχder⟩ := corrugationFixedCutoff_spec
  obtain ⟨C,hC,hnew⟩ := corrugation_speed_freezing g S corrugationFixedCutoff hD hconv
    hU hDU hg hS hp hn hχ hχc (fun x ↦ (hχrange x).1) (fun x ↦ (hχrange x).2)
    corrugationFixedAmplitude_spec.1.le corrugationFixedAmplitude_spec.2.1 hL
  obtain ⟨C₀,hC₀,hold⟩ := corrugation_old_speed_freezing g S hD hconv hU hDU hg hS hp hn
  let E := fun k ↦ (C+C₀)*corrugationGradientRate L k
  have hE : Tendsto (fun k ↦ E k*(2+γ)) atTop (𝓝 0) := by
    simpa [E] using ((corrugationGradientRate_tendsto hL).const_mul (C+C₀)).mul_const (2+γ)
  filter_upwards [hnew,hE.eventually_lt_const hγ,
    (corrugation_frequency_scale_tendsto hL).eventually_ge_atTop B] with k hk hEk hBk
  intro y hy hQD e he0 he
  dsimp only
  let R := corrugationScale L k
  let J := corrugationFrequency k
  let s := corrugationOldSlope g S y
  let W := localizedCorrugation corrugationFixedCutoff (corrugationPeriodicWell corrugationFixedAmplitude)
    s J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
  let Q := closedBall y (R/2)
  have hR : 0 < R := corrugationScale_positive hL k
  have hJ : 0 < J := corrugationFrequency_positive k
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hρ : 0 ≤ corrugationGradientRate L k := (corrugationGradientRate_positive hL k).le
  have hRρ : R ≤ corrugationGradientRate L k := by
    dsimp [R,corrugationGradientRate]
    have hh : 0 ≤ 1/(corrugationFrequency k*corrugationScale L k) := by positivity
    linarith
  have hdist : ∀ x ∈ Q, ‖x-y‖ ≤ R := by
    intro x hx
    have hh : ‖x-y‖ ≤ R/2 := by simpa only [Q,mem_closedBall,dist_eq_norm] using hx
    linarith
  obtain ⟨A,hA,hAsmall,hvol,hgood⟩ := hfrac (g y) (hcmp y hy).2 (hcmp y hy).1 e he y J R hJ hR hBk
  have hAQ : A ⊆ Q := hAsmall.trans (closedBall_subset_closedBall (by linarith))
  have hfin : volume Q ≠ ⊤ := (isCompact_closedBall y (R/2)).measure_ne_top
  have hvolreal : δ*volume.real Q ≤ volume.real A := by
    rw [coordinate_cube_volume_real y hR.le]
    exact (ENNReal.toReal_ofReal (by positivity : 0 ≤ δ*R^4)).symm.trans_le
      (ENNReal.toReal_mono hA.measure_ne_top hvol)
  have hW : ContDiff ℝ ∞ W := localizedCorrugation_smooth _ _ hχ
    (corrugationPeriodicWell_smooth _) _ _ _ _ _ _
  have hfs : IntegrableOn (corrugationOldSlope g (S+W)) Q :=
    ((corrugationOldSlope_continuousOn g (S+W) hU hg (hS.add hW.contDiffOn) hp).mono
      (hQD.trans hDU)).integrableOn_compact (isCompact_closedBall y (R/2))
  have hos : IntegrableOn (corrugationOldSlope g S) Q :=
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono
      (hQD.trans hDU)).integrableOn_compact (isCompact_closedBall y (R/2))
  have happrox : ∀ x ∈ Q,
      s*Real.sqrt (1+(corrugationFixedCutoff (R⁻¹ • (x-y))*
        corrugationSlope corrugationFixedAmplitude (1/4)
          (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
            (frozenFrameCovector e 3) (x-y))))^2)-s*E k ≤ corrugationOldSlope g (S+W) x := by
    intro x hx
    have hh := (abs_le.mp (hk y hy x (hQD hx) (hdist x hx) e he0 he)).1
    have herr : s*C*corrugationGradientRate L k ≤ s*E k := by
      dsimp [E]
      nlinarith [mul_nonneg (mul_nonneg hs.le hC₀.le) hρ]
    change -(s*C*corrugationGradientRate L k) ≤ corrugationOldSlope g (S+W) x-_ at hh
    linarith
  apply integrated_speed_factor measurableSet_closedBall hA.measurableSet hAQ hfin
    (corrugationOldSlope g (S+W)) (corrugationOldSlope g S) hfs hos hs hδ hq hvolreal hEk.le
  · intro x hx
    have hroot : 1 ≤ Real.sqrt (1+(corrugationFixedCutoff (R⁻¹ • (x-y))*
        corrugationSlope corrugationFixedAmplitude (1/4)
          (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
            (frozenFrameCovector e 3) (x-y))))^2) := by
      apply Real.one_le_sqrt.mpr
      linarith [sq_nonneg (corrugationFixedCutoff (R⁻¹ • (x-y))*
        corrugationSlope corrugationFixedAmplitude (1/4)
          (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
            (frozenFrameCovector e 3) (x-y))))]
    have hh := mul_le_mul_of_nonneg_left hroot hs.le
    linarith [happrox x hx]
  · intro x hx
    have hh := happrox x (hAQ hx)
    rw [(hgood x hx).1,one_mul] at hh
    have hroot : q ≤ Real.sqrt (1+(corrugationSlope corrugationFixedAmplitude (1/4)
        (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
          (frozenFrameCovector e 3) (x-y))))^2) := by
      apply Real.sqrt_le_sqrt
      have h := (hgood x hx).2
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hroot hs.le
    linarith
  · intro x hx
    have hh := (abs_le.mp (hold x (hQD hx) y hy)).2
    have herr : s*C₀*‖x-y‖ ≤ s*E k := by
      calc
        _ ≤ s*C₀*corrugationGradientRate L k :=
          mul_le_mul_of_nonneg_left ((hdist x hx).trans hRρ) (mul_nonneg hs.le hC₀.le)
        _ ≤ s*E k := by dsimp [E]; nlinarith [mul_nonneg (mul_nonneg hs.le hC.le) hρ]
    linarith

end
end Yau.Geometry

end OAI
