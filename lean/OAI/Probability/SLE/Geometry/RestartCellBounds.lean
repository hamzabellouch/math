import OAI.Probability.SLE.Geometry.ActualMarkedCell
import OAI.Probability.SLE.Mass.StoppedInverseMass

namespace OAI

/-! Deterministic cell bounds once the actual increment is expressed through
the inverse map and a normalized fresh mass. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Multipoint
local instance restartCellLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

lemma weightedImageMass_subtype_apply
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (μ : Measure upperHalfPlane)
    (A : Set ℂ) (hA : MeasurableSet A) :
    weightedImageMass J w μ (Subtype.val ⁻¹' A) =
      weightedImageMass (fun z => (J z:ℂ)) w μ A := by
  rw [weightedImageMass_apply J hJ w μ _ (hA.preimage measurable_subtype_coe)]
  change _ = weightedImageMass (Subtype.val ∘ J) w μ A
  rw [weightedImageMass_apply _ (measurable_subtype_coe.comp hJ) w μ A hA]
  rfl

lemma IsCapacityTwoWitness.restarted_cell_mass_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (κ : ℝ) (hκ : 0 < κ) (t s : ℝ≥0) (hts : t ≤ s)
    (N : ℝ≥0 → Measure upperHalfPlane) (hmono : Monotone N)
    [IsFiniteMeasureOnCompacts (N t)]
    (hzero : ∀ A : Set ℂ, A ⊆ survivingDomain γ t → N t (Subtype.val ⁻¹' A)=0)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (a : ℝ≥0) (ha : 0 < a)
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ]
    (he : N s-N t = weightedImageMass
      (fun w : upperHalfPlane => (⟨F t ((w:ℂ)+(U t:ℂ)),
        ((hw.2.2.2.2.2.2.1 t (by
          simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
            using w.property)).1.1)⟩ : upperHalfPlane))
      (fun w => ENNReal.ofReal (‖deriv (F t) ((w:ℂ)+(U t:ℂ))‖^dimension κ))
      (dilationMass κ a ha μ))
    (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hpolar : G t z=(U t:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (r : ℝ) (hr : 0 < r) (hR : fullRadius G t z=(2048*Real.pi)*r) :
    let L := ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
      (Target.diskSourceHalfPlane θ) μ)
    ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*L ≤
        N s (Subtype.val ⁻¹' closedBall z ((4096*Real.pi)*r)) ∧
      ∀ A : Set ℂ, MeasurableSet A → A ⊆ closedBall z (2*r) →
        A ⊆ survivingDomain γ t →
        N s (Subtype.val ⁻¹' A) ≤ ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*L := by
  let J : upperHalfPlane → upperHalfPlane := fun w =>
    ⟨F t ((w:ℂ)+(U t:ℂ)),((hw.2.2.2.2.2.2.1 t (by
      simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
        using w.property)).1.1)⟩
  have hJ : Measurable J := by
    apply Measurable.subtype_mk
    apply Continuous.measurable
    apply (hw.2.2.2.2.1 t).continuousOn.comp_continuous
      (continuous_subtype_val.add continuous_const)
    intro w
    change 0 < ((w:ℂ)+(U t:ℂ)).im
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
      using w.property
  have heval (A : Set ℂ) (hA : MeasurableSet A) :
      (N s-N t) (Subtype.val ⁻¹' A) =
        weightedImageMass (fun w : upperHalfPlane => F t ((w:ℂ)+(U t:ℂ)))
          (fun w => ENNReal.ofReal (‖deriv (F t) ((w:ℂ)+(U t:ℂ))‖^dimension κ))
          (dilationMass κ a ha μ) A := by
    rw [he]
    exact weightedImageMass_subtype_apply J hJ _ _ A hA
  have hb := hw.cell_mass_comparison hgrowth κ hκ θ hθ t z hz r hr hR a ha hpolar μ
  refine ⟨?_,?_⟩
  · have h := heval (closedBall z ((4096*Real.pi)*r)) isClosed_closedBall.measurableSet
    exact (hb.1.trans_eq h.symm).trans (Measure.sub_le _)
  · intro A hA hAc hAs
    have h := hb.2 A hAc
    rw [← heval A hA] at h
    have hzA := hzero A hAs
    rw [measure_sub_apply_of_zero (N t) (N s) (hmono hts) (Subtype.val ⁻¹' A) hzA] at h
    exact h

end SLEExactGauge

end

end OAI
