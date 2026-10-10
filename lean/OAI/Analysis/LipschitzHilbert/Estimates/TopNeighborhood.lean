import OAI.Analysis.LipschitzHilbert.Fourier.DemodulatedVertical
import OAI.Analysis.LipschitzHilbert.Estimates.NeighborhoodExceptional

namespace OAI

/-! Uniform vertical neighborhoods for an entire family of sums, with
one measurable exceptional set and an explicit area moment bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem top_neighborhood_exceptional {α κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (U : Set ℝ) (hU : MeasurableSet U) (c r threshold : ℝ)
    (hr : 0 < r) (hthreshold : 0 ≤ threshold) (n : ℕ) (C : ℝ≥0∞)
    (hline : ∀ y, (∫⁻ x in U, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤ C)
    (hf : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k,
      DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))))
    (hbV : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x)) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ U ×ˢ Icc (c-r) (c+r) ∧
      (ENNReal.ofReal threshold)^(2*n)*(volume.prod volume) bad ≤
        (4:ℝ≥0∞)^n*C*ENNReal.ofReal (2*r) ∧
      ∀ i x z v, x ∈ U → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
        ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ threshold := by
  let μ := volume.restrict (Icc (c-2*r) (c+2*r))
  let E : ℝ → ℝ := fun x => verticalSquareEnergy μ
    (fun y => V (y,x)) (fun y => 4*r*D (y,x))
  have hE : Measurable E := verticalSquareEnergy_measurable μ V
    (fun z => 4*r*D z) hV.measurable (hD.measurable.const_mul _)
  let B := {x | threshold^2 ≤ E x}
  have hB : MeasurableSet B := measurableSet_le measurable_const hE
  let bad := (U ∩ B) ×ˢ Icc (c-r) (c+r)
  have hmoment : (∫⁻ x in U, ENNReal.ofReal (E x)^n) ≤ (4:ℝ≥0∞)^n*C :=
    interval_vertical_moment (volume.restrict U) V (fun z => 4*r*D z) hV
      (hD.const_mul _) (by linarith : c-2*r < c+2*r) n C hline
  have hmark := energy_superlevel_moment (volume.restrict U) E hE threshold hthreshold n
    ((4:ℝ≥0∞)^n*C) hmoment
  change (ENNReal.ofReal threshold)^(2*n)*(volume.restrict U) B ≤ _ at hmark
  rw [Measure.restrict_apply hB, inter_comm B U] at hmark
  refine ⟨bad, (hU.inter hB).prod measurableSet_Icc, ?_, ?_, ?_⟩
  · exact prod_mono inter_subset_left Subset.rfl
  · change (ENNReal.ofReal threshold)^(2*n) *
      (volume.prod volume) ((U ∩ B) ×ˢ Icc (c-r) (c+r)) ≤ _
    rw [Measure.prod_prod, Real.volume_Icc, show c+r-(c-r)=2*r by ring, ← mul_assoc]
    exact mul_le_mul' hmark le_rfl
  · intro i x z v hx hz hv hout
    have hzi : z ∈ Icc (c-r) (c+r) := by
      rcases abs_le.mp hz with ⟨h1,h2⟩
      constructor <;> linarith
    have houtE : ¬ threshold^2 ≤ E x := fun he => hout ⟨⟨hx,he⟩,hzi⟩
    have hzv : z+v ∈ Icc (c-2*r) (c+2*r) := by
      rcases abs_le.mp hz with ⟨h1,h2⟩
      rcases abs_le.mp hv with ⟨h3,h4⟩
      constructor <;> linarith
    have hp := covariant_interval_energy frequency (fun k => f i k x)
      (by linarith : c-2*r < c+2*r) (fun y hy => hf i x y hy) (hmem i x)
      (fun y => V (y,x)) (fun y => D (y,x))
      (hV.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hD.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun y hy => hbV i x y hy) (fun y hy => hbD i x y hy) hzv
    have hs : ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖^2 ≤ E x := by
      convert hp using 1
      dsimp only [E, μ]
      congr 1
      funext y
      ring
    have he := lt_of_not_ge houtE
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)]

end LipschitzHilbert

end

end OAI
