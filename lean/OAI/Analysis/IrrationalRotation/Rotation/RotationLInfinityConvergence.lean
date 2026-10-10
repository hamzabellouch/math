import OAI.Analysis.IrrationalRotation.Rotation.RotationLInfinity

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

theorem lInfinityRepresentation_tendsto_apply_of_ae
    (θ : ℝ) (a : ℕ → Lp ℂ ∞ circleMeasure) (b : Lp ℂ ∞ circleMeasure)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hab : ∀ᵐ x ∂circleMeasure, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (v : Hilbert) :
    Tendsto (fun n => lInfinityRepresentation θ (a n) v) atTop
      (𝓝 (lInfinityRepresentation θ b v)) := by
  let g (n : ℕ) : Circle → ℂ := LInfinityRepresentative.value (a n)
  let h : Circle → ℂ := LInfinityRepresentative.value b
  have hg (n : ℕ) : Measurable (g n) :=
    (LInfinityRepresentative.stronglyMeasurable_value (a n)).measurable
  have hh : Measurable h :=
    (LInfinityRepresentative.stronglyMeasurable_value b).measurable
  have hgb (n : ℕ) (x : Circle) : ‖g n x‖ ≤ C :=
    (LInfinityRepresentative.norm_value_le (a n) x).trans (ha n)
  have hhb (x : Circle) : ‖h x‖ ≤ ‖b‖ :=
    LInfinityRepresentative.norm_value_le b x
  have hga : ∀ᵐ x ∂circleMeasure, ∀ n : ℕ, g n x = a n x :=
    ae_all_iff.mpr fun n => LInfinityRepresentative.value_ae (a n)
  have hgh : ∀ᵐ x ∂circleMeasure,
      Tendsto (fun n => g n x) atTop (𝓝 (h x)) := by
    filter_upwards [hga, LInfinityRepresentative.value_ae b, hab] with x hax hbx hx
    change h x = b x at hbx
    simpa only [hax, hbx] using hx
  have hr (n : ℕ) : lInfinityRepresentation θ (a n) =
      measurableRepresentation θ (g n) C hC (hg n) (hgb n) :=
    lInfinityRepresentation_eq_measurable_of_ae θ (a n) (g n) C hC (hg n) (hgb n)
      (LInfinityRepresentative.value_ae (a n)).symm
  have hs : lInfinityRepresentation θ b =
      measurableRepresentation θ h ‖b‖ (norm_nonneg b) hh hhb :=
    lInfinityRepresentation_eq_measurable_of_ae θ b h ‖b‖ (norm_nonneg b) hh hhb
      (LInfinityRepresentative.value_ae b).symm
  simp_rw [hr, hs]
  exact measurableRepresentation_tendsto_apply θ g h C ‖b‖ hC (norm_nonneg b)
    hg hh hgb hhb hgh v

end Invariant233.Rotation

end

end OAI
