import OAI.Geometry.RCD.Sobolev.CompactReciprocalMultiplier

namespace OAI

/-! # Integrating a Li--Yau inequality on the actual support of a cutoff -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

theorem compact_ratio_weight_integrable
    (φ F G E : X → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hF : Continuous F) (hpos : ∀ x ∈ tsupport φ, 0 < F x)
    (hG : AEStronglyMeasurable G μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, |G x| ≤ B)
    (hE : Integrable E μ) : Integrable (fun x => φ x*(G x/F x)*E x) μ := by
  obtain ⟨C,hC,hCF⟩ := compact_reciprocal_multiplier_bound φ F hφ hs hF hpos
  have hcoef : AEStronglyMeasurable (fun x => (φ x/F x)*G x) μ :=
    (hφ.measurable.div hF.measurable).aestronglyMeasurable.mul hG
  have hb : ∀ᵐ x ∂μ, ‖(φ x/F x)*G x‖ ≤ C*B := by
    filter_upwards [hB] with x hx
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hCF x) hx (abs_nonneg _) hC
  apply (hE.bdd_mul hcoef hb).congr
  exact Eventually.of_forall fun x => by
    dsimp only
    ring

omit [BorelSpace X] in
theorem localized_liYau_integral
    (φ F G E d : X → ℝ) (α c : ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hG : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hF : ∀ x ∈ tsupport φ, 0 < F x)
    (hpoint : ∀ᵐ x ∂μ, E x ≤ α*F x*d x+c*(F x)^2)
    (hE : Integrable (fun x => φ x*(G x/F x)*E x) μ)
    (hd : Integrable (fun x => φ x*G x*d x) μ)
    (hM : Integrable (fun x => φ x*G x*F x) μ) :
    (∫ x, φ x*(G x/F x)*E x ∂μ) ≤
      α*(∫ x, φ x*G x*d x ∂μ)+c*(∫ x, φ x*G x*F x ∂μ) := by
  have hp : ∀ᵐ x ∂μ, φ x*(G x/F x)*E x ≤
      α*(φ x*G x*d x)+c*(φ x*G x*F x) := by
    filter_upwards [hG,hpoint] with x hx he
    by_cases hs : x ∈ tsupport φ
    · have hFx := hF x hs
      have hb := mul_le_mul_of_nonneg_left he
        (mul_nonneg (hφ x) (div_nonneg hx hFx.le))
      have hid : φ x*(G x/F x)*(α*F x*d x+c*(F x)^2) =
          α*(φ x*G x*d x)+c*(φ x*G x*F x) := by
        field_simp
      rwa [hid] at hb
    · rw [image_eq_zero_of_notMem_tsupport hs]
      simp only [zero_mul,mul_zero,add_zero,le_refl]
  have hi := integral_mono_ae hE ((hd.const_mul α).add (hM.const_mul c)) hp
  simp only [Pi.add_apply] at hi
  rwa [integral_add (hd.const_mul α) (hM.const_mul c),integral_const_mul,integral_const_mul] at hi

theorem localized_liYau_of_memLp (φ F G E d : X → ℝ) (α c : ℝ)
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hFc : Continuous F) (hGc : Continuous G)
    (hF : ∀ x ∈ tsupport φ, 0 < F x)
    (hFm : MemLp F 2 μ) (hGm : MemLp G 2 μ) (hdm : MemLp d 2 μ)
    (hG0 : ∀ᵐ x ∂μ, 0 ≤ G x) {B : ℝ} (hGB : ∀ᵐ x ∂μ, |G x| ≤ B)
    (hEi : Integrable E μ) (hpoint : ∀ᵐ x ∂μ, E x ≤ α*F x*d x+c*(F x)^2) :
    (∫ x, φ x*(G x/F x)*E x ∂μ) ≤
      α*(∫ x, φ x*G x*d x ∂μ)+c*(∫ x, φ x*G x*F x ∂μ) := by
  obtain ⟨M,hM⟩ := hφs.exists_bound_of_continuous hφ
  have hφB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M := Eventually.of_forall hM
  have hd : Integrable (fun x => φ x*G x*d x) μ := by
    simpa only [Pi.mul_apply,mul_assoc] using
      (hGm.integrable_mul hdm).bdd_mul hφ.measurable.aestronglyMeasurable hφB
  have hmass : Integrable (fun x => φ x*G x*F x) μ := by
    simpa only [Pi.mul_apply,mul_assoc] using (hGm.integrable_mul hFm).bdd_mul
      hφ.measurable.aestronglyMeasurable hφB
  exact localized_liYau_integral μ φ F G E d α c hφ0 hG0 hF hpoint
    (compact_ratio_weight_integrable μ φ F G E hφ hφs hFc hF
      hGc.measurable.aestronglyMeasurable hGB hEi) hd hmass

end RegularPointCoordinates

end

end OAI
