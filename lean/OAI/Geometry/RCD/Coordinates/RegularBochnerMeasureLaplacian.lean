import OAI.Geometry.RCD.Sobolev.BochnerMeasurePolarization
import OAI.Geometry.RCD.Coordinates.RegularBochnerLocalSource
import OAI.Geometry.RCD.Metric.LocalMeasureProduct

namespace OAI

/-! # The local measure Laplacian of a regular Gram entry -/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

/-- Local Sobolev representatives of the Laplacians turn the common
Bochner identity into the full distributional equation for each Gram
entry. Global derivatives of the chosen extensions are not required. -/
theorem regularBochner_measure_laplacian (K : ℝ)
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hsym : ∀ a b, H a b=H b a)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (M : PositiveBilinearMeasure X (Euclidean m))
    (hM : ∀ (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ),
      HasCompactSupport (q : X → ℝ) → tsupport q ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q →
      (∫ x, q x ∂M.measure a)=regularBochnerForm μ hQ K U D H q ψ L hU a a)
    (a b : Euclidean m) (da db : SobolevSpace μ hQ)
    (hH : SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b))
    (hda : IsWeakLaplacian μ hQ (U a) (D a))
    (hdb : IsWeakLaplacian μ hQ (U b) (D b))
    (hsa : D a =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ da)
    (hsb : D b =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ db)
    (A B : ℝ≥0)
    (ha : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ da x|≤A)
    (hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ db x|≤B) :
    IsMeasureLaplacianOn μ hQ Ω (H a b)
      ((2 : ℝ) • M.bilinear a b + μ.withDensityᵥ (fun x =>
        2*K*localGamma μ hQ (U a) (U b) x+
        localGamma μ hQ (U a) db x+localGamma μ hQ (U b) da x)) := by
  intro ψ v hv hvc hvs hψ
  let q : X →ᵇ ℝ := ofCompactSupport v hv hvc
  have hq : HasCompactSupport (q : X → ℝ) := hvc
  have hqp : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q := hψ
  have hm := M.polarized_test q (regularBochnerForm μ hQ K U D H q ψ L hU)
    (regularBochnerForm_symmetric μ hQ K U D H q ψ L hU hsym)
    (fun c => hM c ψ q hq hvs hqp) a b
  have hlocal := regularBochnerForm_local_sources μ hQ K U D H q ψ L hU hΩ hvs hqp
    a b da db hda hdb hsa hsb A B ha hb
  have hI : inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ (H a b)) =
      ∫ x, q x*localGamma μ hQ (U a) (U b) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH,hψ] with x hh hp
    simp only [Real.inner_apply,hh,hp]
    change v x*localGamma μ hQ (U a) (U b) x = v x*localGamma μ hQ (U a) (U b) x
    rfl
  have hig := (localGamma_memL1 μ hQ (U a) (U b)).const_mul (2*K)
  have hid : Integrable (fun x => 2*K*localGamma μ hQ (U a) (U b) x+
      localGamma μ hQ (U a) db x+localGamma μ hQ (U b) da x) μ :=
    (hig.add (localGamma_memL1 μ hQ (U a) db)).add (localGamma_memL1 μ hQ (U b) da)
  have hi₁ := (localGamma_memL1 μ hQ (U a) (U b)).bdd_mul q.continuous.aestronglyMeasurable
    (Eventually.of_forall q.norm_coe_le_norm)
  have hi₂ := (localGamma_memL1 μ hQ (U a) db).bdd_mul q.continuous.aestronglyMeasurable
    (Eventually.of_forall q.norm_coe_le_norm)
  have hi₃ := (localGamma_memL1 μ hQ (U b) da).bdd_mul q.continuous.aestronglyMeasurable
    (Eventually.of_forall q.norm_coe_le_norm)
  have hi₁' : Integrable (fun x => q x*(2*K*localGamma μ hQ (U a) (U b) x)) μ := by
    convert hi₁.const_mul (2*K) using 1
    ext x
    ring
  have hiss : Integrable (fun x => q x*(2*K*localGamma μ hQ (U a) (U b) x)+
      q x*localGamma μ hQ (U a) db x) μ := hi₁'.add hi₂
  have hsource : (∫ᵛ x, v x ∂<•((2 : ℝ) • M.bilinear a b + μ.withDensityᵥ (fun x =>
      2*K*localGamma μ hQ (U a) (U b) x+
      localGamma μ hQ (U a) db x+localGamma μ hQ (U b) da x))) =
      2*signedTestIntegral q (M.bilinear a b)+
      2*K*(∫ x, q x*localGamma μ hQ (U a) (U b) x ∂μ)+
      (∫ x, q x*localGamma μ hQ (U a) db x ∂μ)+
      (∫ x, q x*localGamma μ hQ (U b) da x ∂μ) := by
    change (∫ᵛ x, q x ∂<•((2 : ℝ) • M.bilinear a b + μ.withDensityᵥ _)) = _
    rw [VectorMeasure.integral_add_vectorMeasure (PositiveBilinearMeasure.integrable_weight q _)
      (PositiveBilinearMeasure.integrable_weight q _),VectorMeasure.integral_smul_vectorMeasure,
      integral_signedDensity μ hid]
    have heq : (fun x => q x*(2*K*localGamma μ hQ (U a) (U b) x+
        localGamma μ hQ (U a) db x+localGamma μ hQ (U b) da x)) =
        (fun x => q x*(2*K*localGamma μ hQ (U a) (U b) x)+
        q x*localGamma μ hQ (U a) db x+q x*localGamma μ hQ (U b) da x) := by
      funext x
      ring
    rw [heq,integral_add hiss hi₃,integral_add hi₁' hi₂]
    have hc : (∫ x, q x*(2*K*localGamma μ hQ (U a) (U b) x) ∂μ) =
        2*K*(∫ x, q x*localGamma μ hQ (U a) (U b) x ∂μ) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hc]
    change 2*(∫ᵛ x, q x ∂<•M.bilinear a b)+
      (2*K*(∫ x, q x*localGamma μ hQ (U a) (U b) x ∂μ)+
        (∫ x, q x*localGamma μ hQ (U a) db x ∂μ)+
        (∫ x, q x*localGamma μ hQ (U b) da x ∂μ)) = _
    change _ = 2*(∫ᵛ x, q x ∂<•M.bilinear a b)+
      2*K*(∫ x, q x*localGamma μ hQ (U a) (U b) x ∂μ)+
        (∫ x, q x*localGamma μ hQ (U a) db x ∂μ)+
        (∫ x, q x*localGamma μ hQ (U b) da x ∂μ)
    ring
  rw [← hm,bochnerTestForm_apply,hI] at hlocal
  rw [hsource]
  linarith only [hlocal]

end RegularPointCoordinates

end

end OAI
