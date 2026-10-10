import OAI.Geometry.RCD.Sobolev.BochnerSourceSquare
import OAI.Geometry.RCD.Sobolev.ReciprocalWeightedTest

namespace OAI

/-! # Cancellation of the logarithmic source square

Only bounded products occur. The original Sobolev source is handled by
the proved mixed L² identity against the reciprocal-weighted test.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem fisher_source_cancellation (u d w ℓ S H : SobolevSpace μ hQ)
    (hd : IsWeakLaplacian μ hQ u (SobolevSpace.toLp μ hQ d))
    {ε : ℝ} (hε : 0<ε) (A C B L M : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x∈Icc 0 (A:ℝ))
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hH : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ H x|≤B)
    (hLu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x≤L)
    (hLℓ : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ ℓ x≤M)
    (hℓ : SobolevSpace.toLp μ hQ ℓ =ᵐ[μ]
      fun x => Real.log (ε+SobolevSpace.toLp μ hQ u x)-Real.log ε)
    (hHr : SobolevSpace.toLp μ hQ H =ᵐ[μ] fun x => localGamma μ hQ u u x /
      (ε+SobolevSpace.toLp μ hQ u x)^2)
    (hSr : SobolevSpace.toLp μ hQ S =ᵐ[μ] fun x =>
      SobolevSpace.toLp μ hQ d x/(ε+SobolevSpace.toLp μ hQ u x)-SobolevSpace.toLp μ hQ H x) :
    ∃ (R : SobolevSpace μ hQ) (N : ℝ≥0),
      (SobolevSpace.toLp μ hQ R =ᵐ[μ] fun x =>
        (ε+SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ w x) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ R x|≤N) ∧
      (∫ x, SobolevSpace.toLp μ hQ R x*(SobolevSpace.toLp μ hQ S x)^2 ∂μ)+
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ S) ℓ R =
      -(∫ x, SobolevSpace.toLp μ hQ w x*localGamma μ hQ u d x /
        (ε+SobolevSpace.toLp μ hQ u x) ∂μ)-
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ H) u w := by
  have huA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A :=
    hu.mono fun x hx => (abs_of_nonneg hx.1).trans_le hx.2
  let P := SobolevSpace.product μ hQ u w A C
  let R := ε • w+P
  let N : ℝ≥0 := (⟨ε,hε.le⟩+A)*C
  have hRr : SobolevSpace.toLp μ hQ R =ᵐ[μ] fun x =>
      (ε+SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ w x := by
    filter_upwards [SobolevSpace.product_coe μ hQ u w A C huA hw,
      Lp.coeFn_add (ε • SobolevSpace.toLp μ hQ w) (SobolevSpace.toLp μ hQ P),
      Lp.coeFn_smul ε (SobolevSpace.toLp μ hQ w)] with x hp ha hs
    change SobolevSpace.toLp μ hQ P x = _ at hp
    change (ε • SobolevSpace.toLp μ hQ w+SobolevSpace.toLp μ hQ P) x = _
    simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hp]
    ring
  have hRb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ R x|≤N := by
    filter_upwards [hRr,hu,hw] with x hx hy hz
    rw [hx,abs_mul,abs_of_pos (add_pos_of_pos_of_nonneg hε hy.1)]
    change (ε+SobolevSpace.toLp μ hQ u x)*|SobolevSpace.toLp μ hQ w x|≤
      (ε+(A:ℝ))*(C:ℝ)
    exact mul_le_mul (add_le_add le_rfl hy.2) hz (abs_nonneg _) (add_nonneg hε.le A.coe_nonneg)
  have hΓR : localGamma μ hQ ℓ R =ᵐ[μ] fun x => localGamma μ hQ u w x+
      SobolevSpace.toLp μ hQ w x*(ε+SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ H x := by
    filter_upwards [shifted_logarithm_gamma μ hQ u ℓ hε A hu hℓ R,
      localGamma_add_right μ hQ u (ε • w) P,localGamma_smul_right μ hQ ε u w,
      localGamma_product_right μ hQ u u w A C huA hw,hHr,hu] with x hc ha hs hp hh hux
    change localGamma μ hQ u R x = _ at ha
    change localGamma μ hQ u P x = _ at hp
    rw [hc,ha,hs,hp,hh]
    have hz : ε+SobolevSpace.toLp μ hQ u x≠0 :=
      (add_pos_of_pos_of_nonneg hε hux.1).ne'
    field_simp [hz]
    ring
  obtain ⟨J,Q,hJr,hJb,hΓJ⟩ := reciprocal_weighted_test μ hQ u w hε A C hu hw
  have hiR := (Lp.memLp (SobolevSpace.toLp μ hQ S)).integrable_sq.bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ R))
    (show ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ R x‖≤(N:ℝ) by
      simpa only [Real.norm_eq_abs] using hRb)
  have hiS := (Lp.memLp (SobolevSpace.toLp μ hQ S)).integrable_mul
    (localGamma_memLp_of_bounded_gradient μ hQ ℓ R M hLℓ)
  change Integrable (fun x => SobolevSpace.toLp μ hQ S x*localGamma μ hQ ℓ R x) μ at hiS
  have hiH := (localGamma_memL1 μ hQ u w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ H))
    (show ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ H x‖≤(B:ℝ) by
      simpa only [Real.norm_eq_abs] using hH)
  have hiD := (Lp.memLp (SobolevSpace.toLp μ hQ d)).integrable_mul
    (localGamma_memLp_of_bounded_gradient μ hQ u J L hLu)
  change Integrable (fun x => SobolevSpace.toLp μ hQ d x*localGamma μ hQ u J x) μ at hiD
  have hiJ := (Lp.memLp (SobolevSpace.toLp μ hQ d)).integrable_sq.bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ J))
    (show ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ J x‖≤(Q:ℝ) by
      simpa only [Real.norm_eq_abs] using hJb)
  have hpoint : (fun x => SobolevSpace.toLp μ hQ R x*(SobolevSpace.toLp μ hQ S x)^2+
      SobolevSpace.toLp μ hQ S x*localGamma μ hQ ℓ R x+
      SobolevSpace.toLp μ hQ H x*localGamma μ hQ u w x) =ᵐ[μ] fun x =>
      SobolevSpace.toLp μ hQ d x*localGamma μ hQ u J x+
      SobolevSpace.toLp μ hQ J x*(SobolevSpace.toLp μ hQ d x)^2 := by
    filter_upwards [hRr,hSr,hΓR,hJr,hΓJ,hHr,hu] with x hr hs hg hj hgj hh hu
    rw [hr,hs,hg,hj,hgj,hh]
    have hz : ε+SobolevSpace.toLp μ hQ u x≠0 :=
      (add_pos_of_pos_of_nonneg hε hu.1).ne'
    field_simp [hz]
    ring
  have hint : (∫ x, SobolevSpace.toLp μ hQ R x*(SobolevSpace.toLp μ hQ S x)^2 ∂μ)+
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ S) ℓ R+
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ H) u w =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ d) u J+
      (∫ x, SobolevSpace.toLp μ hQ J x*(SobolevSpace.toLp μ hQ d x)^2 ∂μ) := by
    unfold weightedGamma
    have e1 := integral_add hiR hiS
    have e2 := integral_add (hiR.add hiS) hiH
    have e3 := integral_add hiD hiJ
    simp only [Pi.add_apply] at e1 e2 e3
    rw [←e1,←e2,←e3]
    exact integral_congr_ae hpoint
  have hm := weakLaplacian_mixed_identity_L2 μ hQ u d J Q L hJb hLu hd
  have hfirst : weightedGamma μ hQ (SobolevSpace.toLp μ hQ J) u d =
      ∫ x, SobolevSpace.toLp μ hQ w x*localGamma μ hQ u d x /
        (ε+SobolevSpace.toLp μ hQ u x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hJr] with x hx
    rw [hx]
    ring
  rw [hfirst] at hm
  refine ⟨R,N,hRr,hRb,?_⟩
  linarith only [hint,hm]

end RegularPointCoordinates

end

end OAI
