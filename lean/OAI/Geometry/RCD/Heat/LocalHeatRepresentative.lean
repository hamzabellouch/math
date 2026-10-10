import OAI.Geometry.RCD.Sobolev.RadialLocalSobolev

namespace OAI

/-! # Removing the affine gauge from a local heat representative -/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

theorem local_heat_representative (p : X) {R s M : ℝ} (hR : 0 ≤ R) (hs : 0 < s)
    (u : SobolevSpace μ Q) (H : X → ℝ)
    (hu : ∀ᵐ x ∂μ, x ∈ closedBall p R → SobolevSpace.toLp μ Q u x = -(s/2)*H x-M) :
    ∃ v : SobolevSpace μ Q,
      ∀ᵐ x ∂μ, x ∈ closedBall p R → SobolevSpace.toLp μ Q v x = H x := by
  have hr : 0 < R+1 := by linarith
  let χ := SobolevSpace.ofLipschitzCompact μ Q (radialCutoff_lipschitz p hr)
    (radialCutoff_hasCompactSupport p hr)
  let v := -(2/s) • u - (2*M/s) • χ
  have hχ : SobolevSpace.toLp μ Q χ =ᵐ[μ] radialCutoff p (R+1) :=
    SobolevSpace.ofLipschitzCompact_coe μ Q _ _
  have hv : SobolevSpace.toLp μ Q v =ᵐ[μ] fun x =>
      -(2/s)*SobolevSpace.toLp μ Q u x-(2*M/s)*SobolevSpace.toLp μ Q χ x := by
    dsimp only [v]
    rw [map_sub,map_smul,map_smul]
    filter_upwards [Lp.coeFn_sub (-(2/s) • SobolevSpace.toLp μ Q u)
      ((2*M/s) • SobolevSpace.toLp μ Q χ),
      Lp.coeFn_smul (-(2/s)) (SobolevSpace.toLp μ Q u),
      Lp.coeFn_smul (2*M/s) (SobolevSpace.toLp μ Q χ)] with x he hu hχ
    simp only [he,hu,hχ,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  refine ⟨v,?_⟩
  filter_upwards [hu,hχ,hv] with x hu hχ hv
  intro hx
  have hone : radialCutoff p (R+1) x = 1 :=
    radialCutoff_eq_one p hr ((mem_closedBall'.mp hx).trans (by linarith))
  rw [hv,hu hx,hχ,hone]
  field_simp
  ring

end RegularPointCoordinates

end

end OAI
