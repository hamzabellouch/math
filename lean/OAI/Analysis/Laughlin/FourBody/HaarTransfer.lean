import OAI.Analysis.Laughlin.Fock.OrbitIntegration
import OAI.Analysis.Laughlin.FourBody.UniformTransfer

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

theorem occupationQuadratic_rotation_integrable {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (L : I → Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationQuadratic Q R
      (fun i => L i (exteriorRotation Q g⁻¹ x))) sourceHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (isClosed_tsupport _).isCompact
  unfold occupationQuadratic occupationInner
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  apply continuous_const.mul
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q (L i) x A).star.mul
    (linearMap_rotation_coordinate_continuous Q (L j) x A)

theorem physical_fourBody_haar_transfer (Q D : ℕ) (hQ : 25 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(24 * fourBodyRho D Q * sourceFockEnergy Q x) ≤
      (2*Q-2+1 : ℕ) * (∫ g, occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D
          (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  have hw : Integrable (fun g : SourceSU2 => sourcePairWindow Q (exteriorRotation Q g⁻¹ x)) sourceHaar :=
    integrable_finsetSum _ (fun (p : ℕ) hp =>
      linearMap_rotation_norm_integrable Q (sourcePairEnd Q p) x)
  let L : Fin ((D+1)/2) → Module.End ℂ (Space Q) := fun i =>
    physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega)
  have hi := integral_mono ((hw.const_mul (fourBodyRho D Q)).neg)
    (occupationQuadratic_rotation_integrable Q (finiteFourMiddle Q D) L x)
    (fun g => source_fourBody_uniform_transfer Q D (by omega) hD₁ hD₂ (exteriorRotation Q g⁻¹ x))
  have hi := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))
  simp only [Pi.neg_apply] at hi
  rw [integral_neg,integral_const_mul] at hi
  have he : ((2*Q-2+1 : ℕ) : ℝ) *
      -(fourBodyRho D Q * (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar)) =
        -(24 * fourBodyRho D Q * sourceFockEnergy Q x) := by
    calc
      _ = -(fourBodyRho D Q * ((2*Q-2+1 : ℕ) *
        (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar))) := by ring
      _ = _ := by rw [sourcePairWindow_haar Q hQ]; ring
  rwa [he] at hi

noncomputable def averagedFourTransferError (Q : ℕ) : ℝ := 24 * uniformFourBodyRho Q

theorem averagedFourTransferError_nonneg (Q : ℕ) : 0 ≤ averagedFourTransferError Q :=
  mul_nonneg (by norm_num) (uniformFourBodyRho_nonneg Q)

theorem averagedFourTransferError_tendsto :
    Filter.Tendsto averagedFourTransferError Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun Q => 24 * uniformFourBodyRho Q) Filter.atTop (𝓝 0)
  simpa only [mul_zero] using uniformFourBodyRho_tendsto.const_mul 24

end Laughlin.Fock

end OAI
