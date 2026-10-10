import OAI.Probability.InvariantIsing.Fields.CascadeSeedRetainedLaw
import OAI.Probability.InvariantIsing.Fields.CascadeKeepUpdate
import OAI.Probability.InvariantIsing.Arrays.TensorAncestorRandomization

namespace OAI

/-! The actual retained Ising tensor cascade has a joint ancestor-seed representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensorRetainedCascade_seed_law {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) :
    ∃ ψ : ℕ → (SpinTensorIndex I degree → ℝ) → unitInterval → (SpinTensorIndex I degree → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = tensorAncestorMarkKernel eig U c I degree amplitude n b v i z) ∧
      ∀ z, (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure _).map
        (cascadeSeedTree n b ψ z) =
        (tensorCascadeLaw I degree n b v).map
          (tensorRetainedCascade eig U c I degree amplitude n b v z) := by
  obtain ⟨ψ, hψ, hlaw⟩ := tensorAncestorMarkKernel_seed hN eig U c I degree amplitude n b v hb
  refine ⟨ψ,hψ,hlaw,fun z => ?_⟩
  have h := cascadeSeedTree_retained_law n b (fun i => tensorGaussianLaw I degree (v i))
    (tensorCascadeMultiplier eig U c I degree amplitude n b v) ψ
    (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v) hψ
    (tensorCascadeMultiplier_pos eig U c I degree amplitude n b v)
    (tensorCascadeMultiplier_moment hN eig U c I degree amplitude n b v hb)
    hlaw z
  apply h.trans
  apply congrArg (Measure.map · (tensorCascadeLaw I degree n b v))
  funext T
  apply noiseTreeKeep_update_congr
  intro i hi
  funext p
  simp only [tensorCascadeStopped, stoppedUpdate, hi, ite_true]

end InvariantIsing

end

end OAI
