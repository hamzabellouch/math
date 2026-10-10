import OAI.Probability.DilutedSpin.CompoundRate
import OAI.Probability.DilutedSpin.PhysicalScoreRate
import OAI.Probability.DilutedSpin.ProxyRateIncrement
import OAI.Probability.DilutedSpin.ScoreIncrement

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

lemma scoreRate_real (N : ℕ) : (scoreRate N : ℝ)=scoreScale N := rfl

noncomputable def clippedPhysicalMean {q L : ℕ} (M : Model (q+1)) (C H : ℝ)
    (N : ℕ) [NeZero N] (s : ℝ≥0) (u : Spec L×ℕ → ℝ) : ℝ :=
  perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) (clipSample C) (clipReal H)
    (fun i : Spec L×ℕ => prior i.1) (gridExponents L) (spinFactor direction anchor u) (M.alpha*N) s

noncomputable def clippedReservoirIncrement {q L : ℕ} (M : Model (q+1)) (C H : ℝ)
    (N : ℕ) [NeZero N] (u : Spec L×ℕ → ℝ) : ℝ :=
  energyCavityIncrement (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) M.alpha (scoreRate N)
    (clipSample C) (clipReal H) (fun i : Spec L×ℕ => prior i.1) (gridExponents L)
    (spinFactor direction anchor u)

lemma clippedPhysicalMean_score_bound {q L : ℕ} (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (N : ℕ) (u : Spec L×ℕ → ℝ) :
    |clippedPhysicalMean M C H (N+1) (scoreRate (N+1)) u-
      clippedPhysicalMean M C H (N+1) (scoreRate N) u| ≤ scoreScale (N+1)-scoreScale N := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  simpa [clippedPhysicalMean,mul_one,one_mul,scoreRate_real,Nat.cast_add,Nat.cast_one,NNReal.coe_mk,Subtype.coe_mk] using
    perturbedMean_score_rate (N := N+1) M.disorder.toMeasure M.field.toMeasure (weights L)
      (clipSample C) (clipReal H) hθm (measurable_clipReal H) (fun i : Spec L×ℕ => prior i.1)
      (gridExponents L) (gridExponents_pos L) (spinFactor direction anchor u) (by norm_num : (0:ℝ)≤1)
      (clipSample_bound hC) (fun y => clipReal_bound hH y)
      (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)
      (M.alpha*(N+1)) (scoreRate N) (scoreRate (N+1)) (scoreScale_mono (Nat.le_succ N))

lemma clippedPhysicalMean_reservoir_bound {q L N : ℕ} [NeZero N]
    (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (u : Spec L×ℕ → ℝ) :
    |(clippedPhysicalMean M C H (N+1) (scoreRate N) u-clippedPhysicalMean M C H N (scoreRate N) u)-
      clippedReservoirIncrement M C H N u| ≤ C*cavityBadRate M.alpha q N+2*scoreScale N/(N+1) := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  have ht z : ‖(clipSample (p := q+1) C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa [Real.norm_eq_abs] using clipSample_bound hC z σ)
  simpa [clippedPhysicalMean,clippedReservoirIncrement,mul_one,one_mul,scoreRate_real,Nat.cast_add,Nat.cast_one,NNReal.coe_mk,Subtype.coe_mk] using
    perturbedMean_reservoir_increment (N := N) M.disorder.toMeasure M.field.toMeasure (weights L)
      M.alpha (scoreRate N) (clipSample C) (clipReal H) hθm (measurable_clipReal H)
      (interaction_clip_symmetric M C hsym) (fun i : Spec L×ℕ => prior i.1)
      (gridExponents L) (gridExponents_pos L) (gridExponents_last L) (spinFactor direction anchor u)
      hH hC (by norm_num : (0:ℝ)≤1) ht (fun y => clipReal_bound hH y)
      (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
