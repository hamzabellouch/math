import OAI.Probability.InvariantIsing.Arrays.TensorCascadeDiagonalWard
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalWardLimits
import OAI.Probability.InvariantIsing.Arrays.TensorArrayLaw

namespace OAI

/-! The actual enriched diagonal Ward bound is exactly the corresponding
spectral-array residual, retaining the common rotation in both replicas. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal

namespace InvariantIsing

def spectralDiagonalWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m)
    (x : SpectralArray (m + 1)) : ℝ :=
  ρ a * (x (0,0) b.castSucc : ℝ) - ρ b * (x (0,0) a.castSucc : ℝ) +
    (eig a - eig b) * ((x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ))

def spectralDiagonalWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m)
    (x : SpectralArray (m + 1)) : ℝ :=
  (eig a - eig b) * ((x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ))

lemma continuous_spectralDiagonalWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m) :
    Continuous (spectralDiagonalWardDirect ρ eig a b) := by
  unfold spectralDiagonalWardDirect
  fun_prop

lemma continuous_spectralDiagonalWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m) :
    Continuous (spectralDiagonalWardFresh eig a b) := by
  unfold spectralDiagonalWardFresh
  fun_prop

lemma spectralDiagonalWardResidual_integral {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1))) (ρ eig : Fin m → ℝ) (a b : Fin m) :
    spectralDiagonalWardResidual Q ρ eig a b =
      (∫ x, spectralDiagonalWardDirect ρ eig a b x ∂(Q : Measure (SpectralArray (m + 1)))) -
      ∫ x, spectralDiagonalWardFresh eig a b x ∂(Q : Measure (SpectralArray (m + 1))) := by
  have hI (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
      Integrable F (Q : Measure (SpectralArray (m + 1))) :=
    (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable _
  have ha := hI (fun x => (x (0,0) a.castSucc : ℝ)) (by fun_prop)
  have hb := hI (fun x => (x (0,0) b.castSucc : ℝ)) (by fun_prop)
  have hself := hI (fun x => (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ)) (by fun_prop)
  have hoff := hI (fun x => (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)) (by fun_prop)
  unfold spectralDiagonalWardResidual spectralDiagonalWardDirect spectralDiagonalWardFresh
  have hadd := integral_add ((hb.const_mul (ρ a)).sub (ha.const_mul (ρ b)))
    (hself.const_mul (eig a-eig b))
  have hsub := integral_sub (hb.const_mul (ρ a)) (ha.const_mul (ρ b))
  have hprod := integral_sub hself hoff
  simp only [Pi.sub_apply] at hadd hsub hprod
  rw [hadd, hsub, hprod]
  simp only [integral_const_mul]
  ring

lemma tensorNamespacedArrayLaw_diagonalWard_residual {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (κ : Fin m → ℝ) (a d : Fin m)
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    spectralDiagonalWardResidual (tensorNamespacedArrayLaw μ eig c I degree amp n b treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
  let ρ := fun j => ((I j).card : ℝ) / N
  let Q := tensorNamespacedArrayLaw μ eig c I degree amp n b treeDegree h
  have hdir : (∫ x, spectralDiagonalWardDirect ρ κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amp n b treeDegree h
      _ (continuous_spectralDiagonalWardDirect ρ κ a d) _
      (fun i : Fin 1 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalDirect_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardDirect, tensorDiagonalBlockDirect, spectralJointEntry_spectral, ρ, Fin.val_zero]
    ring
  have hfresh : (∫ x, spectralDiagonalWardFresh κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amp n b treeDegree h
      _ (continuous_spectralDiagonalWardFresh κ a d) _
      (fun i : Fin 2 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalFresh_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardFresh, tensorDiagonalBlockFresh, spectralJointEntry_spectral, Fin.val_zero, Fin.val_one]
    ring
  rw [spectralDiagonalWardResidual_integral Q ρ κ a d, hdir, hfresh]

/-- Exact finite-volume spectral-array diagonal Ward bound for the actual
tensor-enriched law, before taking any overlap limit. -/
theorem tensorNamespacedArrayLaw_diagonalWard_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ j, (degree r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (κ : Fin m → ℝ) (a d : Fin m) (had : Disjoint (I a) (I d))
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    |spectralDiagonalWardResidual
      (tensorNamespacedArrayLaw μ eig c I degree (tensorPerturbationAmplitude N u) n b treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d| ≤ 48 * D * perturbationScale N ^ 2 := by
  rw [tensorNamespacedArrayLaw_diagonalWard_residual μ eig c I degree (tensorPerturbationAmplitude N u)
    b treeDegree h κ a d ha hd]
  exact tensorNamespaced_diagonal_principal_bound hN μ eig c I degree treeDegree u hu D hD hdegree
    b h hh h0 (I a) (I d) had

end InvariantIsing

end

end OAI
