import OAI.Probability.InvariantIsing.Fields.SpinPriorPerturbationCost
import OAI.Probability.InvariantIsing.Fields.SpinPriorFieldMean
import OAI.Probability.InvariantIsing.Magnetic.MagneticSliceFieldBound
import OAI.Probability.InvariantIsing.Arrays.TensorContactStep

namespace OAI

/-! The actual constrained contact boundary retains the cube-mass constant
until it cancels from the physical objective. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorRestrictedContact_zero_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (cut : Fin (n+2) → ℝ) (hc : StrictMono cut) (hfirst : cut 0=0) (hlast : cut (Fin.last (n+1))=1)
    (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2) :
    |spinPriorContactPressure μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I
        (chainExponent cut) (0,a,u,v)-
      (constrainedBlockValue C (contactFieldStep cut hc hfirst hlast a ha)-
        (N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2))| ≤
      2*m*perturbationScale N+8*perturbationScale N^2 := by
  let step := contactFieldStep cut hc hfirst hlast a ha
  have hp := spinPriorPerturbationPressureMean_cost (n := n) hhaar hgauss hN μ hμ
    (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut) 0
    (finiteFieldPath a) (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0) u hu v hv
  have he := spinPriorMeanPressure_restricted_field hhaar hgauss hN μ hμ C hC I
    (fun j : Fin N => enumeratedSpectralDegree m j)
    (fun j : Fin N => enumeratedTreeDegree m j) step
  rw [heightSequence_contactFieldStep] at he
  change spinPriorMeanPressure (n := n) μ (restrictedSpinPrior C hC : Measure (Spin N))
    (fun _ => 0) (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j) 0
    (chainExponent cut) (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath a) =
    constrainedBlockValue C (contactFieldStep cut hc hfirst hlast a ha)-
      (N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2) at he
  have hdiag : diagonalPerturbedEigenvalues eig I 0 0 = fun _ => 0 := by
    ext i
    simp [diagonalPerturbedEigenvalues]
  have hamp : tensorPerturbationAmplitude N 0 = 0 := by
    ext i
    simp [tensorPerturbationAmplitude]
  simp only [spinPriorPerturbationPressureMean, hdiag, hamp, he, add_sub_add_right_eq_sub] at hp
  exact hp

lemma spinPriorRestrictedContact_zero_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (cut : Fin (n+2) → ℝ) (hc : StrictMono cut) (hfirst : cut 0=0) (hlast : cut (Fin.last (n+1))=1)
    (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (trial : OverlapPath) (values : Fin (n+1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s=values i)
    (S : ℝ) (hS : constrainedBlockValue C (contactFieldStep cut hc hfirst hlast a ha)+
      fieldPairing trial (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S)
    (V : ℝ → ℝ) (hV : V 0=0) :
    -(2*m*perturbationScale N+8*perturbationScale N^2) ≤
      spinPriorContactObjective μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I
        (chainExponent cut) (fun i => (cut i.succ-cut i.castSucc)*values i)
        (S-(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2)) V (0,a,u,v) := by
  have hp := spinPriorRestrictedContact_zero_cost hhaar hgauss hN μ hμ C hC eig I
    cut hc hfirst hlast a ha u hu v hv
  have hpair := fieldPairing_contactFieldStep trial cut hc hfirst hlast a ha values hvalues
  rw [hpair] at hS
  have hU : 0 ≤ ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _)
  have hW : 0 ≤ ∑ j : Fin m, (v j-3/2)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hh := (abs_le.mp hp).2
  simp only [spinPriorContactObjective, hV]
  linarith

end InvariantIsing

end

end OAI
