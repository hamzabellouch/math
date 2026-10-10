import OAI.Probability.InvariantIsing.Fields.SpinPriorRestrictedBoundary
import OAI.Probability.InvariantIsing.Arrays.TensorContactCap

namespace OAI

/-! A fixed field cap for constrained contact objectives, uniform in the
finite constraint and with its cube mass canceled. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma constrainedBlockValue_le_fieldValue {N : ℕ} (hN : 0<N)
    (C : Finset (Spin N)) (hC : C.Nonempty) (h : FieldStep) :
    constrainedBlockValue C h ≤ fieldValue h 0 := by
  have hp := (biasedConstrainedBlockValue_gap hN C hC h (fun _ => 0)).1
  have hu := biasedConstrainedBlockValue_univ hN h (fun _ => 0)
  have hz : biasedConstrainedBlockValue C h (fun _ => 0)=constrainedBlockValue C h := rfl
  rw [hz, hu] at hp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hp
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul] at hp
  linarith

lemma spinPriorRestrictedContactPressure_field_le
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (K : ℝ) (heig : ∀ i, |eig i| ≤ K)
    (cut : Fin (n+2) → ℝ) (hc : StrictMono cut) (hfirst : cut 0=0) (hlast : cut (Fin.last (n+1))=1)
    (p : TensorContactParameter N m n) (ht : p.1 ∈ Icc (0 : ℝ) 1)
    (ha : ∀ i, 0 ≤ p.2.1 i) (hu : ∀ j, |p.2.2.1 j| ≤ 2) (hv : ∀ j, |p.2.2.2 j| ≤ 2) :
    spinPriorContactPressure μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I
      (chainExponent cut) p + (N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2) ≤
      fieldValue (contactFieldStep cut hc hfirst hlast p.2.1 ha) 0+K/2+
        (2*m*perturbationScale N+8*perturbationScale N^2) := by
  have hp := spinPriorRestrictedContact_zero_cost hhaar hgauss hN μ hμ C hC eig I
    cut hc hfirst hlast p.2.1 ha p.2.2.1 hu p.2.2.2 hv
  have hb := constrainedBlockValue_le_fieldValue (by omega) C hC
    (contactFieldStep cut hc hfirst hlast p.2.1 ha)
  have hT := spinPriorContactPressure_temperature_modulus hhaar hgauss hN μ hμ
    (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut)
    p.2.1 ha p.2.2.1 p.2.2.2 K heig p.1 0
  have hK : 0 ≤ K := (abs_nonneg (eig ⟨0,by omega⟩)).trans (heig _)
  have ht' : |p.1-0| ≤ 1 := by simpa only [sub_zero,abs_of_nonneg ht.1] using ht.2
  have hT' := hT.trans (mul_le_of_le_one_right (div_nonneg hK (by norm_num)) ht')
  have htemp := (le_abs_self _).trans hT'
  have hbase := (le_abs_self _).trans hp
  change spinPriorContactPressure μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I
    (chainExponent cut) p+_ ≤ _
  have heq : (p.1,p.2.1,p.2.2.1,p.2.2.2)=p := by cases p; rfl
  rw [heq] at htemp
  linarith

/-- A coercive lower bound in the total nonnegative field increment. -/
theorem spinPriorRestrictedContactObjective_cap_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (K : ℝ)
    (heig : ∀ i, |eig i| ≤ K)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 ≤ d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n)
    (ht : p.1 ∈ Icc (0 : ℝ) 1) (ha : ∀ i, 0 ≤ p.2.1 i)
    (hu : ∀ j, |p.2.2.1 j| ≤ 2) (hv : ∀ j, |p.2.2.2 j| ≤ 2) :
    (d * (1 - cut (Fin.last n).castSucc) / 2) * (∑ i, p.2.1 i) -
        gaussianAbsoluteMean * Real.sqrt (∑ i, p.2.1 i) -
        (∑ i : Fin n, Real.log 2 / cut i.succ.castSucc) - K / 2 -
        (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) + S + V p.1 ≤
      spinPriorContactObjective μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2)) V p := by
  let step := contactFieldStep cut hc hfirst hlast p.2.1 ha
  have hp := spinPriorRestrictedContactPressure_field_le hhaar hgauss hN μ hμ C hC eig I K heig
    cut hc hfirst hlast p ht ha hu hv
  have hf := fieldValue_add_pairing_cap trial hd htrial step
  have hpair := fieldPairing_contactFieldStep trial cut hc hfirst hlast p.2.1 ha values hvalues
  change fieldPairing trial step = _ at hpair
  rw [hpair, fieldPartitionConstant_contactFieldStep] at hf
  change fieldValue step 0 + (∑ i, ((cut i.succ - cut i.castSucc) * values i) *
      finiteFieldPath p.2.1 i) / 2 ≤
    -(d * (1 - cut (Fin.last n).castSucc) / 2) * finiteFieldPath p.2.1 n +
      gaussianAbsoluteMean * Real.sqrt (finiteFieldPath p.2.1 n) +
      (∑ i : Fin n, Real.log 2 / cut i.succ.castSucc) at hf
  rw [finiteFieldPath_last] at hf
  have hU : 0 ≤ ∑ j : Fin N, perturbationWeight j * (p.2.2.1 j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _))
  have hW : 0 ≤ ∑ j : Fin m, (p.2.2.2 j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  change spinPriorContactPressure μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut) p+(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2) ≤
    fieldValue step 0 + K / 2 + (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) at hp
  unfold spinPriorContactObjective
  linarith

/-- One fixed cap works for every dimension and every allowed perturbation
parameter.  Thus a negative contact sublevel cannot touch its field face. -/
theorem exists_spinPriorRestrictedContactObjective_cap
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m n : ℕ) (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (K S L : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ) (_hN : 3 ≤ N)
      (μ : Measure (SpecialOrthogonal N)) (_hμprob : IsProbabilityMeasure μ)
      (_hμ : μ.IsMulLeftInvariant) (C : Finset (Spin N)) (hC : C.Nonempty) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
      (_heig : ∀ i, |eig i| ≤ K) (V : ℝ → ℝ)
      (_hV : ∀ t ∈ Icc (0 : ℝ) 1, L ≤ V t) (p : TensorContactParameter N m n),
      p.1 ∈ Icc (0 : ℝ) 1 → (∀ i, 0 ≤ p.2.1 i) →
      (∀ j, |p.2.2.1 j| ≤ 2) → (∀ j, |p.2.2.2 j| ≤ 2) →
      spinPriorContactObjective μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2)) V p < 0 →
      (∑ i, p.2.1 i) < H := by
  let e := d * (1 - cut (Fin.last n).castSucc) / 2
  let Cq := ∑ i : Fin n, Real.log 2 / cut i.succ.castSucc
  have he : 0 < e := by
    have hcut : cut (Fin.last n).castSucc < 1 := by
      simpa only [hlast] using hc (Fin.castSucc_lt_last (Fin.last n))
    dsimp only [e]
    positivity
  obtain ⟨H, hH, hbound⟩ := exists_linear_sqrt_cap he gaussianAbsoluteMean
    (Cq + K / 2 + (2 * m + 8) - S - L) 0
  refine ⟨H, hH, ?_⟩
  intro N hN μ hμprob hμ C hC eig I heig V hV p ht ha hu hv hneg
  have : IsProbabilityMeasure μ := hμprob
  by_contra hn
  have hx : H ≤ ∑ i, p.2.1 i := le_of_not_gt hn
  have hs := hbound (∑ i, p.2.1 i) hx
  have hcap := spinPriorRestrictedContactObjective_cap_bound hhaar hgauss hN μ hμ C hC eig I K heig
    cut hc hfirst hlast trial values hvalues d hd.le htrial S V p ht ha hu hv
  have herr : 2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 ≤ 2 * m + 8 := by
    have h1 := InvariantIsing.perturbationScale_le_one (by omega : 0 < N)
    have h2 := perturbationScale_sq_le_one (by omega : 0 < N)
    have h1' := mul_le_mul_of_nonneg_left h1
      (show 0 ≤ (2 : ℝ) * m from mul_nonneg (by norm_num) (Nat.cast_nonneg m))
    have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (8 : ℝ) by norm_num)
    linarith
  have hv' := hV p.1 ht
  change -e * (∑ i, p.2.1 i) + gaussianAbsoluteMean * Real.sqrt (∑ i, p.2.1 i) +
    (Cq + K / 2 + (2 * m + 8) - S - L) ≤ 0 at hs
  change e * (∑ i, p.2.1 i) - gaussianAbsoluteMean * Real.sqrt (∑ i, p.2.1 i) -
    Cq - K / 2 - _ + S + V p.1 ≤ _ at hcap
  linarith

end InvariantIsing

end

end OAI
