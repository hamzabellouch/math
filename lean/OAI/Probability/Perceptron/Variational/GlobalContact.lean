import Mathlib
import OAI.Probability.Perceptron.Variational.StepEntropy
import OAI.Probability.Perceptron.Variational.RightDerivativeIntegral
import OAI.Probability.Perceptron.Variational.DensityLipschitz

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceStepFieldCap (k : ℕ) (H : ℝ) : Set (Fin (k+1)→ℝ) :=
  Icc (fun _ => 0) (fun _ => H) ∩ {h | Monotone h}

def sourceContactCompactDomain (n k : ℕ) (α : ℝ≥0) (H : ℝ) : Set (SourceContactParameter n k) :=
  Icc 0 α ×ˢ (sourceStepFieldCap k H ×ˢ Icc (fun _ => 1) (fun _ => 2))

lemma sourceStepFieldCap_compact (k : ℕ) (H : ℝ) : IsCompact (sourceStepFieldCap k H) :=
  isCompact_Icc.inter_right isClosed_monotone

lemma sourceContactCompactDomain_compact (n k : ℕ) (α : ℝ≥0) (H : ℝ) :
    IsCompact (sourceContactCompactDomain n k α H) :=
  isCompact_Icc.prod ((sourceStepFieldCap_compact k H).prod isCompact_Icc)

lemma sourceContactCompactDomain_nonempty (n k : ℕ) (α : ℝ≥0) {H : ℝ} (hH : 0≤H) :
    (sourceContactCompactDomain n k α H).Nonempty := by
  refine ⟨(0,(fun _ => 0),(fun _ => 3/2)),?_,?_,?_⟩
  · exact ⟨le_rfl,zero_le⟩
  · exact ⟨⟨fun _ => le_rfl,fun _ => hH⟩,monotone_const⟩
  · constructor <;> intro j <;> norm_num

lemma sourceContactCompactDomain_subset (n k : ℕ) (α : ℝ≥0) (H : ℝ) :
    sourceContactCompactDomain n k α H ⊆ sourceContactDomain n k := by
  intro a ha
  exact ⟨ha.2.1.1.1,ha.2.1.2,fun j => ⟨ha.2.2.1 j,ha.2.2.2 j⟩⟩

def sourceStepContactObjective (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (a : SourceContactParameter n k) : ℝ :=
  -sourceJointPressure n k f p d (stepCumulative w) a-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+
    (entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2

lemma sourceStepContactObjective_continuousOn (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ) :
    ContinuousOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
      (sourceContactCompactDomain n k α H) := by
  have hp := (sourceJointPressure_continuousOn n k f p d (stepCumulative w)
    (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)).mono
      (sourceContactCompactDomain_subset n k α H)
  have hc : Continuous (fun a : SourceContactParameter n k =>
      -(∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal+
      (a.1:ℝ)*(controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ)+
      quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2) := by
    unfold quadraticBoxPenalty
    fun_prop
  convert hp.neg.add hc.continuousOn using 1
  ext a
  simp only [sourceStepContactObjective,Pi.add_apply,Pi.neg_apply]
  ring

lemma source_global_contact_exists (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) {H : ℝ} (hH : 0≤H) :
    ∃ a ∈ sourceContactCompactDomain n k α H,
      IsMinOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
        (sourceContactCompactDomain n k α H) a :=
  (sourceContactCompactDomain_compact n k α H).exists_isMinOn
    (sourceContactCompactDomain_nonempty n k α hH)
    (sourceStepContactObjective_continuousOn n k P f p d w q hw hw1 δ α H)

lemma source_global_contact_perturbation_min (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {a : SourceContactParameter n k} (ha : a∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q hw hw1 δ)
      (sourceContactCompactDomain n k α H) a) :
    IsMinOn (fun u => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u-
      sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u)
      (Icc (fun _ => 1) (fun _ => 2)) a.2.2 := by
  intro u hu
  change quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2-
    sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 a.2.2 ≤
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u-
    sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u
  have he := hmin (show (a.1,a.2.1,u)∈sourceContactCompactDomain n k α H from
    ⟨ha.1,ha.2.1,hu⟩)
  unfold sourceStepContactObjective sourceJointPressure at he
  change -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 a.2.2-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2 ≤
    -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u at he
  linarith

lemma source_global_contact_field (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {c : SourceContactParameter n k} (hc : c∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
      (sourceContactCompactDomain n k α H) c) (hcap : c.2.1 (Fin.last k)<H)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ i, 0≤a i) (ha : Monotone a) :
    (∑ i, w i*(q i:ℝ)*a i) ≤
      ∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
        (sourceCouplingHamiltonian n k f p d c.2.1 c.2.2 b) 2 (sourceFieldObservable a)
          ∂((sourceBaseDataLaw n k (stepCumulative w) c.1).prod countableGaussianLaw) := by
  let L := ∑ i, w i*(q i:ℝ)*a i
  let F : ℝ→ℝ := fun s => -sourceExpectedPressure n k f p d (fun l => c.2.1 l+s*a l)
    (stepCumulative w) c.1 c.2.2-s*L
  let ε := (H-c.2.1 (Fin.last k))/(a (Fin.last k)+1)
  have hε : 0<ε := div_pos (sub_pos.mpr hcap) (by linarith [ha0 (Fin.last k)])
  have hεa : ε*a (Fin.last k) ≤ H-c.2.1 (Fin.last k) := by
    have he : ε*(a (Fin.last k)+1)=H-c.2.1 (Fin.last k) := by
      dsimp [ε]; field_simp [ne_of_gt (show 0<a (Fin.last k)+1 by linarith [ha0 (Fin.last k)])]
    nlinarith
  have hm : IsMinOn F (Icc 0 ε) 0 := by
    intro s hs
    have hc' : (c.1,(fun l => c.2.1 l+s*a l),c.2.2)∈sourceContactCompactDomain n k α H := by
      refine ⟨hc.1,⟨⟨?_,?_⟩,hc.2.1.2.add (ha.const_mul hs.1)⟩,hc.2.2⟩
      · intro i
        exact add_nonneg (hc.2.1.1.1 i) (mul_nonneg hs.1 (ha0 i))
      · intro i
        have hi := hc.2.1.2 (Fin.le_last i)
        have hai : s*a i ≤ ε*a (Fin.last k) :=
          mul_le_mul hs.2 (ha (Fin.le_last i)) (ha0 i) hε.le
        linarith
    have he := hmin hc'
    have hsum : (∑ i, w i*(q i:ℝ)*(c.2.1 i+s*a i))=
        (∑ i, w i*(q i:ℝ)*c.2.1 i)+s*L := by
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros; ring
    change sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ c ≤
      sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ
        (c.1,(fun l => c.2.1 l+s*a l),c.2.2) at he
    dsimp only [sourceStepContactObjective,sourceJointPressure] at he
    rw [hsum] at he
    change F 0 ≤ F s
    dsimp only [F]
    simp only [zero_mul,add_zero,sub_zero]
    linarith
  let D := ∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
    (sourceCouplingHamiltonian n k f p d c.2.1 c.2.2 b) 2 (sourceFieldObservable a)
    ∂((sourceBaseDataLaw n k (stepCumulative w) c.1).prod countableGaussianLaw)
  have hd : HasDerivWithinAt F (D-L) (Ici 0) 0 := by
    have hp := sourceExpectedPressure_field_right_derivative n k f p d c.2.2 hc.2.1.1.1
      hc.2.1.2 ha0 ha (stepCumulative w) (stepCumulative_strictMono w hw)
      (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) c.1
    convert hp.neg.sub
      (((hasDerivAt_id (0:ℝ)).mul_const L).hasDerivWithinAt (s := Ici 0)) using 1 <;>
      first | rfl | simp [D]
  have hseg : segment ℝ (0:ℝ) ε ⊆ Icc 0 ε := by rw [segment_eq_Icc hε.le]
  have hn := hm.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hd.mono (fun _ hx => hx.1)).hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hseg)
  change 0≤(ε-0)*(D-L) at hn
  change L ≤ D
  nlinarith

end SphericalPerceptronFreeEnergy
end

end OAI
