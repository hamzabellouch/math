import OAI.Probability.PosteriorReplicas.Information.BinCutoff
import OAI.Probability.PosteriorReplicas.Information.FiniteEntropyBounds
import OAI.Probability.PosteriorReplicas.Information.ReplicaCost
import OAI.Probability.PosteriorReplicas.Information.ReplicaInformationBound

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma spherical_density_bound_one_le {d : ℕ} (hd : 0 < d)
    {f : Vec d → ℝ} {L : ℝ} (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)))] : 1 ≤ L := by
  let : NeZero d := ⟨hd.ne'⟩
  have : IsProbabilityMeasure (sphereLaw d) := by
    change IsProbabilityMeasure (BaseLaw.spherical.measure d); infer_instance
  apply ENNReal.one_le_ofReal.mp
  calc
    (1:ℝ≥0∞) = ((sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x))) univ := (measure_univ).symm
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂sphereLaw d := by rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    _ ≤ ∫⁻ _x, ENNReal.ofReal L ∂sphereLaw d := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfL x))
    _ = ENNReal.ofReal L := by simp

lemma gaussian_replica_information {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ} (hL : 1 ≤ L)
    (hfL : ∀ x, f x ≤ ENNReal.ofReal L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    conditionalInformation (sideLaw ℓ (signalMessageLaw ((sphereLaw d).withDensity f) κ)) ≤
      ENNReal.ofReal (messageEntropy (signalMessageLaw ((sphereLaw d).withDensity f) κ) / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)+Real.log L)) := by
  have hi := gaussian_replica_information_cost hd hk hm hkm hf ENNReal.ofReal_ne_top hfL κ
    (binCutoff d k L) (binCutoff_valid hL)
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hcost := comparisonCost_le hk hkm hdk hℓk (binCutoff d k L)
  have hlog := binCutoff_log_bound (by omega : k≤d) hL
  have hmm : 0 ≤ (m:ℝ) := by positivity
  have hkr : (k:ℝ) ≤ d := by exact_mod_cast (by omega : k≤d)
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1≤d)
  have hln : 0 ≤ Real.log (1+(d:ℝ)+Real.log L) := Real.log_nonneg (by linarith [Real.log_nonneg hL])
  have hb : (40+Real.pi)*(k:ℝ)+Real.log ((binCutoff d k L:ℝ)+2) ≤
      (100+Real.pi)*(d:ℝ)+Real.log (1+(d:ℝ)+Real.log L) := by
    nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hkr (show (0:ℝ)≤40+Real.pi by positivity)]
  have ha : 0 ≤ (100+Real.pi)*(d:ℝ)+Real.log (1+(d:ℝ)+Real.log L) := by positivity
  have hb' := mul_le_mul_of_nonneg_left hb hmm
  have hm1 : ((m+1:ℕ):ℝ) = (m:ℝ)+1 := by norm_cast
  rw [hm1]
  rw [add_assoc]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(m:ℝ)+1)).mpr
  rw [add_mul,div_mul_cancel₀ _ (by positivity : (m:ℝ)+1 ≠ 0)]
  nlinarith

lemma gaussian_replica_information_real {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k)
    (p : Measure (Vec d)) [IsProbabilityMeasure p]
    {f : Vec d → ℝ} (hf : Measurable f) {L : ℝ} (hL : 1 ≤ L)
    (hfL : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hp : p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)))
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    conditionalInformation (sideLaw ℓ (signalMessageLaw p κ)) ≤
      ENNReal.ofReal (messageEntropy (signalMessageLaw p κ) / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)+Real.log L)) := by
  subst p
  exact gaussian_replica_information hd hk hm hkm hdk hℓk hf.ennreal_ofReal hL
    (fun x => ENNReal.ofReal_le_ofReal (hfL x).2) κ

end PosteriorReplicas
end

end OAI
