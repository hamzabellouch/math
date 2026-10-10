import OAI.Dynamics.StandardMap.BandCap

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma stationary_half_real (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) :
    (μ (Ico (-1/2) 0)).toReal=(μ (Ico 0 1)).toReal/2 := by
  have h1 : μ (Ico (1/2) 1)=μ (Ico 0 (1/2)) := by
    convert! invariant_Ico_translate μ (dyadicHalf (dyadicInt 1):ℝ) (ht _) 0 (1/2) using 2 ; norm_num
  have h2 : μ (Ico (-1/2) 0)=μ (Ico 0 (1/2)) := by
    have hh := invariant_Ico_translate μ (dyadicHalf (dyadicInt 1):ℝ) (ht _) (-1/2) 0
    convert! hh.symm using 2 ; norm_num
  have hzero : μ (Ico 0 (1/2))<∞ := lt_of_le_of_lt (measure_mono (Ico_subset_Ico_right (by norm_num : (1/2:ℝ)≤1))) hf
  have hh := measure_Ico_split μ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
  rw [h1] at hh
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_add hzero.ne hzero.ne] at hr
  rw [h2]; linarith
lemma stationary_interval_real_upper (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) (n:ℕ) :
    (μ (Icc (-2) (n:ℝ))).toReal≤((n:ℝ)+3)*(μ (Ico 0 1)).toReal := by
  have hh : μ (Icc (-2) (n:ℝ))≤μ (Ico (-2) ((n:ℝ)+1)) := measure_mono (fun x hx => ⟨hx.1,by linarith [hx.2]⟩)
  have he : μ (Ico (-2) ((n:ℝ)+1))=(n+3:ℝ≥0∞)*μ (Ico 0 1) := by
    convert! stationary_Ico_nat μ ht (-2) (n+3) using 2 <;> push_cast <;> ring_nf
  rw [he] at hh
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hf.ne) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp : (n:ℝ≥0∞)≠∞) (by norm_num : (3:ℝ≥0∞)≠∞)] at hb
  simpa only [ENNReal.toReal_natCast,ENNReal.toReal_ofNat] using hb
lemma bandLaw_endpoint_map (μ:Measure NonAffineArray) (E:Set ℝ) (hE:MeasurableSet E) :
    bandLaw μ {d:NonAffineArray | endpointLeft d.val∈E}=bandIntensity μ E := by
  change (bandLaw μ) ((endpointLeft ∘ Subtype.val)⁻¹'E)=((bandLaw μ).map (endpointLeft ∘ Subtype.val)) E
  exact (Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) hE).symm
end StandardMapEntropy

end OAI
