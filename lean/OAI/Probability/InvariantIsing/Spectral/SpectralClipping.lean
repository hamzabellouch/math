import OAI.Probability.InvariantIsing.Spectral.EmpiricalSpectralLaw
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralSqueeze

namespace OAI

/-! Clipping the finite spectra to the limiting support interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

def spectralClip (a b x : ℝ) : ℝ := max a (min b x)

lemma continuous_spectralClip (a b : ℝ) : Continuous (spectralClip a b) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma spectralClip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : spectralClip a b x∈Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma spectralClip_eq {a b x : ℝ} (hx : x∈Icc a b) : spectralClip a b x=x := by
  simp only [spectralClip,min_eq_right hx.2,max_eq_right hx.1]

lemma spectralClip_close {a b x η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (hx : a-η ≤ x ∧ x ≤ b+η) : |spectralClip a b x-x| ≤ η := by
  by_cases ha : x < a
  · have he : spectralClip a b x=a := by simp [spectralClip,min_eq_right (ha.le.trans hab),max_eq_left ha.le]
    rw [he,abs_of_nonneg (sub_nonneg.mpr ha.le)]
    linarith [hx.1]
  · by_cases hb : b < x
    · have he : spectralClip a b x=b := by simp [spectralClip,min_eq_left hb.le,max_eq_right hab]
      rw [he,abs_of_nonpos (sub_nonpos.mpr hb.le)]
      linarith [hx.2]
    · rw [spectralClip_eq ⟨le_of_not_gt ha,le_of_not_gt hb⟩,sub_self,abs_zero]
      exact hη

lemma spectral_clip_empirical_tendsto
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k)
      (fun i => spectralClip a b (eig (k+1) i))) atTop (𝓝 ν) := by
  have he : ν.map (spectralClip a b)=ν := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    have h : spectralClip a b =ᵐ[(ν : Measure ℝ)] id := by
      filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
      exact spectralClip_eq (hbound hx)
    rw [Measure.map_congr h,Measure.map_id]
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ ν hweak
    (continuous_spectralClip a b)
  rw [he] at hh
  apply hh.congr
  intro k
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map _ _ _ (continuous_spectralClip a b).measurable

lemma spectral_clip_mean_pressure_close {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig : Fin N → ℝ)
    (a b η : ℝ) (hab : a ≤ b) (hη : 0 ≤ η)
    (heig : ∀ i, a-η ≤ eig i ∧ eig i ≤ b+η) :
    |(∫ V, rotatedPressure (fun i => spectralClip a b (eig i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ)-
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) (fun _ => 0) ∂μ| ≤ η/2 := by
  let K := (∑ i, |eig i|)+|a|+|b|
  have hsum : 0 ≤ ∑ i, |eig i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hi i : |eig i| ≤ K := by
    have hh := Finset.single_le_sum (fun i _ => abs_nonneg (eig i)) (Finset.mem_univ i)
    dsimp [K]
    linarith [abs_nonneg a,abs_nonneg b]
  have hc i : |spectralClip a b (eig i)| ≤ K := by
    have hh := spectralClip_mem hab (eig i)
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [hh.1,hh.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hd i := abs_le.mp (spectralClip_close hab hη (heig i))
  have hh := cavity_meanPressure_squeeze hN μ eig
    (fun i => spectralClip a b (eig i)) (fun i => spectralClip a b (eig i))
    (fun _ => 0) η K hi hc hc
    (fun i => by linarith [(hd i).2]) (fun i => by linarith [(hd i).1])
  rw [abs_le]
  constructor <;> linarith

end InvariantIsing

end

end OAI
