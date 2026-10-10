import OAI.Probability.InvariantIsing.Gaussian.GaussianGramExcessBound
import OAI.Probability.InvariantIsing.Gaussian.GaussianTransposeLowerEdge
import OAI.Probability.InvariantIsing.Gaussian.GaussianSingularUpperEdge
import OAI.Probability.InvariantIsing.Spectral.SpectralExcessScale
import OAI.Probability.InvariantIsing.Spectral.SpectralExcessContinuity

namespace OAI

/-! Both spectral edges of the physical Gaussian Gram matrix, with arbitrary real scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma marchenkoPasturLower_positive_part {α : ℝ} (hα : 0 ≤ α) :
    marchenkoPasturLower α = (max (Real.sqrt α-1) 0)^2 := by
  have hs := Real.sq_sqrt hα
  have hn := Real.sqrt_nonneg α
  by_cases ha : α ≤ 1
  · have hh : Real.sqrt α-1 ≤ 0 := by nlinarith
    simp only [marchenkoPasturLower,ite_eq_left ha,max_eq_right hh,zero_pow (by decide : 2 ≠ 0)]
  · have hh : 0 ≤ Real.sqrt α-1 := by nlinarith
    rw [marchenkoPasturLower,ite_eq_right ha,marchenkoPasturA,max_eq_left hh]
    ring

lemma positive_part_deficit (x b : ℝ) (hb : 0 ≤ b) :
    max (max x 0-b) 0 = max (x-b) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx',max_eq_right (by linarith : 0-b ≤ 0),max_eq_right (by linarith : x-b ≤ 0)]

theorem gaussianPattern_spectralExcess_tendsto {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) (c : ℝ) :
    TendstoInMeasure P (fun k ω => spectralExcess
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)
      (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
      (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))) atTop (fun _ => 0) := by
  let L := max (Real.sqrt α-1) 0
  let U := 1+Real.sqrt α
  let du (k : ℕ) (ω : Ω) := max (gaussianPatternSingularMax (Z (k+1) ω)/Real.sqrt (k+1)-U) 0
  let dl (k : ℕ) (ω : Ω) := max (Real.sqrt α-1-
    gaussianPatternSingularMin (gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1))
      (Z (k+1) ω))/Real.sqrt (k+1)) 0
  let E (k : ℕ) (ω : Ω) := spectralExcess
    (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)
    (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
    (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
  have hU : TendstoInMeasure P du atTop (fun _ => 0) := gaussianPatternSingularMax_upper_edge hα.le P Z hZ
  have hL : TendstoInMeasure P dl atTop (fun _ => 0) := gaussianPatternTranspose_lower_edge hα P Z hZ
  have hbound (k : ℕ) (ω : Ω) : E k ω ≤ |c| * ((U+du k ω)^2-U^2+2*L*dl k ω) := by
    have hh := gaussianGram_spectralExcess_bound (Z (k+1) ω) L U (le_max_right _ _)
      (by dsimp [U]; positivity)
    have hb : 0 ≤ gaussianPatternSingularMin
        (gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1)) (Z (k+1) ω))/Real.sqrt (k+1) :=
      div_nonneg (gaussianPatternSingularMin_nonneg (Nat.succ_pos k) _) (Real.sqrt_nonneg _)
    rw [positive_part_deficit _ _ hb] at hh
    have hlo : marchenkoPasturLower α = L^2 := marchenkoPasturLower_positive_part hα.le
    have hup : marchenkoPasturB α = U^2 := rfl
    have he := spectralExcess_scale_le (gaussianPatternEigenvalues (Z (k+1) ω)) (L^2) (U^2) c
    dsimp only [E]
    rw [hlo,hup]
    exact he.trans (mul_le_mul_of_nonneg_left hh (abs_nonneg c))
  have hmeas (k : ℕ) : AEStronglyMeasurable (E k) P := by
    have hh := continuous_spectralExcess
      (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        fun i => c*gaussianPatternEigenvalues z i)
      (fun i => continuous_const.mul ((continuous_apply i).comp (continuous_gaussianPatternEigenvalues _ _)))
      (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
      (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
    exact (hh.measurable.aemeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable).aestronglyMeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro ns hns
  obtain ⟨u,hu,hua⟩ := (hU.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨v,hv,hva⟩ := (hL.comp (hns.comp hu).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u ∘ v,hu.comp hv,?_⟩
  filter_upwards [hua,hva] with ω hωu hωv
  have hau : Tendsto (fun k => du (ns (u (v k))) ω) atTop (𝓝 0) := hωu.comp hv.tendsto_atTop
  have hav : Tendsto (fun k => dl (ns (u (v k))) ω) atTop (𝓝 0) := hωv
  have ht := (((tendsto_const_nhds (x := U)).add hau).pow 2 |>.sub_const (U^2)).add
    (hav.const_mul (2*L)) |>.const_mul |c|
  have ht' : Tendsto (fun k => |c| *((U+du (ns (u (v k))) ω)^2-U^2+2*L*dl (ns (u (v k))) ω))
      atTop (𝓝 0) := by simpa only [add_zero,sub_self,mul_zero,zero_add] using ht
  exact squeeze_zero (fun k => spectralExcess_nonneg _ _ _)
    (fun k => hbound (ns (u (v k))) ω) ht'

end InvariantIsing

end

end OAI
