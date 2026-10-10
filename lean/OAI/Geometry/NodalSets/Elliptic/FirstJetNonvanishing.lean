import OAI.Geometry.NodalSets.Elliptic.LocalFirstJetNonvanishing

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section

def sourceFirstJetSize (f : Coord → ℝ) (N : ℝ) (x : Coord) : ℝ :=
  |f x|+N⁻¹*sourceEuclideanNorm (fun i ↦ fderiv ℝ f x (Pi.single i 1))

lemma covector_norm_le_source (L : Coord →L[ℝ] ℝ) :
    ‖L‖ ≤ 4*sourceEuclideanNorm (fun i ↦ L (Pi.single i 1)) := by
  have hnorm := sourceEuclideanNorm_nonneg (fun i ↦ L (Pi.single i 1))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  have he : L v = ∑ i : Fin 4, v i*L (Pi.single i 1) := by
    conv_lhs => rw [hv]
    simp
  have hc (i : Fin 4) : |L (Pi.single i 1)| ≤ sourceEuclideanNorm (fun j ↦ L (Pi.single j 1)) :=
    (norm_le_pi_norm (fun j ↦ L (Pi.single j 1)) i).trans (norm_le_sourceEuclideanNorm _)
  rw [he]
  calc
    _ ≤ ∑ i : Fin 4, |v i| * |L (Pi.single i 1)| := by
      simpa only [norm_mul,Real.norm_eq_abs] using norm_sum_le (Finset.univ : Finset (Fin 4))
        (fun i ↦ v i*L (Pi.single i 1))
    _ ≤ ∑ _ : Fin 4, ‖v‖*sourceEuclideanNorm (fun j ↦ L (Pi.single j 1)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (norm_le_pi_norm v i) (hc i) (abs_nonneg _) (norm_nonneg v)
    _ = _ := by norm_num; ring

lemma firstJetSize_le_source (f : Coord → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : Coord) :
    firstJetSize f N x ≤ 4*sourceFirstJetSize f N x := by
  have h := mul_le_mul_of_nonneg_left (covector_norm_le_source (fderiv ℝ f x)) (inv_nonneg.mpr hN)
  unfold firstJetSize sourceFirstJetSize
  nlinarith [abs_nonneg (f x)]

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem source_first_jet_failure_tends_zero (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ Ω,
        sourceFirstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x <
        ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ≤
      ENNReal.ofReal ε := by
  intro ε hε
  filter_upwards [a.local_first_jet_failure_tends_zero hUD hU hUb hS
    S0 T0 hS0 hT0 hΩ hk0 hq hd hgap ε hε,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,(measure_mono ?_).trans hb⟩
  intro coeff hbad
  obtain ⟨x,hx,hsmall⟩ := hbad
  refine ⟨x,hx,?_⟩
  have h := firstJetSize_le_source
    (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z)
    (N := (n:ℝ)) (by positivity) x
  nlinarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
