import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientFormComparison
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientLimitTail
import OAI.Geometry.NodalSets.SmoothLimit.SphereSummableSmoothPair

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphereCoefficientDistance_le_sum_range (P : Finset Base) (J : ℕ)
    (d : ℕ → SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density) (n : ℕ) :
    sphereCoefficientDistance P J (d 0).tensor (d 0).density (d n).tensor (d n).density ≤
      ∑ k ∈ Finset.range n, sphereCoefficientDistance P J
        (d k).tensor (d k).density (d (k+1)).tensor (d (k+1)).density := by
  have hs (k : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d k).tensor (d k).smooth (d k).symm (d k).pos (d k).density (hd k) p
  induction n with
  | zero => simp only [sphereCoefficientDistance_self,Finset.range_zero,Finset.sum_empty,le_refl]
  | succ n ih =>
    exact (sphereCoefficientDistance_triangle P J (d 0).tensor (d n).tensor (d (n+1)).tensor
      (d 0).density (d n).density (d (n+1)).density (fun p _ ↦ hs 0 p)
      (fun p _ ↦ hs n p) (fun p _ ↦ hs (n+1) p)).trans
      (by
        simpa only [Finset.sum_range_succ,add_comm] using add_le_add_right ih
          (sphereCoefficientDistance P J (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density))

theorem sphere_coefficient_summable_positive_limit (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z=x)
    (a : SphereEnergyData) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a.density) :
    ∃ eta > 0, ∀ (d : ℕ → SphereEnergyData),
      (∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d k).density) → d 0=a →
      (∀ J : ℕ, Summable (fun k ↦ sphereCoefficientDistance P J (d k).tensor (d k).density
        (d (k+1)).tensor (d (k+1)).density)) →
      (∑' k, sphereCoefficientDistance P 0 (d k).tensor (d k).density
        (d (k+1)).tensor (d (k+1)).density) < eta →
      ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
        ∀ (Q : Finset Base) (J : ℕ),
          Summable (fun k ↦ sphereCoefficientDistance Q J (d k).tensor (d k).density
            (d (k+1)).tensor (d (k+1)).density) →
          Tendsto (fun k ↦ sphereCoefficientDistance Q J (d k).tensor (d k).density b.tensor b.density)
            atTop (𝓝 0) ∧
          ∀ k, sphereCoefficientDistance Q J (d k).tensor (d k).density b.tensor b.density ≤
            ∑' j, sphereCoefficientDistance Q J (d (k+j)).tensor (d (k+j)).density
              (d (k+j+1)).tensor (d (k+j+1)).density := by
  have hcover' : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z=x := by
    intro x
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨p,hp,z,interior_subset hz,he⟩
  obtain ⟨eta,heta,H⟩ := sphere_coefficient_relative_form_comparison P hcover'
    a.tensor a.smooth a.symm a.pos a.density ha a.positive (1/2) (by norm_num)
  refine ⟨eta,heta,?_⟩
  intro d hd hzero hseq hsmall
  obtain ⟨A,rho,hAs,hr,hAt,hrt⟩ := sphere_summable_smooth_pair P hcover d hd hseq
  have hds (n : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d n).tensor (d n).smooth (d n).symm (d n).pos (d n).density (hd n) p
  have hdist (n : ℕ) :
      sphereCoefficientDistance P 0 a.tensor a.density (d n).tensor (d n).density < eta := by
    have h := sphereCoefficientDistance_le_sum_range P 0 d hd n
    rw [hzero] at h
    apply h.trans_lt
    apply lt_of_le_of_lt _ hsmall
    exact (hseq 0).sum_le_tsum (Finset.range n) (fun k _ ↦ sphereCoefficientDistance_nonneg P 0
      (d k).tensor (d (k+1)).tensor (d k).density (d (k+1)).density
      (fun p _ ↦ hds k p) (fun p _ ↦ hds (k+1) p))
  have hcmp (n : ℕ) (x : Base) := H (d n).tensor (d n).density (d n).smooth
    (d n).symm (d n).pos (hd n) (hdist n) x
  have hsym : ∀ x alpha beta, A x alpha beta = A x beta alpha := by
    intro x alpha beta
    apply tendsto_nhds_unique (hAt x alpha beta)
    simpa only [(d _).symm] using hAt x beta alpha
  have hpos : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha := by
    intro x alpha hn
    have hle : a.tensor x alpha alpha/2 ≤ A x alpha alpha :=
      ge_of_tendsto (hAt x alpha alpha) (Filter.Eventually.of_forall (fun n ↦ by
        have h := (abs_le.mp ((hcmp n x).1 alpha)).1
        linarith))
    exact lt_of_lt_of_le (half_pos (a.pos x alpha hn)) hle
  have hrpos (x : Base) : 0 < rho x := by
    have hle : a.density x/2 ≤ rho x :=
      ge_of_tendsto (hrt x) (Filter.Eventually.of_forall (fun n ↦ by
        have h := (abs_le.mp (hcmp n x).2).1
        linarith))
    exact lt_of_lt_of_le (half_pos (a.positive x)) hle
  let b : SphereEnergyData := ⟨A,hAs,hsym,hpos,rho,hr.continuous,hrpos⟩
  refine ⟨b,hr,?_⟩
  intro Q J hsum
  exact sphere_coefficient_limit_tail Q J d b hd hr
    (fun p _ z _ ↦ intrinsicChartCoefficient_tendsto_of_pairings d A rho hAt hrt p z) hsum

end
end Yau.Target

end OAI
