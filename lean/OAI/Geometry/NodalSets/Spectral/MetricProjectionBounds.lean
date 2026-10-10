import OAI.Geometry.NodalSets.Charts.MetricNormalizationBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def metricPerpProjection (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e t : Coord) : Coord :=
  t-g e t • e

lemma metricPerpProjection_orthogonal (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e t : Coord) (he : g e e = 1) : g e (metricPerpProjection g e t) = 0 := by
  simp [metricPerpProjection,map_sub,map_smul,he]

lemma metricPerpProjection_difference_bound
    (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e e₀ t : Coord)
    {M K δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (he : ‖e‖ ≤ K) (he₀ : ‖e₀‖ ≤ K) (ht : ‖t‖ ≤ K)
    (hd : ‖e-e₀‖ ≤ δ) (hm : ‖g-h‖ ≤ η) (horth : h e₀ t = 0) :
    ‖metricPerpProjection g e t-t‖ ≤ (M*δ*K+η*K^2)*K := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hd
  have hη : 0 ≤ η := (norm_nonneg (g-h)).trans hm
  have h1 : |g (e-e₀) t| ≤ M*δ*K := (bilinear_pairing_bound _ _ _).trans (by gcongr)
  have h2 : |(g-h) e₀ t| ≤ η*K*K := (bilinear_pairing_bound _ _ _).trans (by gcongr)
  have hid : g e t = g (e-e₀) t+(g-h) e₀ t := by
    simp only [map_sub,sub_apply,horth]
    ring
  have hpair : |g e t| ≤ M*δ*K+η*K^2 := by
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans (by ring_nf; rfl))
  have heq : metricPerpProjection g e t-t = -(g e t • e) := by unfold metricPerpProjection; abel
  rw [heq,norm_neg,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hpair he (norm_nonneg _) (by positivity)

lemma metric_normalization_near_unit
    (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v w : Coord)
    {M K δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hw : ‖w‖ ≤ K) (hunit : h w w = 1)
    (hd : ‖v-w‖ ≤ δ) (hm : ‖g-h‖ ≤ η) (hδ : δ ≤ 1)
    (hsmall : 2*M*(K+1)*δ+η*(K+1)^2 ≤ 1/2) :
    1/2 ≤ g v v ∧ v ≠ 0 ∧
      ‖metricNormalize g v-w‖ ≤ 2*δ+8*(K+1)*(2*M*(K+1)*δ+η*(K+1)^2) := by
  have hv : ‖v‖ ≤ K+1 := by
    calc
      ‖v‖ ≤ ‖v-w‖+‖w‖ := norm_le_norm_sub_add _ _
      _ ≤ δ+K := add_le_add hd hw
      _ ≤ K+1 := by linarith
  have hw' : ‖w‖ ≤ K+1 := hw.trans (by linarith)
  have hdiag := bilinear_diagonal_change_bound g h v w hM (by linarith : 0 ≤ K+1) hg hv hw' hd hm
  rw [hunit] at hdiag
  have hpos : 1/2 ≤ g v v := by
    have hh := (abs_le.mp hdiag).1
    linarith
  have hn : v ≠ 0 := by
    intro hz
    simp only [hz,map_zero] at hpos
    norm_num at hpos
  refine ⟨hpos,hn,?_⟩
  have hb := metricNormalize_difference_bound g h v w hM (by linarith : 0 ≤ K+1)
    (by norm_num : (0:ℝ) < 1/2) hg hv hw' hd hm (by linarith) (by rw [hunit]; norm_num)
  rw [metricNormalize_fixed h w hunit] at hb
  convert hb using 1
  ring

theorem normalized_projection_stability
    (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e e₀ t : Coord)
    {M K δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (he : ‖e‖ ≤ K) (he₀ : ‖e₀‖ ≤ K) (ht : ‖t‖ ≤ K)
    (heunit : g e e = 1) (htunit : h t t = 1) (horth : h e₀ t = 0)
    (hd : ‖e-e₀‖ ≤ δ) (hm : ‖g-h‖ ≤ η)
    (hsmall₁ : (M*δ*K+η*K^2)*K ≤ 1)
    (hsmall₂ : 2*M*(K+1)*((M*δ*K+η*K^2)*K)+η*(K+1)^2 ≤ 1/2) :
    let q := metricPerpProjection g e t
    q ≠ 0 ∧ g (metricNormalize g q) (metricNormalize g q) = 1 ∧
      g e (metricNormalize g q) = 0 ∧
      ‖metricNormalize g q-t‖ ≤
        2*((M*δ*K+η*K^2)*K)+
          8*(K+1)*(2*M*(K+1)*((M*δ*K+η*K^2)*K)+η*(K+1)^2) := by
  dsimp only
  have hq := metricPerpProjection_difference_bound g h e e₀ t hM hK hg he he₀ ht hd hm horth
  obtain ⟨hpos,hn,hb⟩ := metric_normalization_near_unit g h (metricPerpProjection g e t) t
    hM hK hg ht htunit hq hm hsmall₁ hsmall₂
  exact ⟨hn,metricNormalize_unit g _ (by linarith),
    metricNormalize_orthogonal g e _ (metricPerpProjection_orthogonal g e t heunit),hb⟩

end
end Yau.Geometry

end OAI
