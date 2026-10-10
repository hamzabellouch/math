import OAI.Geometry.NodalSets.Charts.MetricCoercivity
import OAI.Geometry.NodalSets.Elliptic.FirstJetNonvanishing

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma sourceEuclideanNorm_smul (r : ℝ) (v : Coord) :
    sourceEuclideanNorm (r • v) = |r| * sourceEuclideanNorm v := by
  simp only [sourceEuclideanNorm,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs]

lemma source_covector_le_norm (L : Coord →L[ℝ] ℝ) :
    sourceEuclideanNorm (fun i ↦ L (Pi.single i 1)) ≤ 2*‖L‖ := by
  apply (sourceEuclideanNorm_le _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg L)).mpr
  intro i
  simpa only [Pi.norm_single,norm_one,mul_one] using L.le_opNorm (Pi.single i (1:ℝ))

def sourceFrequency (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (q : Coord) (s : ℝ) : Coord :=
  fun i ↦ g q (Pi.single i 1)/s

lemma metric_frequency_annulus (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (μ B : ℝ) (hμ : 0 < μ) (hB : 0 < B) (hg : ‖g‖ ≤ B)
    (hc : ∀ v, μ*‖v‖^2 ≤ g v v) (q : Coord) (sx sy : ℝ)
    (hx : 0 < sx) (hy : 0 < sy) (hlen : g q q = sy^2)
    (hrlo : sx/2 ≤ sy) (hrhi : sy ≤ 2*sx) :
    Real.sqrt μ/8 ≤ sourceEuclideanNorm (sourceFrequency g q sx) ∧
      sourceEuclideanNorm (sourceFrequency g q sx) ≤ 4*B/Real.sqrt μ := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hs2 := Real.sq_sqrt hμ.le
  have hq : ‖q‖ ≤ sy/Real.sqrt μ := by
    apply (le_div_iff₀ hs).mpr
    have hh := hc q
    rw [hlen] at hh
    nlinarith [norm_nonneg q]
  let l := sourceEuclideanNorm (fun i ↦ g q (Pi.single i 1))
  have hl : 0 ≤ l := sourceEuclideanNorm_nonneg _
  have hlo : Real.sqrt μ*sy ≤ 4*l := by
    have he := ((le_abs_self (g q q)).trans ((g q).le_opNorm q)).trans
      (mul_le_mul_of_nonneg_right (covector_norm_le_source (g q)) (norm_nonneg q))
    rw [hlen] at he
    have he' : sy^2 ≤ 4*l*(sy/Real.sqrt μ) := he.trans
      (mul_le_mul_of_nonneg_left hq (by positivity))
    have hh := mul_le_mul_of_nonneg_right he' hs.le
    have hid : (4*l*(sy/Real.sqrt μ))*Real.sqrt μ = 4*l*sy := by field_simp
    rw [hid] at hh
    nlinarith
  have hhi : l ≤ 2*B*(sy/Real.sqrt μ) := by
    apply (source_covector_le_norm (g q)).trans
    have he := (g.le_opNorm q).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg q))
    calc
      _ ≤ 2*(B*‖q‖) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = 2*B*‖q‖ := by ring
      _ ≤ _ := by gcongr
  have hid : sourceFrequency g q sx = sx⁻¹ • (fun i ↦ g q (Pi.single i 1)) := by
    ext i
    simp only [sourceFrequency,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [hid,sourceEuclideanNorm_smul,abs_of_pos (inv_pos.mpr hx)]
  change Real.sqrt μ/8 ≤ sx⁻¹*l ∧ sx⁻¹*l ≤ 4*B/Real.sqrt μ
  have hmul : sx⁻¹*l = l/sx := by ring
  rw [hmul]
  constructor
  · apply (le_div_iff₀ hx).mpr
    nlinarith
  · apply (div_le_iff₀ hx).mpr
    apply hhi.trans
    calc
      _ ≤ 2*B*((2*sx)/Real.sqrt μ) := by gcongr
      _ = (4*B/Real.sqrt μ)*sx := by ring

theorem compact_metric_frequency_bounds (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {H : Set Coord} (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ κ > 0, ∃ K > 0, ∀ y ∈ H, ∀ q : Coord, ∀ sx sy : ℝ,
      0 < sx → 0 < sy → g y q q = sy^2 → sx/2 ≤ sy → sy ≤ 2*sx →
      κ ≤ sourceEuclideanNorm (sourceFrequency (g y) q sx) ∧
        sourceEuclideanNorm (sourceFrequency (g y) q sx) ≤ K := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  obtain ⟨μ,hμ,B,hB,hb⟩ := uniform_metric_coercivity (fun y : H ↦ g y)
    (continuousOn_iff_continuous_domRestrict.mp hg) (fun y ↦ hp y y.property)
  refine ⟨Real.sqrt μ/8,by positivity,4*B/Real.sqrt μ,by positivity,?_⟩
  intro y hy q sx sy hx hs hlen hlo hhi
  exact metric_frequency_annulus (g y) μ B hμ hB (hb ⟨y,hy⟩).1
    (hb ⟨y,hy⟩).2 q sx sy hx hs hlen hlo hhi

end
end Yau.Geometry

end OAI
