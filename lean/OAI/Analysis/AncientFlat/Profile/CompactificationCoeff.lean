import OAI.Analysis.AncientFlat.Geometry.AnnularCompactHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicAnnular
def compactArgument (z : ℝ × ℝ) : ℝ := z.2/z.1^4
def compactPrincipal (H : ℝ → ℝ) (z : ℝ × ℝ) : ℝ := H (compactArgument z)^2/16
def compactPotential (H : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  2/z.1^4*derivWithin H (Ici 0) (compactArgument z)/H (compactArgument z)
lemma compactArgument_smooth : ContDiffOn ℝ ∞ compactArgument rectangle := by
  apply contDiff_snd.contDiffOn.div (contDiff_fst.contDiffOn.pow 4)
  intro z hz
  exact pow_ne_zero _ (ne_of_gt (by linarith [hz.1.1] : 0<z.1))
lemma compactArgument_nonneg {z : ℝ × ℝ} (hz : z∈rectangle) : 0≤compactArgument z :=
  div_nonneg hz.2.1 (pow_nonneg (by linarith [hz.1.1] : 0≤z.1) _)
lemma compactification_pos (G H : ℝ → ℝ) (c κ : ℝ) (hc : 0<c) (hκ : 0<κ)
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) {u : ℝ} (hu : 0≤u) : 0<H u := by
  rcases hu.eq_or_lt with h0 | hu
  · rwa [←h0,hH0]
  · rw [hmatch u hu]
    exact hκ.trans_le (hpos _ (Real.rpow_nonneg hu.le _))
lemma compactPrincipal_smooth (H : ℝ → ℝ) (hH : ContDiffOn ℝ ∞ H (Ici 0)) :
    ContDiffOn ℝ ∞ (compactPrincipal H) rectangle := by
  exact ((hH.comp compactArgument_smooth (fun _ hz => compactArgument_nonneg hz)).pow 2).div
    contDiffOn_const (by norm_num)
lemma compactPotential_smooth (H : ℝ → ℝ) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hpos : ∀ u∈Ici (0:ℝ), 0<H u) : ContDiffOn ℝ 1 (compactPotential H) rectangle := by
  have harg : ContDiffOn ℝ 1 compactArgument rectangle := compactArgument_smooth.of_le (by simp)
  have hHd : ContDiffOn ℝ 1 (derivWithin H (Ici 0)) (Ici 0) :=
    hH.derivWithin (uniqueDiffOn_Ici 0) (by
      norm_num only [one_add_one_eq_two]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hHv : ContDiffOn ℝ 1 (fun z => H (compactArgument z)) rectangle :=
    (hH.of_le (show (1:ℕ∞ω)≤∞ by simp)).comp harg (fun _ hz => compactArgument_nonneg hz)
  have hfac : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => 2/z.1^4) rectangle :=
    contDiffOn_const.div (contDiff_fst.contDiffOn.pow 4)
      (fun z hz => pow_ne_zero _ (ne_of_gt (by linarith [hz.1.1] : 0<z.1)))
  exact (hfac.mul (hHd.comp harg (fun _ hz => compactArgument_nonneg hz))).div hHv
    (fun z hz => (hpos _ (compactArgument_nonneg hz)).ne')
end ParabolicAnnular

end

end OAI
