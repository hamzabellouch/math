import OAI.Geometry.SurfaceImmersion.Correction.NormalizedLinearModel
import OAI.Geometry.SurfaceImmersion.Geometry.CompactPlaneZero

namespace OAI

/-! Linearizing only the transverse coordinate preserves exactly the two zeros
on a common thin rectangle throughout the homotopy. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma plane_map_columns (L : Base →L[ℝ] Base) :
    L = (ContinuousLinearMap.proj 0).smulRight (L (![1,0] : Base))+
      (ContinuousLinearMap.proj 1).smulRight (L (![0,1] : Base)) := by
  ext v : 1
  have hv : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add,map_smul,map_smul]
  rfl

lemma normalizedLinearModel_fderiv_eq {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q t : ℝ} {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) :
    fderiv ℝ (normalizedLinearModel G p q) (crosscapAxis t) = fderiv ℝ G (crosscapAxis t) := by
  rw [normalizedLinearModel_fderiv_axis hG]
  rw [←normalized_axis_derivative hG.contDiffAt hW ht haxis]
  change (ContinuousLinearMap.proj 1 : Base →L[ℝ] ℝ).smulRight (fderiv ℝ G (crosscapAxis t) (![0,1] : Base))+
    (ContinuousLinearMap.proj 0 : Base →L[ℝ] ℝ).smulRight (fderiv ℝ G (crosscapAxis t) (![1,0] : Base)) = _
  rw [add_comm]
  exact (plane_map_columns _).symm

def linearDefectHomotopy (G : Base → Base) (p q s : ℝ) (x : Base) : Base :=
  (1-s) • G x+s • normalizedLinearModel G p q x

lemma linearDefectHomotopy_smooth {G : Base → Base} (hG : ContDiff ℝ ∞ G) (p q : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Base => linearDefectHomotopy G p q z.1 z.2) :=
  ((contDiff_const.sub contDiff_fst).smul (hG.comp contDiff_snd)).add
    (contDiff_fst.smul ((normalizedLinearModel_smooth hG p q).comp contDiff_snd))

lemma linearDefectHomotopy_fderiv {G : Base → Base} (hG : ContDiff ℝ ∞ G) (p q s : ℝ) (x : Base) :
    fderiv ℝ (linearDefectHomotopy G p q s) x =
      (1-s) • fderiv ℝ G x+s • fderiv ℝ (normalizedLinearModel G p q) x := by
  exact (((hG.differentiable (by simp) x).hasFDerivAt.const_smul (1-s)).add
    (((normalizedLinearModel_smooth hG p q).differentiable (by simp) x).hasFDerivAt.const_smul s)).fderiv

lemma linearDefectHomotopy_axis {G : Base → Base} {p q t : ℝ}
    (he : G (crosscapAxis t) = ![(t-p)*(t-q),0]) (s : ℝ) :
    linearDefectHomotopy G p q s (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  rw [linearDefectHomotopy,he,normalizedLinearModel_axis,←add_smul]
  simp

lemma linearDefectHomotopy_jet {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q t : ℝ} {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) (s : ℝ) :
    fderiv ℝ (linearDefectHomotopy G p q s) (crosscapAxis t) = fderiv ℝ G (crosscapAxis t) := by
  rw [linearDefectHomotopy_fderiv hG,normalizedLinearModel_fderiv_eq hG hW ht haxis,
    ←add_smul]
  simp

theorem linearDefectHomotopy_two_zeros {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q : ℝ} (hpq : p < q) {W : Set ℝ} (hW : IsOpen W) (hKW : Icc p q ⊆ W)
    (haxis : ∀ t ∈ W, G (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hIp : Function.Bijective (fderiv ℝ G (crosscapAxis p)))
    (hIq : Function.Bijective (fderiv ℝ G (crosscapAxis q))) :
    ∃ (r : ℝ) (O : Set Base), 0 < r ∧ IsOpen O ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (p-r) (q+r), (![x,t] : Base) ∈ O) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ O, linearDefectHomotopy G p q s x = 0 ↔
        x = crosscapAxis p ∨ x = crosscapAxis q := by
  have hsmooth := linearDefectHomotopy_smooth hG p q
  have hFs : ∀ s ∈ Icc (0:ℝ) 1, ContDiff ℝ ∞ (linearDefectHomotopy G p q s) := by
    intro s _
    exact hsmooth.comp (contDiff_const.prodMk contDiff_id)
  have hD : Continuous (fun z : ℝ × Base => fderiv ℝ (linearDefectHomotopy G p q z.1) z.2) := by
    simp_rw [linearDefectHomotopy_fderiv hG]
    exact ((continuous_const.sub continuous_fst).smul
      ((hG.continuous_fderiv (by simp)).comp continuous_snd)).add
      (continuous_fst.smul (((normalizedLinearModel_smooth hG p q).continuous_fderiv (by simp)).comp continuous_snd))
  apply compact_two_zero_rectangle isCompact_Icc _ hFs hsmooth.continuous hD hpq
  · intro s _ t ht
    exact linearDefectHomotopy_axis (haxis t (hKW ht)) s
  · intro s _
    rw [linearDefectHomotopy_jet hG hW (hKW (left_mem_Icc.mpr hpq.le)) haxis]
    exact hIp
  · intro s _
    rw [linearDefectHomotopy_jet hG hW (hKW (right_mem_Icc.mpr hpq.le)) haxis]
    exact hIq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
