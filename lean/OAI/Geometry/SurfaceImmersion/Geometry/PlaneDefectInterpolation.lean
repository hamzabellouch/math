import OAI.Geometry.SurfaceImmersion.Correction.DiagonalDefectModel

namespace OAI

/-! Convex interpolation with matching transverse signs retains the simple
axial zeros on one common rectangle. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeDefectInterpolation (F G : Base → Base) (s : ℝ) (x : Base) : Base :=
  (1-s) • F x+s • G x

lemma planeDefectInterpolation_smooth {F G : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun z : ℝ × Base => planeDefectInterpolation F G z.1 z.2) :=
  ((contDiff_const.sub contDiff_fst).smul (hF.comp contDiff_snd)).add
    (contDiff_fst.smul (hG.comp contDiff_snd))

lemma planeDefectInterpolation_fderiv {F G : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (s : ℝ) (x : Base) :
    fderiv ℝ (planeDefectInterpolation F G s) x =
      (1-s) • fderiv ℝ F x+s • fderiv ℝ G x :=
  (((hF.differentiable (by simp) x).hasFDerivAt.const_smul (1-s)).add
    ((hG.differentiable (by simp) x).hasFDerivAt.const_smul s)).fderiv

lemma planeDefectInterpolation_axis {F G : Base → Base} {p q t : ℝ}
    (hF : F (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hG : G (crosscapAxis t) = ![(t-p)*(t-q),0]) (s : ℝ) :
    planeDefectInterpolation F G s (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  rw [planeDefectInterpolation,hF,hG,←add_smul]
  simp

theorem planeDefectInterpolation_two_zeros {F G : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {p q : ℝ} (hpq : p < q) {W : Set ℝ} (hW : IsOpen W) (hKW : Icc p q ⊆ W)
    (hFa : ∀ t ∈ W, F (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hGa : ∀ t ∈ W, G (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hsp : 0 < (fderiv ℝ F (crosscapAxis p) ![1,0] 1)*
      (fderiv ℝ G (crosscapAxis p) ![1,0] 1))
    (hsq : 0 < (fderiv ℝ F (crosscapAxis q) ![1,0] 1)*
      (fderiv ℝ G (crosscapAxis q) ![1,0] 1)) :
    ∃ (r : ℝ) (O : Set Base), 0 < r ∧ IsOpen O ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (p-r) (q+r), (![x,t] : Base) ∈ O) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ O, planeDefectInterpolation F G s x = 0 ↔
        x = crosscapAxis p ∨ x = crosscapAxis q := by
  have hsm := planeDefectInterpolation_smooth hF hG
  have hFs : ∀ s ∈ Icc (0:ℝ) 1, ContDiff ℝ ∞ (planeDefectInterpolation F G s) := by
    intro s _
    exact hsm.comp (contDiff_const.prodMk contDiff_id)
  have hD : Continuous (fun z : ℝ × Base => fderiv ℝ (planeDefectInterpolation F G z.1) z.2) := by
    simp_rw [planeDefectInterpolation_fderiv hF hG]
    exact ((continuous_const.sub continuous_fst).smul
      ((hF.continuous_fderiv (by simp)).comp continuous_snd)).add
      (continuous_fst.smul ((hG.continuous_fderiv (by simp)).comp continuous_snd))
  apply compact_two_zero_rectangle isCompact_Icc _ hFs hsm.continuous hD hpq
  · intro s _ t ht
    exact planeDefectInterpolation_axis (hFa t (hKW ht)) (hGa t (hKW ht)) s
  · intro s hs
    rw [planeDefectInterpolation_fderiv hF hG]
    apply convex_plane_jets_bijective _ _ (c := (p-p)+(p-q)) (by linarith)
      (normalized_axis_derivative hF.contDiffAt hW (hKW (left_mem_Icc.mpr hpq.le)) hFa)
      (normalized_axis_derivative hG.contDiffAt hW (hKW (left_mem_Icc.mpr hpq.le)) hGa) hsp hs
  · intro s hs
    rw [planeDefectInterpolation_fderiv hF hG]
    apply convex_plane_jets_bijective _ _ (c := (q-p)+(q-q)) (by linarith)
      (normalized_axis_derivative hF.contDiffAt hW (hKW (right_mem_Icc.mpr hpq.le)) hFa)
      (normalized_axis_derivative hG.contDiffAt hW (hKW (right_mem_Icc.mpr hpq.le)) hGa) hsq hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
