import OAI.Geometry.SurfaceImmersion.Geometry.MonotoneGermDiffeomorphism
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCurveCoordinates

namespace OAI

/-! A regular coordinate projection gives an actual local graph of a smooth
plane curve, with a globally smooth graph function available for cutoff gluing. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem plane_curve_graph {γ : ℝ → Base} (hγ : ContDiff ℝ ∞ γ) (t : ℝ)
    (h0 : deriv (fun u => γ u 0) t ≠ 0) :
    ∃ (g : ℝ → ℝ) (U : Set ℝ), ContDiff ℝ ∞ g ∧ IsOpen U ∧ t ∈ U ∧
      ∀ u ∈ U, γ u = ![γ u 0,g (γ u 0)] := by
  let d := deriv (fun u => γ u 0) t
  let s : ℝ := if 0 < d then 1 else -1
  have hd : 0 < s*d := by
    dsimp only [s]
    split_ifs with hp
    · simpa using hp
    · have hn : d < 0 := lt_of_le_of_ne (not_lt.mp hp) h0
      simpa using hn
  let h : ℝ → ℝ := fun u => s*γ u 0
  have hγ0 : ContDiff ℝ ∞ (fun u => γ u 0) := (contDiff_apply ℝ ℝ 0).comp hγ
  have hh : ContDiff ℝ ∞ h := contDiff_const.mul hγ0
  have hdt : deriv h t = s*d := (hγ0.differentiable (by simp) t |>.hasDerivAt.const_mul s).deriv
  obtain ⟨e,_,hei,_,he⟩ := increasing_smooth_germ_diffeomorphism hh t (hdt ▸ hd)
  let g : ℝ → ℝ := fun x => γ (e.symm (s*x)) 1
  have hg : ContDiff ℝ ∞ g := (contDiff_apply ℝ ℝ 1).comp
    (hγ.comp (hei.comp (contDiff_const.mul contDiff_id)))
  obtain ⟨U,hU,htU,hsub⟩ := mem_nhds_iff.mp he
  refine ⟨g,U,hg,htU,hsub,?_⟩
  intro u hu
  have heu : e u = s*γ u 0 := hU hu
  have hu' : e.symm (s*γ u 0) = u := by rw [← heu,e.symm_apply_apply]
  ext i
  fin_cases i
  · rfl
  · change γ u 1 = γ (e.symm (s*γ u 0)) 1
    rw [hu']

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
