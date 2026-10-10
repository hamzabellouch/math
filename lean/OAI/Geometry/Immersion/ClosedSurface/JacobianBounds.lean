import OAI.Geometry.Immersion.ClosedSurface.SmoothCoordinates

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma continuous_coordDet : Continuous coordDet := by
  unfold coordDet
  fun_prop

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by simp)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



theorem compact_chart_jacobian_bounds {φ ψ : Base → Base} {U V K : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ p ∈ K, d ≤ |coordDet (fderiv ℝ φ p)| ∧ ‖fderiv ℝ φ p‖ ≤ C := by
  have hD : ContinuousOn (fderiv ℝ φ) K :=
    (hφ.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  have hd : ContinuousOn (fun p => |coordDet (fderiv ℝ φ p)|) K :=
    (continuous_coordDet.comp_continuousOn hD).abs
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hD
  by_cases hn : K.Nonempty
  · obtain ⟨p,hp,hm⟩ := hK.exists_isMinOn hn hd
    refine ⟨|coordDet (fderiv ℝ φ p)|,|C|+1,abs_pos.mpr ?_,by positivity,?_⟩
    · exact coordDet_fderiv_ne_zero_of_local_inverse hU hV hφ hψ hmap hinv (hKU hp)
    · intro q hq
      exact ⟨hm hq,(hC q hq).trans (by linarith [le_abs_self C])⟩
  · exact ⟨1,1,zero_lt_one,zero_lt_one,fun p hp => False.elim (hn ⟨p,hp⟩)⟩

end ClosedSurfaceR4.RealModes

end

end OAI
