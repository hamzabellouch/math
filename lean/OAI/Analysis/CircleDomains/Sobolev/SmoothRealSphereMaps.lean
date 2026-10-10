import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereEquivalence
import OAI.Analysis.CircleDomains.Sobolev.NormalizedCircleEnergy
import OAI.Analysis.CircleDomains.Transfer.CompletedChart

namespace OAI

/-!
# Smooth finite charts of sphere equivalences fixing infinity

The two genuine inverses induce smooth inverse maps in finite real
coordinates. Their restriction to any open source region is open,
which supplies the domain of each transported masked coordinate.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem IsSmoothSphereAt.contDiffAt_sphereRealMap
    {f : Sphere → Sphere} {x : ℝ × ℝ}
    (hf : IsSmoothSphereAt f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    ContDiffAt ℝ ∞ (sphereRealMap f) x := by
  let p : Sphere := ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)
  have hd : ContDiffAt ℝ ∞ (sphereLocalMap f p) (Complex.equivRealProdCLM.symm x) := by
    simpa only [p, chart_coe_self] using hf.2
  have hc := Complex.equivRealProdCLM.contDiff.contDiffAt.comp x
    (hd.comp x Complex.equivRealProdCLM.symm.contDiff.contDiffAt)
  have heq : sphereRealMap f =
      Complex.equivRealProdCLM ∘ sphereLocalMap f p ∘ Complex.equivRealProdCLM.symm := by
    funext y
    simp only [sphereRealMap, sphereLocalMap, p, chart, chartSymm,
      OnePoint.coe_ne_infty, ite_false, hfinite, Function.comp_apply]
  simpa only [heq] using hc

theorem coe_finiteCoord {p : Sphere} (hp : p ≠ OnePoint.infty) :
    ((finiteCoord p : ℂ) : Sphere) = p := CannonMobius.coe_coordinate hp

theorem sphereRealMap_mem
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : MapsTo f U V)
    {x : ℝ × ℝ} (hx : x ∈ realChartDomain U)
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    sphereRealMap f x ∈ realChartDomain V := by
  change ((Complex.equivRealProdCLM.symm (sphereRealMap f x) : ℂ) : Sphere) ∈ V
  simpa only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply,
    coe_finiteCoord hfinite] using hf hx

theorem sphereRealMap_left_inverse
    {f fi : Sphere → Sphere} {U : Set Sphere}
    (hl : ∀ p ∈ U, fi (f p) = p)
    {x : ℝ × ℝ} (hx : x ∈ realChartDomain U)
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    sphereRealMap fi (sphereRealMap f x) = x := by
  simp only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply,
    coe_finiteCoord hfinite, hl _ hx, finiteCoord_coe,
    ContinuousLinearEquiv.apply_symm_apply]

theorem isOpen_realChartDomain {U : Set Sphere} (hU : IsOpen U) : IsOpen (realChartDomain U) :=
  hU.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

namespace IsSmoothSphereEquivalence

variable {f fi : Sphere → Sphere} {U V : Set Sphere}
variable (h : IsSmoothSphereEquivalence f fi U V)
variable (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)

include h hU hfix

theorem inverse_fixes_infty : fi OnePoint.infty = OnePoint.infty := by
  simpa only [hfix] using h.left_inv OnePoint.infty hU

theorem infty_mem_target : OnePoint.infty ∈ V := hfix ▸ h.mapsTo hU

theorem finite_inv {z : ℂ} (hz : (z : Sphere) ∈ V) : fi (z : Sphere) ≠ OnePoint.infty :=
  finite_image_of_fixes_infty h.symm.bijOn.injOn (h.infty_mem_target hU hfix)
    (h.inverse_fixes_infty hU hfix) hz

theorem finite_forward {z : ℂ} (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty :=
  finite_image_of_fixes_infty h.bijOn.injOn hU hfix hz

theorem real_bijOn : BijOn (sphereRealMap f) (realChartDomain U) (realChartDomain V) := by
  refine ⟨fun x hx => sphereRealMap_mem h.mapsTo hx (h.finite_forward hU hfix hx),
    sphereRealMap_injOn h.bijOn.injOn (fun _ hx => hx)
      (fun _ hx => h.finite_forward hU hfix hx), ?_⟩
  intro y hy
  have hyfin := h.finite_inv hU hfix hy
  exact ⟨sphereRealMap fi y, sphereRealMap_mem h.mapsTo_inv hy hyfin,
    sphereRealMap_left_inverse h.right_inv hy hyfin⟩

theorem real_left_inv {x : ℝ × ℝ} (hx : x ∈ realChartDomain U) :
    sphereRealMap fi (sphereRealMap f x) = x :=
  sphereRealMap_left_inverse h.left_inv hx (h.finite_forward hU hfix hx)

theorem real_right_inv {y : ℝ × ℝ} (hy : y ∈ realChartDomain V) :
    sphereRealMap f (sphereRealMap fi y) = y :=
  sphereRealMap_left_inverse h.right_inv hy (h.finite_inv hU hfix hy)

theorem real_smooth {x : ℝ × ℝ} (hx : x ∈ realChartDomain U) :
    ContDiffAt ℝ ∞ (sphereRealMap f) x :=
  (h.smooth _ hx).contDiffAt_sphereRealMap (h.finite_forward hU hfix hx)

theorem real_smooth_inv {y : ℝ × ℝ} (hy : y ∈ realChartDomain V) :
    ContDiffAt ℝ ∞ (sphereRealMap fi) y :=
  (h.smooth_inv _ hy).contDiffAt_sphereRealMap (h.finite_inv hU hfix hy)

theorem real_image_eq {O : Set (ℝ × ℝ)} (hO : O ⊆ realChartDomain U) :
    sphereRealMap f '' O = realChartDomain V ∩ (sphereRealMap fi) ⁻¹' O := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(h.real_bijOn hU hfix).mapsTo (hO hx), by
      change sphereRealMap fi (sphereRealMap f x) ∈ O
      rwa [h.real_left_inv hU hfix (hO hx)]⟩
  · rintro ⟨hy, hiy⟩
    exact ⟨sphereRealMap fi y, hiy, h.real_right_inv hU hfix hy⟩

theorem isOpen_real_image (hV : IsOpen V) {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hOU : O ⊆ realChartDomain U) : IsOpen (sphereRealMap f '' O) := by
  rw [h.real_image_eq hU hfix hOU]
  exact (show ContinuousOn (sphereRealMap fi) (realChartDomain V) from
    fun y hy => (h.real_smooth_inv hU hfix hy).continuousAt.continuousWithinAt).isOpen_inter_preimage
      (isOpen_realChartDomain hV) hO

end IsSmoothSphereEquivalence
end CircleDomainRigidity

end

end OAI
