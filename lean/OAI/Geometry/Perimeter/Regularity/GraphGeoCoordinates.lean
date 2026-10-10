import OAI.Geometry.Perimeter.Regularity.GraphCoordinates

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

theorem geoC_one_isometry {θ η : ℝ} (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2) (hθη : θ ≤ η)
    (e : Euc m ≃ₗᵢ[ℝ] W) {f : W → ℝ} {U : Set W} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U)
    (hh : ∀ p∈U, GeometricHolderAt η (fderiv ℝ f) p) :
    GeoC θ 1 (f ∘ e) (e ⁻¹' U) := by
  have hV : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hc : ContDiffOn ℝ 1 (f ∘ e) (e ⁻¹' U) :=
    hf.comp e.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hd : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m:=0) (by norm_num)).continuousOn
  have hdc : ContinuousOn (fderiv ℝ (f ∘ e)) (e ⁻¹' U) :=
    (hc.fderiv_of_isOpen hV (m:=0) (by norm_num)).continuousOn
  refine ⟨hc,geoC_zero_of_C1 hθ hθh hV hc,fun u ↦ ⟨hdc.clm_apply continuousOn_const,?_⟩⟩
  intro p hp
  have hm := ((hh (e p) hp).mono_scale hθ hθη).precomp_isometry e
  have hh' := hm.comp_C1 hθ
    ((hd.continuousAt (hU.mem_nhds hp)).comp e.continuous.continuousAt)
    (ContinuousLinearMap.apply ℝ ℝ (e u)).contDiff
  have he : (fun x ↦ fderiv ℝ (f ∘ e) x u)=(fun x ↦ fderiv ℝ f (e x) (e u)) := by
    funext x
    exact congrArg (fun L : Euc m →L[ℝ] ℝ ↦ L u)
      (e.toContinuousLinearEquiv.comp_right_fderiv (f:=f) (x:=x))
  rw [he]
  exact hh'

end RPISingularHarnack

end

end OAI
