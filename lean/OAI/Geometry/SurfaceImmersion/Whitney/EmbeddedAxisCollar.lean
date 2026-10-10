import OAI.Geometry.SurfaceImmersion.Geometry.CompactAxisRectangle
import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalInjectivity
import OAI.Geometry.SurfaceImmersion.Geometry.ImmersionLocalInjectivity

namespace OAI

/-! A regular collar of an embedded compact boundary arc is embedded
on a uniform thinner rectangle. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem embedded_axis_collar {F : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ t ∈ Icc a b, Function.Injective (fderiv ℝ F (crosscapAxis t)))
    (hinj : (Icc a b).InjOn (fun t => F (crosscapAxis t))) :
    ∃ r : ℝ, 0 < r ∧
      {x : Base | |x 0| ≤ r ∧ x 1 ∈ Icc a b}.InjOn F := by
  let K := crosscapAxis '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image crosscapAxis.continuous
  have hKI : K.InjOn F := by
    rintro x ⟨t,ht,rfl⟩ y ⟨s,hs,rfl⟩ h
    exact congrArg crosscapAxis (hinj ht hs h)
  have hlocal : ∀ x ∈ K, ∃ U : Set Base, IsOpen U ∧ x ∈ U ∧ U.InjOn F := by
    rintro x ⟨t,ht,rfl⟩
    exact euclidean_surface_local_injective hF _ (hreg t ht)
  obtain ⟨U,hU,hKU,hUI⟩ := compact_local_injectivity hF.continuous hK hKI hlocal
  obtain ⟨r,hr,hrect⟩ := compact_axis_rectangle hab hU (fun t ht => by
    simpa only [crosscapAxis_apply] using hKU (mem_image_of_mem crosscapAxis ht))
  have hsub : {x : Base | |x 0| ≤ r ∧ x 1 ∈ Icc a b} ⊆ U := by
    intro x hx
    have hh := hrect (x 0) (abs_le.mp hx.1) (x 1)
      ⟨by linarith [hx.2.1],by linarith [hx.2.2]⟩
    have he : (![x 0,x 1] : Base) = x := by ext i; fin_cases i <;> rfl
    simpa only [he] using hh
  exact ⟨r,hr,hUI.mono hsub⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
