import OAI.Geometry.SurfaceImmersion.Atlas.SubmersionFiberLineChart
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A transverse zero fiber has a globally smooth local parametrization
with injective derivative, retaining its exact zero-fiber equation. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem smooth_regular_zero_arc_data {f : Base × Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base × Base) (hp : f p = 0)
    (hreg : Function.Surjective (fderiv ℝ f p)) :
    ∃ (t₀ : ℝ) (U : Set ℝ) (F : ℝ → Base × Base), IsOpen U ∧ t₀ ∈ U ∧
      ContDiff ℝ ∞ F ∧ F t₀ = p ∧
      (∀ t ∈ U, f (F t) = 0 ∧ Function.Injective (fderiv ℝ F t)) ∧ U.InjOn F ∧
      IsOpen {z : {x : Base × Base // f x = 0} | ∃ t ∈ U, F t = z.val} := by
  obtain ⟨e,hpe,hef,he,hi⟩ := double_locus_submersion_chart hf p hreg
  let t₀ := (e p).2
  have he0 : (0,t₀) = e p := by
    apply Prod.ext
    · exact (hef p).trans hp |>.symm
    · rfl
  let T : Set ℝ := {t | (0,t) ∈ e.target}
  have hT : IsOpen T := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have ht₀ : t₀ ∈ T := by change (0,t₀) ∈ e.target; rw [he0]; exact e.map_source hpe
  have hθ : ContDiffOn ℝ ∞ (fun t : ℝ => e.symm (0,t)) T :=
    hi.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ ht => ht)
  obtain ⟨U,hU,htU,hUT,F,hF,hEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t₀)) hT (singleton_subset_iff.mpr ht₀) hθ
  have hEF (t : ℝ) (ht : t ∈ U) : e (F t) = (0,t) := by
    rw [hEq ht]
    exact e.right_inv (hUT ht)
  refine ⟨t₀,U,F,hU,htU (mem_singleton _),hF,?_,?_,?_,?_⟩
  · rw [hEq (htU (mem_singleton _))]
    change e.symm (0,t₀) = p
    rw [he0,e.left_inv hpe]
  · intro t ht
    constructor
    · rw [← hef (F t),hEF t ht]
    · let g : Base × Base → ℝ := fun x => (e x).2
      have hg : ContDiff ℝ ∞ g := he.snd
      have hcomp : g ∘ F =ᶠ[𝓝 t] id := by
        filter_upwards [hU.mem_nhds ht] with s hs
        exact congrArg Prod.snd (hEF s hs)
      have hd : (fderiv ℝ g (F t)).comp (fderiv ℝ F t) = ContinuousLinearMap.id ℝ ℝ := by
        rw [← fderiv_comp t (hg.differentiable (by simp) _) (hF.differentiable (by simp) _),
          hcomp.fderiv_eq,fderiv_id]
      intro a b hab
      have hh := congrArg (fderiv ℝ g (F t)) hab
      change ((fderiv ℝ g (F t)).comp (fderiv ℝ F t)) a =
        ((fderiv ℝ g (F t)).comp (fderiv ℝ F t)) b at hh
      simpa only [hd,ContinuousLinearMap.id_apply] using hh
  · intro s hs t ht hst
    have hh : ((0 : ProjectionTarget 3),s) = (0,t) := (hEF s hs).symm.trans ((congrArg e hst).trans (hEF t ht))
    exact congrArg Prod.snd hh
  · obtain ⟨c,_,hcs,hce,hci⟩ := submersion_fiber_line_chart f e p hpe hp
      (fun z _ => hef z)
    have hz (t : ℝ) (ht : t ∈ U) : f (F t) = 0 := by
      rw [← hef (F t),hEF t ht]
    have hUsource (t : ℝ) (ht : t ∈ U) : F t ∈ e.source := by
      rw [hEq ht]
      exact e.map_target (hUT ht)
    have hUt : U ⊆ c.target := by
      intro t ht
      let z : {x : Base × Base // f x = 0} := ⟨F t,hz t ht⟩
      have hcz : c z = t := by rw [hce]; exact congrArg Prod.snd (hEF t ht)
      rw [← hcz]
      apply c.map_source
      rw [hcs]
      exact hUsource t ht
    have hciF (t : ℝ) (ht : t ∈ U) : (c.symm t).val = F t :=
      (hci t (hUt ht)).trans (hEq ht).symm
    have heq : {z : {x : Base × Base // f x = 0} | ∃ t ∈ U, F t = z.val} = c.symm '' U := by
      ext z
      constructor
      · rintro ⟨t,ht,hFz⟩
        exact ⟨t,ht,Subtype.ext ((hciF t ht).trans hFz)⟩
      · rintro ⟨t,ht,rfl⟩
        exact ⟨t,ht,(hciF t ht).symm⟩
    rw [heq]
    exact c.symm.isOpen_image_of_subset_source hU hUt

theorem smooth_regular_zero_arc {f : Base × Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base × Base) (hp : f p = 0)
    (hreg : Function.Surjective (fderiv ℝ f p)) :
    ∃ (t₀ : ℝ) (U : Set ℝ) (F : ℝ → Base × Base), IsOpen U ∧ t₀ ∈ U ∧
      ContDiff ℝ ∞ F ∧ F t₀ = p ∧
      (∀ t ∈ U, f (F t) = 0 ∧ Function.Injective (fderiv ℝ F t)) ∧ U.InjOn F := by
  obtain ⟨t,U,F,hU,ht,hF,hp,hreg,hinj,_⟩ := smooth_regular_zero_arc_data hf p hp hreg
  exact ⟨t,U,F,hU,ht,hF,hp,hreg,hinj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
