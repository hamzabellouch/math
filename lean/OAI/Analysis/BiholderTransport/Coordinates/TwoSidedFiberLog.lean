import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ExpNonconjugacy

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TwoSidedFiberLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_coordinate_exp_inverse_of_nonconjugate {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ
      (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)
        (riemannianExp (n := n) x v)) p)) :
    ∃ e : OpenPartialHomeomorph (TangentSpace 𝓘(ℝ,Model n) x) (Model n),
      (e : TangentSpace 𝓘(ℝ,Model n) x → Model n) =
        (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)) ∧
      p ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (e p) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let f := fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)
  have hf : ContDiffAt ℝ ∞ f p :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞
      (extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)) (riemannianExp (n := n) x p) from
      contMDiffAt_extChartAt).comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  let D := fderiv ℝ f p
  have hi : Function.Injective D := hp
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) x
  let L : TangentSpace 𝓘(ℝ,Model n) x ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt (Model n) _ x)
  have hs : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank L.toLinearEquiv.finrank_eq).mp hi
  let A := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs)
  have hd : HasFDerivAt f (A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n) p :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  have he : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,rfl,he,?_⟩
  exact hf.to_localInverse hd (by simp)

lemma exists_smooth_two_sided_fiber_log_of_nonconjugate {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ
      (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)
        (riemannianExp (n := n) x v)) p)) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) ∧
      (∀ᶠ v in 𝓝 p, L (riemannianExp x v)=v) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse_of_nonconjugate hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_,?_⟩
  · have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
      (continuousAt_extChartAt y).eventually (e.open_target.mem_nhds (hep ▸ e.map_source hpe))
    have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
      (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
    have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
      have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
        rw [hLy]; exact extChartAt_source_mem_nhds y)
      exact H
    filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
    apply d.injOn hzs hsz
    have HR := e.right_inv hzt
    rw [he] at HR
    exact HR
  · filter_upwards [e.open_source.mem_nhds hpe] with v hv
    change e.symm (d (riemannianExp x v))=v
    rw [←show e v=d (riemannianExp x v) from congrFun he v]
    exact e.left_inv hv

end TwoSidedFiberLog
end WeakMTWTransport

end

end

end

end OAI
