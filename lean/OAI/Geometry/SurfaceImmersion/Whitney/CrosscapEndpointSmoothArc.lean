import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisDoublePair
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapEndpointParameter
import OAI.Geometry.SurfaceImmersion.Whitney.SignedCrosscapAxis
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! The actual initial crosscap branch has a smooth regular embedded
parameterization including its singular endpoint, with both source projections regular. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_endpoint_smooth_arc (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (ε : ℝ) (P : SmoothCompactArc (planeModel.prod planeModel) (M × M)),
      0 < ε ∧ ε < 1/3 ∧ P.start = 0 ∧
      P.curve '' Icc P.start P.finish = Γ '' {t : I | (t:ℝ) ≤ ε} ∧
      P.curve P.start = (p,p) ∧
      (∀ u : I, (u:ℝ) = ε → P.curve P.finish = Γ u) ∧
      (∀ t ∈ P.domain, t ≠ P.start → P.curve t ∈ surfaceDoublePairs f) ∧
      ∀ t ∈ P.domain,
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.curve u).1) t) ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.curve u).2) t) := by
  obtain ⟨ε,s,d,hε,hε1,hs,hd,himage,htarget,hend⟩ :=
    crosscap_endpoint_parameter c hΓ hinj hzero heq hne
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  let A : ℝ → M := fun t => c.axisCurve (s*t)
  let B : ℝ → M := fun t => c.axisCurve (-(s*t))
  let V : Set ℝ := {t | crosscapAxis (s*t) ∈ c.source.target}
  let W : Set ℝ := {t | crosscapAxis (-(s*t)) ∈ c.source.target}
  let U := V ∩ W
  have hV : IsOpen V := c.source.open_target.preimage
    (crosscapAxis.continuous.comp (continuous_const.mul continuous_id))
  have hW : IsOpen W := c.source.open_target.preimage
    (crosscapAxis.continuous.comp ((continuous_const.mul continuous_id).neg))
  obtain ⟨hAs,hAi,hAj⟩ := c.signed_axis_curve hs0
  have hBs : ContMDiffOn 𝓘(ℝ) planeModel ∞ B W := by
    simpa only [neg_mul] using (c.signed_axis_curve (neg_ne_zero.mpr hs0)).1
  have hBi : ∀ t ∈ W, Function.Injective (mfderiv 𝓘(ℝ) planeModel B t) := by
    intro t ht
    change crosscapAxis (-(s*t)) ∈ c.source.target at ht
    have hb := (c.signed_axis_curve (neg_ne_zero.mpr hs0)).2.1 t (by simpa only [neg_mul] using ht)
    have he : (fun u => c.axisCurve (-s*u)) = B := by
      funext u
      dsimp only [B]
      rw [neg_mul]
    rw [he] at hb
    exact hb
  have hpair : ∀ t ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ) (planeModel.prod planeModel) (fun u => (A u,B u)) t) := by
    intro t ht
    have hAt := hAs.contMDiffAt (hV.mem_nhds ht.1)
    have hBt := hBs.contMDiffAt (hW.mem_nhds ht.2)
    have he := mfderiv_prodMk (hAt.mdifferentiableAt (by simp)) (hBt.mdifferentiableAt (by simp))
    have hj : Function.Injective
        ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)) := by
      intro x y hxy
      exact hAi t ht.1 (congrArg Prod.fst hxy)
    exact he.symm ▸ hj
  have hPi : InjOn (fun t => (A t,B t)) (Icc 0 d) := by
    intro x hx y hy hxy
    exact hAj (htarget x hx).1 (htarget y hy).1 (congrArg Prod.fst hxy)
  let P : SmoothCompactArc (planeModel.prod planeModel) (M × M) :=
    ⟨(fun t => (A t,B t)),0,d,hd,U,hV.inter hW,htarget,
      (hAs.mono inter_subset_left).prodMk (hBs.mono inter_subset_right),hpair,hPi⟩
  obtain ⟨_,_,_,_,_,hK0,_⟩ := c.axis_curve
  refine ⟨ε,P,hε,hε1,rfl,himage,?_,hend,?_,?_⟩
  · change (c.axisCurve (s*0),c.axisCurve (-(s*0))) = (p,p)
    simp only [mul_zero,neg_zero,hK0]
  · intro t ht htn
    exact c.axis_double_pair (mul_ne_zero hs0 htn) ht.1 ht.2
  · intro t ht
    exact ⟨hAi t ht.1,hBi t ht.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
