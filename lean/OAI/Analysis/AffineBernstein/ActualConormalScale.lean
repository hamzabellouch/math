import Mathlib
import OAI.Analysis.AffineBernstein.SupportOrientation
import OAI.Analysis.AffineBernstein.ActualInverseMetric

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The scale relating the ACTUAL epigraph support conormal to the pulled-back
canonical graph conormal is strictly positive. The scale is produced from the
Gauss equations, not supplied as a geometric hypothesis. -/
theorem affineEpigraph_supportConormal_scale [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ∃ c : ℝ, 0 < c ∧ supportConormal H (s,e) =
      c • (graphConormalAt u (a+L (s,Y (s,e))).1).comp L.toContinuousLinearMap := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let F := affineDefining u a L
  obtain ⟨hb,hl,lam,hlam,hn⟩ := affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hs he
  have huc := hu.contDiffAt (hΩ.mem_nhds hb)
  have haf : ContDiffAt ℝ ∞ (fun q : S × E => a+L q) (supportParam Y (s,e)) :=
    contDiffAt_const.add L.contDiff.contDiffAt
  have hF : ContDiffAt ℝ ∞ F (supportParam Y (s,e)) :=
    (huc.comp (supportParam Y (s,e)) haf.fst).sub haf.snd
  obtain ⟨hH,hY,heul,hgrad⟩ := affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hs he
  have hlevel : (fun q => F (supportParam Y q)) =ᶠ[nhds (s,e)] (fun _ => 0) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hB.mem_nhds hs),
      continuous_snd.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds he)] with q hqs hqe
    exact (affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hqs hqe).2.1
  have hnormal (z : E) : fderiv ℝ F (supportParam Y (s,e)) (0,z) = lam*inner ℝ e z := by
    have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp (Y (s,e))
      ((hasFDerivAt_const s (Y (s,e))).prodMk (hasFDerivAt_id (Y (s,e))))
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A z) hn
    change fderiv ℝ (F ∘ Prod.mk s) (Y (s,e)) z = _ at hh
    rw [hd.fderiv] at hh
    exact hh
  have hc := supportConormal_of_level (hH.differentiableAt (by simp)) (hY.differentiableAt (by simp))
    (hF.differentiableAt (by simp)) heul hgrad.self_of_nhds hlevel lam hnormal
  refine ⟨lam⁻¹,inv_pos.mpr hlam,?_⟩
  apply ContinuousLinearMap.ext
  intro v
  have hh := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v) hc
  change fderiv ℝ (affineDefining u a L) (s,Y (s,e)) v =
    -lam * supportConormal H (s,e) v at hh
  rw [affineDefining_deriv a L huc] at hh
  change supportConormal H (s,e) v =
    lam⁻¹ * ((L v).2-fderiv ℝ u (a+L (s,Y (s,e))).1 (L v).1)
  field_simp
  linarith

end AffineBernstein
end

end OAI
