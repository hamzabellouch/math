import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace S] in
lemma supportConormal_of_level {H F : S × E → ℝ} {Y : S × E → E} {q : S × E}
    (hH : DifferentiableAt ℝ H q) (hY : DifferentiableAt ℝ Y q)
    (hF : DifferentiableAt ℝ F (supportParam Y q))
    (heul : H =ᶠ[nhds q] (fun p => inner ℝ p.2 (Y p)))
    (hgrad : ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w)
    (hl : (fun p => F (supportParam Y p)) =ᶠ[nhds q] (fun _ => 0))
    (lam : ℝ) (hn : ∀ z : E, fderiv ℝ F (supportParam Y q) (0,z) = lam*inner ℝ q.2 z) :
    fderiv ℝ F (supportParam Y q) = -lam • supportConormal H q := by
  have hs : DifferentiableAt ℝ (supportParam Y) q := differentiableAt_fst.prodMk hY
  have hz (v : S × E) : fderiv ℝ F (supportParam Y q)
      (fderiv ℝ (supportParam Y) q v) = 0 := by
    have he := (hF.hasFDerivAt.comp q hs.hasFDerivAt).fderiv
    have hh := hl.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (F ∘ supportParam Y) q = _ at hh
    rw [he] at hh
    simpa using congrArg (fun A : (S × E) →L[ℝ] ℝ => A v) hh
  have hb (s : S) : fderiv ℝ F (supportParam Y q) (s,0) =
      -lam * fderiv ℝ H q (s,0) := by
    have hh := hz (s,0)
    rw [supportParam_fderiv hY] at hh
    have hp : (s,fderiv ℝ Y q (s,0)) = (s,0)+(0,fderiv ℝ Y q (s,0)) := by simp
    rw [hp,map_add,hn,support_tangent_identity hH hY heul hgrad (s,0)] at hh
    linarith
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = (v.1,0)+(0,v.2) := by simp
  conv_lhs => rw [hv,map_add,hb,hn]
  change -lam * fderiv ℝ H q (v.1,0) + lam*inner ℝ q.2 v.2 =
    -lam * (fderiv ℝ H q (v.1,0)-inner ℝ q.2 v.2)
  ring

/- The literal support conormal is inward relative to the original solution
 graph, even after a general ambient affine change of variables. -/
theorem affineEpigraph_supportConormal_inward [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    0 < supportConormal H (s,e) (L.symm ((0 : Space n),1)) := by
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
  have hh := congrArg (fun A : (S × E) →L[ℝ] ℝ => A (L.symm ((0 : Space n),1))) hc
  change fderiv ℝ (affineDefining u a L) (s,Y (s,e)) (L.symm ((0 : Space n),1)) =
    -lam * supportConormal H (s,e) (L.symm ((0 : Space n),1)) at hh
  rw [affineDefining_deriv a L huc] at hh
  simp only [ContinuousLinearEquiv.apply_symm_apply,map_zero,zero_sub,neg_mul,neg_inj] at hh
  change 0 < supportConormal H (s,e) (L.symm ((0 : Space n),1))
  nlinarith

end AffineBernstein
end

end OAI
