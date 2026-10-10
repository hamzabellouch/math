import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ExpNonconjugacy

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_joint_exp_inverse (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
    let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
    ∃ e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n),
      (e : Model n × Model n → Model n × Model n) =
        (fun q => (q.1, d (riemannianExp (χ.symm q).1 (χ.symm q).2))) ∧
      χ z ∈ e.source ∧ e.source ⊆ χ.target ∧
      (∀ q ∈ e.source, riemannianExp (χ.symm q).1 (χ.symm q).2 ∈ d.source) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let f : Model n × Model n → Model n := fun q =>
    d (riemannianExp (χ.symm q).1 (χ.symm q).2)
  let S := χ.target ∩ (fun q => riemannianExp (χ.symm q).1 (χ.symm q).2) ⁻¹' d.source
  have hχz : χ z ∈ χ.target := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hχ : ContMDiffOn 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm χ.target :=
    contMDiffOn_extChartAt_symm z
  have hE : ContMDiffOn 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞
      (fun q => riemannianExp (χ.symm q).1 (χ.symm q).2) χ.target :=
    contMDiff_riemannianExp.comp_contMDiffOn hχ
  have hS : IsOpen S :=
    hE.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_target z) (isOpen_extChartAt_source _)
  have hzS : χ z ∈ S := ⟨hχz,by change riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2 ∈ d.source; rw [hχinv]; exact mem_extChartAt_source _⟩
  have hd : ContMDiffOn 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d d.source := by
    simpa only [d,extChartAt_source] using (contMDiffOn_extChartAt (I := 𝓘(ℝ,Model n)) (n := ∞) (x := riemannianExp z.1 z.2))
  have hf : ContDiffOn ℝ ∞ f S :=
    (hd.comp (hE.mono (inter_subset_left)) (fun _ hq => hq.2)).contDiffOn
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) z.1
  let L : TangentSpace 𝓘(ℝ,Model n) z.1 ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ z.1 (mem_baseSet_trivializationAt (Model n) _ z.1)
  have hχsecond : (χ z).2=L z.2 := rfl
  have hχfiber (w : Model n) : χ.symm ((χ z).1,w) =
      (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    have hforward : χ (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) = ((χ z).1,w) := by
      apply Prod.ext
      · rfl
      · change L (L.symm w)=w
        exact L.apply_symm_apply w
    rw [←hforward]
    apply χ.left_inv
    exact (tangent_chart_source_iff z _).mpr (mem_extChartAt_source z.1)
  let F : TangentSpace 𝓘(ℝ,Model n) z.1 → Model n :=
    fun v => d (riemannianExp z.1 v)
  have hF : ContDiffAt ℝ ∞ F z.2 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) from
      contMDiffAt_extChartAt).comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hFi : Function.Injective (fderiv ℝ F z.2) := riemannianExp_interior_nonconjugate hz
  have hpart : (fun w => f ((χ z).1,w)) = F ∘ L.symm := by
    funext w
    dsimp [f]
    rw [hχfiber]
  have hpartder : fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2 =
      (fderiv ℝ F z.2).comp (L.symm : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1) := by
    rw [hpart,hχsecond]
    have hF' : HasFDerivAt F (fderiv ℝ F z.2) (L.symm (L z.2)) := by
      simpa only [L.symm_apply_apply] using (hF.differentiableAt (by simp)).hasFDerivAt
    exact (hF'.comp (L z.2) L.symm.hasFDerivAt).fderiv
  have hpi : (fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2).IsInvertible := by
    have hi : Function.Injective (fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2) := by
      rw [hpartder]
      exact hFi.comp L.symm.injective
    have hs := LinearMap.injective_iff_surjective.mp hi
    exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hi)
      (LinearMap.range_eq_top.mpr hs),rfl⟩
  have hi := first_coordinate_preserving_derivative_invertible
    ((hf.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by simp)) hpi
  obtain ⟨e,he,hz',heS,heD,heInv⟩ := exists_smooth_local_diffeomorphism hS
    (contDiffOn_fst.prodMk hf) hzS hi
  exact ⟨e,he,hz',fun _ hq => (heS hq).1,fun _ hq => (heS hq).2,heD,heInv⟩

end WeakMTWTransport

end

end OAI
