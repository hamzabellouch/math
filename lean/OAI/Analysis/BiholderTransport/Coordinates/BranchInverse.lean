import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ExpNonconjugacy

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_joint_exp_inverse_of_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
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
    (hd.comp (hE.mono (inter_subset_left)) (fun q hq => hq.2)).contDiffOn
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
  have hFi : Function.Injective (fderiv ℝ F z.2) := hz
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
  exact ⟨e,he,hz',fun q hq => (heS hq).1,fun q hq => (heS hq).2,heD,heInv⟩

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_exp_branch (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ P : M×M → TangentBundle 𝓘(ℝ,Model n) M,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P
        (z.1,riemannianExp z.1 z.2) ∧
      P (z.1,riemannianExp z.1 z.2)=z ∧
      (∀ᶠ r in 𝓝 z, P (r.1,riemannianExp r.1 r.2)=r) ∧
      (∀ᶠ q in 𝓝 (z.1,riemannianExp z.1 z.2),
        (P q).1=q.1 ∧ riemannianExp (P q).1 (P q).2=q.2) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let c := extChartAt 𝓘(ℝ,Model n) z.1
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let y : M×M := (z.1,riemannianExp z.1 z.2)
  let J : M×M → Model n × Model n := fun q => (c q.1,d q.2)
  obtain ⟨e,he,hze,_,hend,_,hei⟩ := exists_joint_exp_inverse_of_nonconjugate z hz
  have hχz := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hJy : J y = e (χ z) := by
    rw [he]
    change (c z.1,d (riemannianExp z.1 z.2)) =
      ((χ z).1,d (riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2))
    rw [hχinv]
    rfl
  have hyT : J y ∈ e.target := by
    simpa only [hJy] using e.map_source hze
  have hiy : e.symm (J y)=χ z := by rw [hJy,e.left_inv hze]
  have hJ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,Model n × Model n) ∞ J y := by
    have hc₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ c y.1 := contMDiffAt_extChartAt
    have hd₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y.2 := contMDiffAt_extChartAt
    exact (hc₀.comp y contMDiffAt_fst).prodMk_space (hd₀.comp y contMDiffAt_snd)
  have hi := (hei.contDiffAt (e.open_target.mem_nhds hyT)).contMDiffAt.comp y hJ
  have hc : ContMDiffAt 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm
      (e.symm (J y)) :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds (by simpa only [hiy] using hχz))
  let P : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => χ.symm (e.symm (J q))
  have hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P y :=
    hc.comp y hi
  have hPy : P y = z := by dsimp [P]; rw [hiy,hχinv]
  refine ⟨P,hP,hPy,?_,?_⟩
  · have hχnear : ∀ᶠ r in 𝓝 z, χ r ∈ e.source :=
      (show ContinuousAt χ z from continuousAt_extChartAt z).preimage_mem_nhds (e.open_source.mem_nhds hze)
    filter_upwards [hχnear,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z] with r hre hrs
    have hJr : J (r.1,riemannianExp r.1 r.2)=e (χ r) := by
      rw [he]
      change (c r.1,d (riemannianExp r.1 r.2)) =
        ((χ r).1,d (riemannianExp (χ.symm (χ r)).1 (χ.symm (χ r)).2))
      rw [χ.left_inv hrs]
      rfl
    dsimp only [P]
    rw [hJr,e.left_inv hre,χ.left_inv hrs]
  · have hJnear : ∀ᶠ q in 𝓝 y, J q ∈ e.target :=
      hJ.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hyT)
    have hcnear : ∀ᶠ q : M×M in 𝓝 y, q.1 ∈ c.source :=
      (continuous_fst : Continuous (fun q : M×M => q.1)).continuousAt.preimage_mem_nhds
        (show c.source ∈ 𝓝 y.1 from extChartAt_source_mem_nhds z.1)
    have hdnear : ∀ᶠ q : M×M in 𝓝 y, q.2 ∈ d.source :=
      (continuous_snd : Continuous (fun q : M×M => q.2)).continuousAt.preimage_mem_nhds
        (show d.source ∈ 𝓝 y.2 from extChartAt_source_mem_nhds (riemannianExp z.1 z.2))
    filter_upwards [hJnear,hcnear,hdnear] with q hqJ hqc hqd
    have his := e.map_target hqJ
    have hmap := e.right_inv hqJ
    rw [he] at hmap
    constructor
    · change (χ.symm (e.symm (J q))).1=q.1
      rw [tangent_chart_symm_base]
      have hf := congrArg Prod.fst hmap
      change (e.symm (J q)).1=c q.1 at hf
      rw [hf,c.left_inv hqc]
    · apply d.injOn (hend _ his) hqd
      exact congrArg Prod.snd hmap

end WeakMTWTransport

end

end OAI
