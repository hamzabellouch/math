import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModelData
import OAI.Analysis.CircleDomains.Uniformization.LocalInverseConvergence
import OAI.Analysis.CircleDomains.Topology.ProjectionJordanCap
import OAI.Analysis.CircleDomains.Topology.FinitePlaneEmbedding

namespace OAI

/-! The actual continuous projections of finite scalar models converge
to the inverse on the limiting conformal image. This also transports
uniformly convergent source tests to their actual model continuations. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem CompactScalarCircleModel.projection_finite
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (M : CompactScalarCircleModel G u) (hinf : OnePoint.infty ∈ G) (z : ℂ) :
    M.projection (z : Sphere) ≠ OnePoint.infty := by
  intro h
  have he := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf).mp h
  exact OnePoint.coe_ne_infty z (he.trans (extendAtInfinity_infty M.function))

 theorem scalar_model_projection_tendsto
    (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G)
    {m : ℕ → ℕ} {u : (n : ℕ) → Fin (m n) → EuclideanPlane → ℝ}
    (M : (n : ℕ) → CompactScalarCircleModel G (u n))
    {F : ℂ → ℂ} (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M n).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    {z : ℂ} (hz : (z : Sphere) ∈ G) :
    Tendsto (fun n => (M n).projection (F z : Sphere)) atTop (𝓝 (z : Sphere)) := by
  have hV := hF.1.isOpen_image hG hG (Subset.refl G)
  obtain ⟨fi,hfi⟩ := hF.exists_smooth_inverse hG hV
  have hfp := hfi.finite_open_embedding hinf rfl hV
  choose gi hgi using fun n => (M n).conformal.exists_smooth_inverse hG (M n).circle.1
  have hmp (n : ℕ) := (hgi n).finite_open_embedding hinf (M n).normalized.1 (M n).circle.1
  have hi : Tendsto (fun n => finiteCoord ((M n).projection (F z : Sphere))) atTop (𝓝 z) := by
    apply inverse_tendsto_of_locally_uniform_open_embeddings hsch
      (hG.preimage OnePoint.continuous_coe)
      (by simpa only [extendAtInfinity_coe,finiteCoord_coe] using hfp.1)
      (by simpa only [extendAtInfinity_coe,finiteCoord_coe] using hfp.2.1)
      (by simpa only [extendAtInfinity_coe,finiteCoord_coe] using hfp.2.2)
      (fun _ => {z : ℂ | (z : Sphere) ∈ G})
      (fun _ => hG.preimage OnePoint.continuous_coe)
      (fun n => (M n).function) (fun n z => finiteCoord ((M n).projection (z : Sphere)))
      (fun n z hz => by
        convert (hmp n).1 z hz using 1
        · funext w; simp only [extendAtInfinity_coe,finiteCoord_coe]
        · rfl)
      (fun n S hS hSG => by
        simpa only [extendAtInfinity_coe,finiteCoord_coe] using (hmp n).2.1 S hS hSG)
      (fun n x hx y hy he => (hmp n).2.2 hx hy (by
        simpa only [extendAtInfinity_coe,finiteCoord_coe] using he))
      ?_ hlim (fun _ _ hKG => Eventually.of_forall (fun _ => hKG)) hz
    intro n x hx
    simpa only [extendAtInfinity_coe,finiteCoord_coe] using
      congrArg finiteCoord ((M n).projection_inverse (x : Sphere) hx)
  have ht := OnePoint.continuous_coe.continuousAt.tendsto.comp hi
  apply ht.congr'
  exact Eventually.of_forall (fun n => CannonMobius.coe_coordinate ((M n).projection_finite hinf (F z)))

 theorem scalar_model_continuations_tendsto
    (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G)
    {m : ℕ → ℕ} {u : (n : ℕ) → Fin (m n) → EuclideanPlane → ℝ}
    (M : (n : ℕ) → CompactScalarCircleModel G (u n))
    {F : ℂ → ℂ} (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M n).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    {a : ℕ → C(Sphere,ℝ)} {b : C(Sphere,ℝ)} (hab : Tendsto a atTop (𝓝 b))
    {z : ℂ} (hz : (z : Sphere) ∈ G) :
    Tendsto (fun n => a n ((M n).projection (F z : Sphere))) atTop (𝓝 (b (z : Sphere))) := by
  have hp := scalar_model_projection_tendsto hsch hG hinf M hF hlim hz
  exact (continuous_eval.tendsto (b,(z : Sphere))).comp (hab.prodMk_nhds hp)

end CircleDomainRigidity

end

end OAI
