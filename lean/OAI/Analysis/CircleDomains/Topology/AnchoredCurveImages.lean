import OAI.Analysis.CircleDomains.Topology.RetainedCurveImage
import OAI.Analysis.CircleDomains.Topology.RetainedJordanConvergence

namespace OAI

/-! Every fixed source contour has compatible image interiors along a
locally uniformly convergent sequence of normalized conformal maps. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_anchored_curve_images (hsch : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G)
    (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hf : ∀ n, IsConformalEquivalence (extendAtInfinity (f n)) G (extendAtInfinity (f n) '' G))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn f F atTop {z : ℂ | (z : Sphere) ∈ G})
    (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (hγ : Continuous γ) (hγi : Injective γ)
    (hfront : range γ = frontier (jordanInterior H))
    (hγG : ∀ t, (γ t : Sphere) ∈ G) :
    ∃ (J : ℂ ≃ₜ ℂ) (Jn : ℕ → ℂ ≃ₜ ℂ) (q : ℂ),
      (q : Sphere) ∈ G ∧ F q ∈ jordanInterior J ∧
      Continuous (F ∘ γ) ∧ range (F ∘ γ) = frontier (jordanInterior J) ∧
      (∀ n, range (f n ∘ γ) = frontier (jordanInterior (Jn n))) ∧
      TendstoUniformly (fun n => f n ∘ γ) (F ∘ γ) atTop ∧
      Tendsto (fun n => f n q) atTop (𝓝 (F q)) ∧
      (∀ n, f n q ∈ jordanInterior (Jn n)) ∧
      extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
        extendAtInfinity F '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  have hinj (g : ℂ → ℂ)
      (hg : IsConformalEquivalence (extendAtInfinity g) G (extendAtInfinity g '' G)) :
      InjOn (extendAtInfinity g) G := by
    obtain ⟨_,_,gi,_,_,hl,_⟩ := hg
    intro x hx y hy he
    simpa only [hl x hx,hl y hy] using congrArg gi he
  have himg (g : ℂ → ℂ)
      (hg : IsConformalEquivalence (extendAtInfinity g) G (extendAtInfinity g '' G)) :=
    exists_retained_curve_image hsch hG hconn hinf
      (fun p hp => (hg.1 p hp).1.continuousWithinAt)
      (fun U hU hUG => hg.1.isOpen_image hG hU hUG) (hinj g hg) (by rfl)
      H γ hγ hγi hfront hγG
  obtain ⟨J,hJc,hJfront,hJbd,hJside⟩ := himg F hF
  choose Jn hJnc hJnfront hJnbd hJnside using fun n => himg (f n) (hf n)
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨t,rfl⟩ := hfront.symm ▸ hz
    exact hγG t
  obtain ⟨q,hqG,hqH⟩ := exists_domain_point_inside_jordan hG H hbd
  have hinside (g : ℂ → ℂ) (K : ℂ ≃ₜ ℂ)
      (hside : extendAtInfinity g '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
        extendAtInfinity g '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior K)) :
      g q ∈ jordanInterior K := by
    have h := mem_image_of_mem (extendAtInfinity g) (show (q : Sphere) ∈
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) from ⟨hqG,q,hqH,rfl⟩)
    rw [hside] at h
    simpa only [extendAtInfinity_coe,OnePoint.coe_injective.mem_set_image] using h.2
  refine ⟨J,Jn,q,hqG,hinside F J hJside,?_,?_,?_,?_,hlim.tendsto_at hqG,
    fun n => hinside (f n) (Jn n) (hJnside n),hJside⟩
  · simpa only [extendAtInfinity_coe,finiteCoord_coe,Function.comp_def] using hJc
  · simpa only [extendAtInfinity_coe,finiteCoord_coe,Function.comp_def] using hJfront
  · intro n
    simpa only [extendAtInfinity_coe,finiteCoord_coe,Function.comp_def] using hJnfront n
  · apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp γ (fun t _ => hγG t) hγ.continuousOn

end CircleDomainRigidity

end

end OAI
