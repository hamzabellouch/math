import OAI.Geometry.KahlerSplitting.ProductRetracts

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ,F) ∞ N]

lemma holomorphic_local_chart_of_bijective {f : M → N}
    (hf : MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) f) {p : M}
    (hbij : Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f p)) :
    ∃ e : OpenPartialHomeomorph M N, p ∈ e.source ∧ EqOn e f e.source ∧
      e.MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) := by
  let c := chartAt E p
  let d := chartAt F (f p)
  have hc : c.MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,E) := mdifferentiable_chart p
  have hd : d.MDifferentiable 𝓘(ℂ,F) 𝓘(ℂ,F) := mdifferentiable_chart (f p)
  have hpc : p ∈ c.source := mem_chart_source E p
  have hpd : f p ∈ d.source := mem_chart_source F (f p)
  let U : Set E := c.target ∩ (f ∘ c.symm) ⁻¹' d.source
  have hUc : IsOpen U := (hf.continuous.comp_continuousOn c.symm.continuousOn).isOpen_inter_preimage
    c.open_target d.open_source
  have hpU : c p ∈ U := ⟨c.map_source hpc,by change f (c.symm (c p)) ∈ d.source; rw [c.left_inv hpc]; exact hpd⟩
  let H : E → F := d ∘ f ∘ c.symm
  have hH : DifferentiableOn ℂ H U := mdifferentiableOn_iff_differentiableOn.mp
    (hd.1.comp ((hf.mdifferentiableOn (s := univ)).comp (hc.2.mono inter_subset_left) (fun _ _ ↦ mem_univ _))
      (fun _ hz ↦ hz.2))
  have hD : Function.Bijective (fderiv ℂ H (c p)) := by
    have hci := hc.mdifferentiableAt_symm (c.map_source hpc)
    have hfp := hf p
    have hdp := hd.mdifferentiableAt hpd
    have hcomp := mfderiv_comp (I := 𝓘(ℂ,E)) (I' := 𝓘(ℂ,E)) (I'' := 𝓘(ℂ,F))
      (c p) (by simpa only [c.left_inv hpc] using hfp) hci
    have hfp' : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,F) f (c.symm (c p)) := by
      simpa only [c.left_inv hpc] using hfp
    have hfc : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,F) (f ∘ c.symm) (c p) := hfp'.comp (c p) hci
    have hdp' : MDifferentiableAt 𝓘(ℂ,F) 𝓘(ℂ,F) d ((f ∘ c.symm) (c p)) := by
      simpa only [Function.comp_apply,c.left_inv hpc] using hdp
    have hcomp2 := mfderiv_comp (I := 𝓘(ℂ,E)) (I' := 𝓘(ℂ,F)) (I'' := 𝓘(ℂ,F))
      (c p) hdp' hfc
    rw [mfderiv_eq_fderiv] at hcomp2
    change fderiv ℂ H (c p)=_ at hcomp2
    rw [hcomp2,hcomp]
    have hbij' : Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f (c.symm (c p))) := by
      rw [c.left_inv hpc]
      exact hbij
    have hpd' : f (c.symm (c p)) ∈ d.source := by rwa [c.left_inv hpc]
    exact (hd.mfderiv_bijective hpd').comp (hbij'.comp (hc.symm.mfderiv_bijective (c.map_source hpc)))
  let L : E ≃L[ℂ] F := (LinearEquiv.ofBijective (fderiv ℂ H (c p)).toLinearMap hD).toContinuousLinearEquiv
  have hL : HasFDerivAt H (L : E →L[ℂ] F) (c p) := (hH.differentiableAt (hUc.mem_nhds hpU)).hasFDerivAt
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨b,hb,hpb,hbU,hbd,hbdi⟩ := exists_holomorphic_ift_chart hUc
    (finite_holomorphic_contDiffOn_one hUc hH) hpU L hL
  have hbM : b.MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) :=
    ⟨mdifferentiableOn_iff_differentiableOn.mpr (hbd.differentiableOn (by norm_num)),
      mdifferentiableOn_iff_differentiableOn.mpr (hbdi.differentiableOn (by norm_num))⟩
  let e := (c.trans b).trans d.symm
  have heq (x : M) (hx : x ∈ e.source) : e x=f x := by
    change d.symm (b (c x))=f x
    rw [hb]
    change d.symm (d (f (c.symm (c x))))=f x
    rw [c.left_inv hx.1.1]
    have hh : f x ∈ d.source := by
      have h := (hbU hx.1.2).2
      change f (c.symm (c x)) ∈ d.source at h
      rwa [c.left_inv hx.1.1] at h
    exact d.left_inv hh
  have hpe : p ∈ e.source := by
    refine ⟨⟨hpc,hpb⟩,?_⟩
    change b (c p) ∈ d.target
    rw [hb]
    change d (f (c.symm (c p))) ∈ d.target
    rw [c.left_inv hpc]
    exact d.map_source hpd
  exact ⟨e,hpe,heq,(hc.trans hbM).trans hd.symm⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace ProductRetracts
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

lemma pair_derivative_bijective (z : Z.Carrier) :
    Function.Bijective (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z) := by
  obtain ⟨e,hz,_⟩ := exists_coverProductChart π S h₁ h₂ z
  have heDiff : e.chart.MDifferentiable (model n) 𝓘(ℂ,Model r × Model s) :=
    ⟨e.holomorphic,e.inverse_holomorphic⟩
  have hd := mfderiv_prodMk (P.q₁_holomorphic g z) (P.q₂_holomorphic g z)
  change mfderiv (model n) ((model r).prod (model s)) (P.pair g) z = _ at hd
  have hinj : Function.Injective (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    rw [hd] at hv
    have hv₁ := congrArg Prod.fst hv
    have hv₂ := congrArg Prod.snd hv
    have he₁ := (e.factor_kernel (P.q₁_holomorphic g) (P.q₁_factor g e) hz
      (P.q₁_submersion g z) v).mp hv₁
    have he₂ := (e.swap.factor_kernel (P.q₂_holomorphic g) (P.q₂_factor g e)
      hz (P.q₂_submersion g z) v).mp hv₂
    rw [e.swap_derivative hz v] at he₂
    have he : mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v=0 := Prod.ext he₁ he₂
    exact heDiff.mfderiv_injective hz
      (he.trans (map_zero _).symm)
  refine ⟨hinj,?_⟩
  have hb := heDiff.mfderiv_bijective hz
  have hfin : Module.finrank ℂ (Model n)=Module.finrank ℂ (Model r × Model s) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective
      (show Model n →ₗ[ℂ] (Model r × Model s) from (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z).toLinearMap) hb)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (show Model n →ₗ[ℂ] (Model r × Model s) from
      (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z).toLinearMap))).mp hinj

lemma pair_local_chart (z : Z.Carrier) :
    ∃ e : OpenPartialHomeomorph Z.Carrier (P.Y₁.Carrier × P.Y₂.Carrier),
      z ∈ e.source ∧ EqOn e (P.pair g) e.source ∧
      e.MDifferentiable (model n) ((model r).prod (model s)) := by
  let : ChartedSpace (Model r × Model s) (P.Y₁.Carrier × P.Y₂.Carrier) :=
    prodChartedSpace (Model r) P.Y₁.Carrier (Model s) P.Y₂.Carrier
  have hmodel : (model r).prod (model s)=𝓘(ℂ,Model r × Model s) := modelWithCornersSelf_prod.symm
  let : IsManifold 𝓘(ℂ,Model r × Model s) ∞ (P.Y₁.Carrier × P.Y₂.Carrier) := by
    rw [←hmodel]
    exact IsManifold.prod (I := model r) (I' := model s) P.Y₁.Carrier P.Y₂.Carrier
  have hf : MDifferentiable (model n) 𝓘(ℂ,Model r × Model s) (P.pair g) := by
    rw [←hmodel]; exact P.pair_holomorphic g
  have hb : Function.Bijective (mfderiv (model n) 𝓘(ℂ,Model r × Model s) (P.pair g) z) := by
    rw [←hmodel]; exact P.pair_derivative_bijective g z
  obtain ⟨e,he,heq,hd⟩ := holomorphic_local_chart_of_bijective hf hb
  exact ⟨e,he,heq,by rw [hmodel]; exact hd⟩

lemma pair_isLocalHomeomorph : IsLocalHomeomorph (P.pair g) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro z
  obtain ⟨e,he,heq,_⟩ := P.pair_local_chart g z
  refine ⟨e.source,e.open_source.mem_nhds he,?_⟩
  have h : e.source.domRestrict (P.pair g)=e.source.domRestrict e := funext (fun x ↦ (heq x.property).symm)
  rw [h]
  exact e.isOpenEmbedding_restrict

end ProductRetracts
end UniversalCoverSplitting
end
end

end OAI
