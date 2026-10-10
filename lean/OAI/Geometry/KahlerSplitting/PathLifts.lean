import OAI.Geometry.KahlerSplitting.ProductLocal

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

lemma cover_path_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α β : I → Z.Carrier} (hcα : Continuous α) (hcβ : Continuous β)
    (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α))
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β))
    (hbase : α 0=β 0) :
    ∃ L : C(I × I,Z.Carrier),
      ProductBoxTopology.IsBox (splittingAtlas S) (π.projection ∘ L) ∧
      (∀ t, L (t,0)=α t) ∧ (∀ t, L (0,t)=β t) := by
  obtain ⟨R,hR,ha,hb⟩ := path_axes g h₁ h₂ hα hβ (congrArg π.projection hbase)
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨L,⟨hL0,hLb⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts
    ⟨R,hR.1⟩ (0,0) (α 0) (ha 0).symm
  have hA : (fun t : I ↦ L (t,0))=α := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (L.continuous.comp (continuous_id.prodMk continuous_const)) hcα ?_ 0 hL0
    ext t
    exact (congrFun hLb (t,0)).trans (ha t)
  have hB : (fun t : I ↦ L (0,t))=β := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (L.continuous.comp (continuous_const.prodMk continuous_id)) hcβ ?_ 0 (hL0.trans hbase)
    ext t
    exact (congrFun hLb (0,t)).trans (hb t)
  exact ⟨L,by rw [hLb]; exact hR,congrFun hA,congrFun hB⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    {A : Type*} [TopologicalSpace A]

lemma GlobalProjection.fixed_path_horizontal [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) {α : A → Z.Carrier} (hc : Continuous α)
    (hfix : ∀ t, Q.toFun (α t)=α t) :
    ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α) := by
  refine ⟨π.covering.continuous.comp hc,?_⟩
  rintro _ ⟨e,rfl⟩
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t
  have ht : π.projection (α t.val) ∈ e.chart.source := t.property
  have hloc := Q.image_local g (α t.val) e (by rwa [hfix])
  rw [hfix] at hloc
  have hct : Continuous (fun u : {u : A // (π.projection ∘ α) u ∈ e.chart.source} ↦ α u.val) :=
    hc.comp continuous_subtype_val
  have hb : (e.chart (π.projection (α t.val))).2 ∈ ball 0 e.radius := by
    have H := e.chart.map_source ht
    rw [e.product_range] at H
    exact H.2
  filter_upwards [hct.continuousAt.preimage_mem_nhds hloc] with u hu
  change π.projection (Q.toFun (α u.val))=
    e.firstProjection (e.chart (π.projection (α t.val))).2 (π.projection (α u.val)) at hu
  rw [hfix] at hu
  have hh := congrArg (fun x ↦ (e.chart x).2) hu
  have huE : π.projection (α u.val) ∈ e.chart.source := u.property
  rw [e.firstProjection_coordinates hb huE] at hh
  exact hh

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.horizontal_lift [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) {α : I → Z.Carrier}
    (hcα : Continuous α) (hfix : ∀ t, Q.toFun (α t)=α t) (hα0 : α 0=Q.toFun z) :
    ∃ A : C(I,Z.Carrier), A 0=z ∧
      ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ A) ∧
      ∀ t, Q.toFun (A t)=α t := by
  obtain ⟨β,hβ0,hβ1,hβ⟩ := Q.vertical_reach g z
  obtain ⟨L,hL,ha,hb⟩ := cover_path_axes g h₁ h₂ hcα β.continuous
    (Q.fixed_path_horizontal g hcα hfix) hβ (hα0.trans hβ0.symm)
  let A : C(I,Z.Carrier) := ⟨fun t ↦ L (t,1),L.continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨A,(hb 1).trans hβ1,hL.horizontal 1,?_⟩
  intro t
  have H := Q.vertical_constant (L.continuous.comp (continuous_const.prodMk continuous_id)) (hL.vertical t) 1
  change Q.toFun (L (t,1))=Q.toFun (L (t,0)) at H
  exact H.trans ((congrArg Q.toFun (ha t)).trans (hfix t))

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace ProductRetracts
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

lemma pair_path_lift (z : Z.Carrier) (γ : C(I,P.Y₁.Carrier × P.Y₂.Carrier))
    (hγ : γ 0=P.pair g z) :
    ∃ L : C(I,Z.Carrier), L 0=z ∧ P.pair g ∘ L=γ := by
  have hα0 : (γ 0).1.val=P.first.toFun z := congrArg (fun y : P.Y₁.Carrier × P.Y₂.Carrier ↦ y.1.val) hγ
  have hβ0 : (γ 0).2.val=P.second.toFun z := congrArg (fun y : P.Y₁.Carrier × P.Y₂.Carrier ↦ y.2.val) hγ
  obtain ⟨A,hA0,hA,hAeq⟩ := P.first.horizontal_lift g z
    (continuous_subtype_val.comp γ.continuous.fst) (fun t ↦ (γ t).1.property) hα0
  obtain ⟨B,hB0,hB,hBeq⟩ := P.second.horizontal_lift g z
    (continuous_subtype_val.comp γ.continuous.snd) (fun t ↦ (γ t).2.property) hβ0
  obtain ⟨R,hR,ha,hb⟩ := cover_path_axes g h₁ h₂ A.continuous B.continuous hA
    (vertical_of_horizontal_swap hB) (hA0.trans hB0.symm)
  let L : C(I,Z.Carrier) := ⟨fun t ↦ R (t,t),R.continuous.comp (continuous_id.prodMk continuous_id)⟩
  refine ⟨L,(ha 0).trans hA0,?_⟩
  funext t
  apply Prod.ext
  · apply Subtype.ext
    have H := P.first.vertical_constant (R.continuous.comp (continuous_const.prodMk continuous_id))
      (hR.vertical t) t
    change P.first.toFun (R (t,t))=P.first.toFun (R (t,0)) at H
    exact H.trans ((congrArg P.first.toFun (ha t)).trans (hAeq t))
  · apply Subtype.ext
    have H := P.second.vertical_constant (R.continuous.comp (continuous_id.prodMk continuous_const))
      (vertical_swap_of_horizontal (hR.horizontal t)) t
    change P.second.toFun (R (t,t))=P.second.toFun (R (0,t)) at H
    exact H.trans ((congrArg P.second.toFun (hb t)).trans (hBeq t))

end ProductRetracts
end UniversalCoverSplitting
end
end

section

noncomputable section
namespace UniversalCoverSplitting
lemma simplyConnected_product {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [SimplyConnectedSpace A] [SimplyConnectedSpace B] : SimplyConnectedSpace (A × B) := by
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance,?_⟩
  intro x y p₁ p₂
  obtain ⟨H₁⟩ := SimplyConnectedSpace.paths_homotopic (p₁.map continuous_fst) (p₂.map continuous_fst)
  obtain ⟨H₂⟩ := SimplyConnectedSpace.paths_homotopic (p₁.map continuous_snd) (p₂.map continuous_snd)
  refine ⟨{ toFun := fun z ↦ (H₁ z,H₂ z)
            continuous_toFun := H₁.continuous.prodMk H₂.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact Prod.ext (H₁.map_zero_left t) (H₂.map_zero_left t)
  · intro t
    exact Prod.ext (H₁.map_one_left t) (H₂.map_one_left t)
  · intro t u hu
    exact Prod.ext (H₁.eq_fst t hu) (H₂.eq_fst t hu)
end UniversalCoverSplitting
end
end

end OAI
