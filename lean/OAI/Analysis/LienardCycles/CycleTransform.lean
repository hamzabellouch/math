import OAI.Analysis.LienardCycles.CaseOne

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard
noncomputable def flipY : Plane ≃ₜ Plane where
  toFun p := (p.1,-p.2)
  invFun p := (p.1,-p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk continuous_snd.neg
  continuous_invFun := continuous_fst.prodMk continuous_snd.neg
@[simp] lemma flipY_apply (p : Plane) : flipY p=(p.1,-p.2) := rfl
@[simp] lemma flipY_symm : flipY.symm=flipY := rfl
lemma IsPeriodicOrbit.flipY {F : Polynomial ℝ} {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    IsPeriodicOrbit (-F) (QuinticLienard.flipY '' C) := by
  obtain ⟨z,T,hz,hT,hp,hn,rfl⟩ := hC
  refine ⟨reverseY z,T,hz.reverseY,hT,reverseY_periodic hp,reverseY_nonconstant hn,?_⟩
  ext p
  constructor
  · rintro ⟨q,⟨t,rfl⟩,rfl⟩
    exact ⟨-t,by simp [reverseY]⟩
  · rintro ⟨t,rfl⟩
    exact ⟨z (-t),mem_range_self _,rfl⟩
lemma IsLimitCycle.map_homeomorph {F G : Polynomial ℝ} (e : Plane ≃ₜ Plane)
    (he : ∀ C,IsPeriodicOrbit F C → IsPeriodicOrbit G (e '' C))
    (he' : ∀ C,IsPeriodicOrbit G C → IsPeriodicOrbit F (e.symm '' C))
    {C : Set Plane} (hC : IsLimitCycle F C) : IsLimitCycle G (e '' C) := by
  obtain ⟨U,hU,hCU,hiso⟩ := hC.2
  refine ⟨he C hC.1,e '' U,e.isOpenMap U hU,image_mono hCU,?_⟩
  intro D hD hDU
  have hi : e.symm '' D ⊆ U := by
    rintro p ⟨q,hq,rfl⟩
    obtain ⟨v,hv,hvq⟩ := hDU hq
    simpa only [←hvq,e.symm_apply_apply] using hv
  have H := congrArg (fun S=>e '' S) (hiso _ (he' D hD) hi)
  simpa only [image_image,Function.comp_def,e.apply_symm_apply,image_id'] using H
lemma IsLimitCycle.flipY {F : Polynomial ℝ} {C : Set Plane} (hC : IsLimitCycle F C) :
    IsLimitCycle (-F) (QuinticLienard.flipY '' C) := by
  apply hC.map_homeomorph QuinticLienard.flipY (fun _ h=>h.flipY)
  intro D hD
  simpa only [flipY_symm,neg_neg] using hD.flipY
lemma limitCycle_encard_neg (F : Polynomial ℝ) :
    {C : Set Plane | IsLimitCycle F C}.encard={C : Set Plane | IsLimitCycle (-F) C}.encard := by
  have h (G : Polynomial ℝ) : {C : Set Plane | IsLimitCycle G C}.encard≤{C : Set Plane | IsLimitCycle (-G) C}.encard := by
    apply encard_le_encard_of_injOn (f:=fun C=>flipY '' C) (fun _ h=>h.flipY)
    exact (Set.image_injective.mpr flipY.injective).injOn
  exact le_antisymm (h F) (by simpa only [neg_neg] using h (-F))
end QuinticLienard

end OAI
