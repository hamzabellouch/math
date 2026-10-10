import OAI.Analysis.CircleDomains.Topology.RoundCollarLifts

namespace OAI

/-! One jointly continuous real lift on the unwrapped annulus gives the
same finite period on every small concentric circle. The period need not
be specified as an additional hypothesis for removing offsets. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem continuous_unitCircleParam_family (c : ℂ) (r : ℝ) :
    Continuous (fun p : ℝ × ℝ => unitCircleParam c (r + p.1) p.2) := by
  unfold unitCircleParam circleMap
  fun_prop

 theorem exists_constant_period_round_collars
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : ContinuousOn u O)
    (c : ℂ) (r : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ ρ ∈ Ioo (0 : ℝ) δ, ∀ t, unitCircleParam c (r + ρ) t ∈ O) :
    ∃ (v : ℝ → ℝ → ℝ) (k : ℝ), ∀ ρ ∈ Ioo (0 : ℝ) δ,
      Continuous (v ρ) ∧
      (∀ t, (v ρ t : UnitAddCircle) = u (unitCircleParam c (r + ρ) t)) ∧
      v ρ 1 - v ρ 0 = k := by
  let D : Set (ℝ × ℝ) := Ioo 0 δ ×ˢ univ
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_univ
  have hmid : δ / 2 ∈ Ioo (0 : ℝ) δ := ⟨half_pos hδ, half_lt_self hδ⟩
  let : ContractibleSpace D :=
    ((convex_Ioo (0 : ℝ) δ).prod convex_univ).contractibleSpace ⟨(δ / 2, 0), hmid, mem_univ _⟩
  let : LocallyPathConnectedSpace D := hD.locallyPathConnectedSpace
  let F : ℝ × ℝ → UnitAddCircle := fun p => u (unitCircleParam c (r + p.1) p.2)
  have hF : ContinuousOn F D := hu.comp (continuous_unitCircleParam_family c r).continuousOn
    (fun p hp => hc p.1 hp.1 p.2)
  obtain ⟨v, hv, _, hp⟩ := exists_continuous_circle_lift F hF
    (show (δ / 2, 0) ∈ D from ⟨hmid, mem_univ _⟩)
    (circleRepresentative (F (δ / 2, 0))) (coe_circleRepresentative _)
  let A := Ioo (0 : ℝ) δ
  let : PreconnectedSpace A := Subtype.preconnectedSpace (convex_Ioo (0 : ℝ) δ).isPreconnected
  let v₀ : A → ℝ := fun ρ => v (ρ, 0)
  let v₁ : A → ℝ := fun ρ => v (ρ, 1)
  have hv₀ : Continuous v₀ := hv.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun ρ => ⟨ρ.property, mem_univ _⟩)
  have hv₁ : Continuous v₁ := hv.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun ρ => ⟨ρ.property, mem_univ _⟩)
  have hperiod := isLocallyConstant_real_lift_difference hv₁ hv₀ (fun ρ => by
    rw [hp (ρ, 1) ⟨ρ.property, mem_univ _⟩, hp (ρ, 0) ⟨ρ.property, mem_univ _⟩]
    exact congrArg u (unitCircleParam_one_eq_zero c (r + ρ)))
  refine ⟨fun ρ t => v (ρ, t), v₁ ⟨δ / 2, hmid⟩ - v₀ ⟨δ / 2, hmid⟩, ?_⟩
  intro ρ hρ
  refine ⟨hv.comp_continuous (continuous_const.prodMk continuous_id)
    (fun t => ⟨hρ, mem_univ t⟩), fun t => hp (ρ, t) ⟨hρ, mem_univ _⟩, ?_⟩
  exact hperiod.apply_eq_of_preconnectedSpace ⟨ρ, hρ⟩ ⟨δ / 2, hmid⟩

end CircleDomainRigidity

end

end OAI
