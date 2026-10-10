import OAI.Analysis.CircleDomains.Topology.CircleLifts

namespace OAI

/-! Continuous real branches of one circle coordinate differ locally by
a constant integer. Their ordinary derivatives therefore agree. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem circle_lift_difference_eventually_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (he : ∀ x ∈ U, (u x : UnitAddCircle) = (v x : UnitAddCircle))
    {x : E} (hx : x ∈ U) :
    (fun y => u y - v y) =ᶠ[𝓝 x] (fun _ => u x - v x) := by
  let a := u x - v x - 1 / 2
  have hmem : u x - v x ∈ Ioo a (a + 1) := by dsimp [a]; constructor <;> linarith
  have hnear := ((hu.sub hv).continuousAt (hU.mem_nhds hx)).eventually
    (isOpen_Ioo.mem_nhds hmem)
  filter_upwards [hU.mem_nhds hx, hnear] with y hy hyI
  have hmod : ((u y - v y : ℝ) : UnitAddCircle) = ((u x - v x : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_sub, he y hy, sub_self, AddCircle.coe_sub, he x hx, sub_self]
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hyI)
    (Ioo_subset_Ico_self hmem)).mp hmod

 theorem circle_lift_difference_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (he : ∀ x ∈ U, (u x : UnitAddCircle) = (v x : UnitAddCircle))
    {x : E} (hx : x ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => u y - v y) x :=
  contDiffAt_const.congr_of_eventuallyEq
    (circle_lift_difference_eventually_constant hU hu hv he hx)

 theorem circle_lift_difference_eq_on_preconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) {u v : E → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (he : ∀ x ∈ U, (u x : UnitAddCircle) = (v x : UnitAddCircle))
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) : u x - v x = u y - v y := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hconn
  have hd : IsLocallyConstant (fun z : U => u z.val - v z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.eventually
      (circle_lift_difference_eventually_constant hU hu hv he z.property)
  exact hd.apply_eq_of_preconnectedSpace (⟨x, hx⟩ : U) ⟨y, hy⟩

 theorem contDiffAt_circle_quotient_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (a : ℝ) (ha : (u x : UnitAddCircle) ≠ (a : UnitAddCircle)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => (AddCircle.equivIco (1 : ℝ) a (u y : UnitAddCircle) : ℝ)) x := by
  have hmod : ¬ u x ≡ a [PMOD (1 : ℝ)] := AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr ha
  have hconst := (eventuallyEq_toIcoDiv_nhds (by norm_num : (0 : ℝ) < 1) a hmod).comp_tendsto
    hu.continuousAt
  have heq : (fun y => (AddCircle.equivIco (1 : ℝ) a (u y : UnitAddCircle) : ℝ))
      =ᶠ[𝓝 x] (fun y => u y - (toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) : ℝ)) := by
    filter_upwards [hconst] with y hy
    change toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u y) =
      toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) at hy
    change toIcoMod (by norm_num : (0 : ℝ) < 1) a (u y) = _
    simp only [toIcoMod, hy, zsmul_eq_mul, mul_one]
  exact (hu.sub contDiffAt_const).congr_of_eventuallyEq heq

end CircleDomainRigidity

end

end OAI
