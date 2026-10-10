import OAI.Analysis.CircleDomains.Transfer.PeriodicFilling

namespace OAI

/-! Continuous families of circle paths have continuous real increments.
This follows from the actual homotopy lift, so no choice of a discontinuous
starting-angle representative enters the continuity or compact bounds. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_family_circle_increment
    {A : Type*} [TopologicalSpace A]
    (γ : A → C(unitInterval, UnitAddCircle)) (hγ : Continuous γ)
    (a : A → ℝ) (ha : Continuous a)
    (hproj : ∀ x, (a x : UnitAddCircle) = γ x 0) :
    Continuous (fun x => circlePathIncrement (γ x)) := by
  let H : C(unitInterval × A, UnitAddCircle) :=
    ⟨fun p => γ p.2 p.1, continuous_eval.comp ((hγ.comp continuous_snd).prodMk continuous_fst)⟩
  let L := (AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy H ⟨a, ha⟩ (fun x => (hproj x).symm)
  have he (x : A) : circlePathIncrement (γ x) = L (1, x) - a x := by
    let u : C(unitInterval, ℝ) := L.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ x))
    have hu (t : unitInterval) : (u t : UnitAddCircle) = γ x t :=
      congrFun ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy_lifts H ⟨a, ha⟩
        (fun x => (hproj x).symm)) (t, x)
    rw [circlePathIncrement_eq_lift (γ x) u hu]
    change L (1, x) - L (0, x) = _
    rw [show L (0, x) = a x from
      (AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy_zero H ⟨a, ha⟩ (fun x => (hproj x).symm) x]
  exact ((L.continuous.comp (continuous_const.prodMk continuous_id)).sub ha).congr
    (fun x => (he x).symm)

theorem continuous_circlePathIncrement :
    Continuous (circlePathIncrement : C(unitInterval, UnitAddCircle) → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro γ
  let a := circleCut (fun δ : C(unitInterval, UnitAddCircle) => δ 0) γ
  let O : Set C(unitInterval, UnitAddCircle) := {δ | δ 0 ≠ (a : UnitAddCircle)}
  have hO : IsOpen O := isClosed_singleton.isOpen_compl.preimage (continuous_eval_const 0)
  have hγ : γ ∈ O := circleCut_ne (fun δ : C(unitInterval, UnitAddCircle) => δ 0) γ
  let u : O → ℝ := fun δ => (AddCircle.equivIco (1 : ℝ) a (δ.val 0)).val
  have hu : Continuous u := by
    apply continuous_iff_continuousAt.mpr
    intro δ
    have heval : ContinuousAt (fun ε : O => ε.val (0 : unitInterval)) δ :=
      ((continuous_eval_const (0 : unitInterval)).comp continuous_subtype_val).continuousAt
    have hchart : ContinuousAt
        (fun ε : O => AddCircle.equivIco (1 : ℝ) a (ε.val 0)) δ :=
      (AddCircle.continuousAt_equivIco (1 : ℝ) a δ.property).comp
        (f := fun ε : O => ε.val 0) heval
    exact continuous_subtype_val.continuousAt.comp hchart
  have hloc : ContinuousOn circlePathIncrement O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_family_circle_increment (fun δ : O => δ.val) continuous_subtype_val u hu
      (fun _ => AddCircle.coe_equivIco)
  exact hloc.continuousAt (hO.mem_nhds hγ)

theorem compact_circle_increment_bounded
    (K : Set C(unitInterval, UnitAddCircle)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ γ ∈ K, |circlePathIncrement γ| ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image continuous_circlePathIncrement).isBounded.exists_norm_le
  exact ⟨M, fun γ hγ => by simpa only [Real.norm_eq_abs] using hM _ (mem_image_of_mem _ hγ)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
