import OAI.Analysis.CircleDomains.Topology.BoundaryArcComplement

namespace OAI

/-! Exact circle arcs for four points ordered by the fixed circle cut. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma standardCirclePoint_sub (θ φ : UnitAddCircle) :
    standardCirclePoint (θ-φ) = (standardCirclePoint φ)⁻¹ * standardCirclePoint θ := by
  simp only [standardCirclePoint,AddCircle.homeomorphCircle_apply,sub_eq_add_neg,
    AddCircle.toCircle_add,AddCircle.toCircle_neg,Circle.coe_mul,Circle.coe_inv]
  exact mul_comm _ _

lemma unitCircleCut_coe_of_mem {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    unitCircleCut (s : UnitAddCircle) = s := by
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs))

lemma alternating_boundary_rotated_arcs (θ : Fin 4 → UnitAddCircle)
    (hθ : StrictMono (unitCircleCut ∘ θ)) :
    let a := (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 2)
    let x := (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 1)
    let y := (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 3)
    ∃ ha : ‖a‖ = 1, a ≠ 1 ∧ x ∈ range (boundaryClosingArc a ha) ∧
      y ∈ Metric.sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) := by
  let t : Fin 4 → ℝ := unitCircleCut ∘ θ
  have h01 : t 0 < t 1 := hθ (by decide)
  have h12 : t 1 < t 2 := hθ (by decide)
  have h23 : t 2 < t 3 := hθ (by decide)
  have h0 : 0 ≤ t 0 := (unitCircleCut_mem (θ 0)).1
  have h3 : t 3 < 1 := (unitCircleCut_mem (θ 3)).2
  have hd (i : Fin 4) : (((t i-t 0 : ℝ) : UnitAddCircle)) = θ i-θ 0 := by
    rw [AddCircle.coe_sub]
    exact congrArg₂ (·-·) AddCircle.coe_equivIco AddCircle.coe_equivIco
  have he (i : Fin 4) : (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ i) =
      standardCirclePoint ((t i-t 0 : ℝ) : UnitAddCircle) := by
    rw [hd,standardCirclePoint_sub]
  have h2mem : t 2-t 0 ∈ Ico (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
  have hcut : unitCircleCut (normalizedArgument
      ((standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 2))) = t 2-t 0 := by
    rw [he,normalizedArgument_standardCirclePoint,unitCircleCut_coe_of_mem h2mem]
  have ha : ‖(standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 2)‖ = 1 := by
    rw [he]; exact Circle.norm_coe _
  refine ⟨ha,?_,?_,?_⟩
  · intro h
    have harg : normalizedArgument (1 : ℂ) = (0 : UnitAddCircle) := by
      rw [← standardCirclePoint_zero,normalizedArgument_standardCirclePoint]
    have hz := unitCircleCut_coe_of_mem (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
    rw [AddCircle.coe_zero] at hz
    rw [h,harg,hz] at hcut
    linarith
  · let u : PathTime := ⟨(t 1-t 0)/(t 2-t 0),⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩⟩
    refine ⟨u,?_⟩
    change standardCirclePoint ((unitCircleCut (normalizedArgument _) * (u : ℝ) : ℝ) : UnitAddCircle) = _
    rw [hcut,he]
    congr 2
    exact mul_div_cancel₀ _ (by linarith)
  · rw [← boundaryClosingArc_complement_image ha (by
      intro h
      have harg : normalizedArgument (1 : ℂ) = (0 : UnitAddCircle) := by
        rw [← standardCirclePoint_zero,normalizedArgument_standardCirclePoint]
      have hz := unitCircleCut_coe_of_mem (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
      rw [AddCircle.coe_zero] at hz
      rw [h,harg,hz] at hcut
      linarith)]
    exact ⟨t 3-t 0,⟨by rw [hcut]; linarith,by linarith⟩,(he 3).symm⟩

end CircleDomainRigidity

end

end OAI
