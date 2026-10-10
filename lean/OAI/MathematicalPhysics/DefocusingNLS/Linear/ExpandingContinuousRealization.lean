import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredLimit

namespace OAI

/-! # Joint continuity of the actual physical ball observation -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

noncomputable def expandingTorusRealization (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    FourierL2 →L[ℂ] C(SchrodingerTorus, ℂ) :=
  LinearMap.mkContinuous
    { toFun := expandingTorusFunction a k L
      map_add' := by
        intro f g
        ext x
        simp only [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_add,
          ContinuousMap.add_apply]
      map_smul' := by
        intro c f
        ext x
        simp only [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_smul,
          ContinuousMap.smul_apply, RingHom.id_apply] }
    (expandingEmbeddingBound a k) (expandingTorusFunction_norm_le a k L ha ha1 hk hL)

theorem continuous_expandingPhysical_observation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (fun p : (Radius × FourierL2) × E =>
      expandingTorusFunction a k p.1.1.1 p.1.2
        (euclideanToTorus (p.1.1.1⁻¹ • p.2))) := by
  have hi : Continuous (fun p : (Radius × FourierL2) × E =>
      expandingInverseTransfer a k p.1.1.1 ha hk p.1.1.2 p.1.2) :=
    ((continuous_expandingInverseTransfer a k ha hk).comp
      (continuous_fst.comp continuous_fst)).clm_apply (continuous_snd.comp continuous_fst)
  have hf : Continuous (fun p : (Radius × FourierL2) × E =>
      expandingTorusFunction a k 1
        (expandingInverseTransfer a k p.1.1.1 ha hk p.1.1.2 p.1.2)) :=
    (expandingTorusRealization a k 1 ha ha1 hk le_rfl).continuous.comp hi
  have hy : Continuous (fun p : (Radius × FourierL2) × E =>
      euclideanToTorus (p.1.1.1⁻¹ • p.2)) := by
    unfold euclideanToTorus
    apply continuous_pi
    intro j
    have hR : Continuous (fun p : (Radius × FourierL2) × E => p.1.1.1⁻¹) :=
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).inv₀
        (fun p => by change p.1.1.1 ≠ 0; linarith [p.1.1.2])
    have hY : Continuous (fun p : (Radius × FourierL2) × E => p.2 j) := by fun_prop
    exact (AddCircle.continuous_mk' (2 * Real.pi)).comp (hR.mul hY)
  have he := continuous_eval.comp (hf.prodMk hy)
  simpa only [Function.comp_def, expandingInverseTransfer_function a k _ ha ha1 hk] using he

theorem continuous_expandingPhysicalBall (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (fun p : Radius × FourierL2 =>
      expandingPhysicalBall a k p.1.1 R ha ha1 hk p.1.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry _
  have hm : Continuous (fun p : (Radius × FourierL2) × Metric.closedBall (0 : E) R =>
      (p.1, (p.2 : E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h := (continuous_expandingPhysical_observation a k ha ha1 hk).comp hm
  simpa only [Function.uncurry_def, Function.comp_def, expandingPhysicalBall_apply] using h

end DefocusingNLS

end OAI
