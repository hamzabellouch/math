import OAI.Analysis.PureInfiniteness.InnerHomCompression
import OAI.Analysis.Nuclearity.MatrixCPAmplification
import OAI.Analysis.WeakInfiniteness.NonUnitalClosedRange

namespace OAI

/-! Bounded completely positive maps annihilating a quotient kernel descend
with their norm bound. The matrix positivity step lifts a square root.
This does not assert that nuclear approximations already annihilate the kernel. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B D : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra D]

theorem continuousLinear_descends (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (F : A →L[ℂ] D) (hk : ∀ a, q a = 0 → F a = 0) :
    ∃ G : B →L[ℂ] D, (∀ a, G (q a) = F a) ∧ ‖G‖ ≤ ‖F‖ := by
  classical
  have hcompat (a b : A) (h : q a = q b) : F a = F b := by
    have hz : q (a - b) = 0 := by rw [map_sub, h, sub_self]
    simpa only [map_sub, sub_eq_zero] using hk (a - b) hz
  let s : B → A := fun b => Classical.choose (hq b)
  have hs (b : B) : q (s b) = b := Classical.choose_spec (hq b)
  let L : B →ₗ[ℂ] D :=
    { toFun := fun b => F (s b)
      map_add' := fun x y => by
        rw [← map_add]
        exact hcompat _ _ (by rw [map_add, hs, hs, hs])
      map_smul' := fun c x => by
        rw [← map_smul]
        exact hcompat _ _ (by rw [map_smul, hs, hs]; rfl) }
  have he (a : A) : L (q a) = F a := hcompat _ _ (hs (q a))
  have hb (b : B) : ‖L b‖ ≤ ‖F‖ * ‖b‖ := by
    by_cases hzero : b = 0
    · simp only [hzero, map_zero, norm_zero, mul_zero, le_refl]
    · obtain ⟨a, ha, han⟩ := nonUnitalStarHom_exists_lift_norm_le q.toNonUnitalStarAlgHom
        (s b) (norm_pos_iff.mpr hzero) (by change ‖q (s b)‖ ≤ ‖b‖; rw [hs])
      have hqa : q a = b := ha.trans (hs b)
      calc
        ‖L b‖ = ‖F a‖ := by rw [← hqa, he]
        _ ≤ ‖F‖ * ‖a‖ := F.le_opNorm a
        _ ≤ ‖F‖ * ‖b‖ := mul_le_mul_of_nonneg_left han (norm_nonneg F)
  let G := L.mkContinuous ‖F‖ hb
  exact ⟨G, he, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F) hb⟩

theorem matrixMap_surjective (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (n : ℕ) : Function.Surjective (CStarMatrix.mapₙₐ q.toNonUnitalStarAlgHom :
      CStarMatrix (Fin n) (Fin n) A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) B) := by
  classical
  intro M
  refine ⟨CStarMatrix.ofMatrix (fun i j => Classical.choose (hq (M i j))), ?_⟩
  ext i j
  exact Classical.choose_spec (hq (M i j))

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder D] [StarOrderedRing D]

theorem matrixMap_positive_lift (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) B) (hM : 0 ≤ M) :
    ∃ N : CStarMatrix (Fin n) (Fin n) A, 0 ≤ N ∧
      CStarMatrix.mapₙₐ q.toNonUnitalStarAlgHom N = M := by
  let : Module ℝ (CStarMatrix (Fin n) (Fin n) B) := Module.compHom _ Complex.ofRealHom
  obtain ⟨Y, hY⟩ := matrixMap_surjective q hq n (CFC.sqrt M)
  refine ⟨star Y * Y, star_mul_self_nonneg Y, ?_⟩
  rw [map_mul, map_star, hY, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self M hM]

theorem completelyPositive_descends (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (F : A →L[ℂ] D) (G : B →L[ℂ] D) (hF : CompletelyPositive F)
    (he : ∀ a, G (q a) = F a) : CompletelyPositive G := by
  intro n M hM
  change 0 ≤ matrixLinearMap G M
  obtain ⟨N, hN, hqN⟩ := matrixMap_positive_lift q hq n M hM
  have hm : matrixLinearMap G (CStarMatrix.mapₙₐ q.toNonUnitalStarAlgHom N) =
      matrixLinearMap F N := by
    ext i j
    exact he (N i j)
  rw [← hqN, hm]
  exact hF n N hN

theorem cpMap_descends (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (F : A →L[ℂ] D) (hF : CompletelyPositive F) (hk : ∀ a, q a = 0 → F a = 0) :
    ∃ G : B →L[ℂ] D, CompletelyPositive G ∧ (∀ a, G (q a) = F a) ∧ ‖G‖ ≤ ‖F‖ := by
  obtain ⟨G, he, hn⟩ := continuousLinear_descends q hq F hk
  exact ⟨G, completelyPositive_descends q hq F G hF he, he, hn⟩

end WeakPureInfiniteness

end

end OAI
