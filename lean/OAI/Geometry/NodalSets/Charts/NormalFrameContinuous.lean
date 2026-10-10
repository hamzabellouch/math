import OAI.Geometry.NodalSets.Charts.NormalFramePhase

namespace OAI

namespace Yau.Jets
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma contactEta_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) :
    Continuous (fun t ↦ Yau.contactEta (a t) (b t) (H t 0 0) (H t 1 1)) := by
  apply Continuous.div (((ha.pow 2).mul (hH 0 0)).add ((hb.pow 2).mul (hH 1 1)))
    ((ha.pow 2).add (hb.pow 2))
  intro t
  change a t ^ 2 + b t ^ 2 ≠ 0
  have h := sq_pos_of_ne_zero (ha0 t)
  nlinarith [sq_nonneg (b t)]

lemma normalRealHessian_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (i j : Fin 4) :
    Continuous (fun t ↦ normalRealHessian (a t) (b t) (H t) i j) := by
  unfold normalRealHessian
  split_ifs
  · exact (hH i j).sub (contactEta_continuous a b H ha hb hH ha0)
  · exact (hH i j).sub continuous_const

lemma normalComplexHessian_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0) (i j : Fin 4) :
    Continuous (fun t ↦ normalComplexHessian (a t) (b t) (H t) i j) := by
  have hR := normalRealHessian_continuous a b H ha hb hH ha0
  have hK : Continuous (fun t ↦ Yau.imaginaryHessian (a t) (b t)
      (normalRealHessian (a t) (b t) (H t)) i j) := by
    unfold Yau.imaginaryHessian
    split_ifs
    · exact ((hb.div ha ha0).neg).mul (hR 1 j)
    · exact (ha.div hb hb0).mul (hR 0 j)
    · exact ((hb.div ha ha0).neg).mul (hR 1 i)
    · exact (ha.div hb hb0).mul (hR 0 i)
    · exact continuous_const
  exact (Complex.continuous_ofReal.comp (hR i j)).add
    ((Complex.continuous_ofReal.comp hK).mul continuous_const)

lemma normalFrameVector_continuous (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b)
    (i : Fin 4) : Continuous (fun t ↦ normalFrameVector (a t) (b t) i) := by
  fin_cases i
  · exact Complex.continuous_ofReal.comp ha
  · exact (Complex.continuous_ofReal.comp hb).mul continuous_const
  · exact continuous_const
  · exact continuous_const

theorem normal_frame_initial_jets_continuous (a b S : T → ℝ)
    (H : T → Fin 4 → Fin 4 → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hS : Continuous S) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0) (k : ℕ) :
    ContinuousPolyFamily (fun t ↦ initialPhaseJet (S t) (normalFrameVector (a t) (b t))
      (normalComplexHessian (a t) (b t) (H t)) k) :=
  initialPhaseJet_continuous S _ _ hS (normalFrameVector_continuous a b ha hb)
    (normalComplexHessian_continuous a b H ha hb hH ha0 hb0) k

end
end Yau.Jets

end OAI
