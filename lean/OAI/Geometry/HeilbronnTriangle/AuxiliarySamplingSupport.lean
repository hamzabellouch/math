import OAI.Geometry.HeilbronnTriangle.AuxiliarySamplingLaw
import OAI.Geometry.HeilbronnTriangle.AuxiliaryIntegralSupport

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling

open scoped BigOperators
open LiftingProbability

namespace Law

variable {q H : ℕ} [Fact q.Prime]

theorem exists_outcome_of_weight_pos (L : Law q H) (p : Fin 3 → Fin 3 → ZMod q)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets p) :
    ∃ ω : L.Outcome, ∀ i, p i ∈ L.sets ω := by
  classical
  have hinc : 0 < inclusionMass L.weight L.sets p := by
    by_contra hn
    have hn' : inclusionMass L.weight L.sets p ≤ 0 := le_of_not_gt hn
    have hbad : auxiliaryWeight q L.size L.weight L.sets p ≤ 0 := by
      unfold auxiliaryWeight
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hn'
    exact (not_le_of_gt hpositive) hbad
  by_contra hn
  have hnone : ∀ ω : L.Outcome, ¬ (∀ i, p i ∈ L.sets ω) := by
    intro ω hω
    exact hn ⟨ω, hω⟩
  have hz : inclusionMass L.weight L.sets p = 0 := by
    unfold inclusionMass
    apply Finset.sum_eq_zero
    intro ω hω
    exact ite_eq_right (hnone ω)
  exact (ne_of_gt hinc) hz

theorem support_of_weight_pos (L : Law q H) (p : Fin 3 → Fin 3 → ZMod q)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets p) :
    (∀ i, p i ≠ 0) ∧
      (AffineIndependent (ZMod q) p ∨ ∃ i j, i ≠ j ∧ p i = p j) ∧
      (AffineIndependent (ZMod q) p → ∀ x : Fin 3 → ℤ,
        (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0) := by
  classical
  obtain ⟨ω, hω⟩ := L.exists_outcome_of_weight_pos p hpositive
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact L.zero_not_mem ω (hi ▸ hω i)
  · by_cases hinj : Function.Injective p
    · exact Or.inl (AuxiliarySet.affineIndependent_of_mem_cap (L.isCap ω) hω hinj)
    · right
      simp only [Function.Injective] at hinj
      push Not at hinj
      obtain ⟨i, j, heq, hne⟩ := hinj
      exact ⟨i, j, hne, heq⟩
  · intro hAI x hx hne
    exact L.short_relation ω p hω hAI.injective x hx hne

theorem matrix_short_kernel_excluded (L : Law q H)
    (A : Matrix (Fin 3) (Fin 3) (ZMod q))
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets A.col)
    (hAI : AffineIndependent (ZMod q) A.col)
    (x : Fin 3 → ℤ) (hx : ∀ i, |x i| ≤ (H : ℤ)) (hne : x ≠ 0) :
    A.mulVec (fun i => (x i : ZMod q)) ≠ 0 := by
  intro hrel
  have hno := (L.support_of_weight_pos A.col hpositive).2.2 hAI x hx hne
  apply hno
  funext i
  have hi := congrFun hrel i
  simpa [Matrix.mulVec, Matrix.col, dotProduct, Finset.sum_apply, mul_comm] using hi

theorem kernel_norm_gt_of_weight_pos (L : Law q H)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    (hAI : AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
    {x : PrimitiveNormal.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
    (H : ℝ) < ‖PrimitiveNormal.toEuclidean x‖ := by
  by_contra hn
  have hx := AuxiliarySet.coordinate_abs_le_of_euclidean_norm_le (le_of_not_gt hn)
  have hno := L.matrix_short_kernel_excluded (A.map (Int.castRingHom (ZMod q)))
    hpositive hAI x hx hne
  exact hno (AuxiliarySet.cast_mulVec_eq_zero hkernel)

theorem kernel_norm_gt_main_square {h : ℕ} (L : Law q (h ^ 2))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    (hAI : AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
    {x : PrimitiveNormal.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
    (h : ℝ) ^ 2 < ‖PrimitiveNormal.toEuclidean x‖ := by
  simpa only [Nat.cast_pow] using L.kernel_norm_gt_of_weight_pos A hpositive hAI hne hkernel

end Law
end Problem355.AuxiliarySampling

end

end OAI
