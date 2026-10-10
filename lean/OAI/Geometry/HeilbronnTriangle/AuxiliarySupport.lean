import OAI.Geometry.HeilbronnTriangle.AuxiliarySet

namespace OAI


namespace Problem355.AuxiliarySet

open scoped BigOperators

theorem exists_outcome_of_inclusion_sum_pos
    {Θ : Type*} (T : Finset Θ) (μ : Θ → ℝ) (P : Θ → Prop)
    [DecidablePred P] (hpositive : 0 < ∑ θ ∈ T, if P θ then μ θ else 0) :
    ∃ θ ∈ T, P θ := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : (∑ θ ∈ T, if P θ then μ θ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro θ hθ
    simp [hnone θ hθ]
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

theorem matrix_support_of_inclusion_sum_pos
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hHq : H < q)
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    {Θ : Type*} (T : Finset Θ) (μ : Θ → ℝ)
    (a : Θ → Fin 3 → ZMod q)
    (G : Θ → ((Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)))
    (ha : ∀ θ ∈ T, ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a θ 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (A : Matrix (Fin 3) (Fin 3) (ZMod q))
    [DecidablePred (fun θ => ∀ j, (fun i => A i j) ∈ transformed S (a θ) (G θ))]
    (hpositive : 0 < ∑ θ ∈ T,
      if ∀ j, (fun i => A i j) ∈ transformed S (a θ) (G θ) then μ θ else 0) :
    (∀ j, (fun i => A i j) ≠ 0) ∧
      (AffineIndependent (ZMod q) (fun j => fun i => A i j) ∨
        ∃ j k, j ≠ k ∧ (fun i => A i j) = (fun i => A i k)) ∧
      (AffineIndependent (ZMod q) (fun j => fun i => A i j) →
        ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          A.mulVec (fun i => (x i : ZMod q)) ≠ 0) := by
  classical
  obtain ⟨θ, hθ, hcols⟩ := exists_outcome_of_inclusion_sum_pos T μ _ hpositive
  have hcap := isCap_transformed hS (a θ) (G θ)
  have hzero := zero_not_mem_of_allowed hH hbox (a θ) (ha θ hθ) (G θ)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact hzero (hj ▸ hcols j)
  · by_cases hinj : Function.Injective (fun j => fun i => A i j)
    · exact Or.inl (affineIndependent_of_mem_cap hcap hcols hinj)
    · right
      simp only [Function.Injective] at hinj
      push Not at hinj
      obtain ⟨j, k, heq, hne⟩ := hinj
      exact ⟨j, k, hne, heq⟩
  · intro hAI x hx hne hrel
    have hsum := short_relation_excluded hS hbox (a θ) (ha θ hθ) (G θ)
      hcols hAI.injective hx hHq hne
    apply hsum
    funext i
    have hi := congrFun hrel i
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using hi

end Problem355.AuxiliarySet

end OAI
