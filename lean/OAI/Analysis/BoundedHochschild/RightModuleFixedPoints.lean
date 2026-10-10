import OAI.Analysis.BoundedHochschild.RightAveragingOrbit

namespace OAI

/-! The common fixed points of right averaging are exactly the left
multiplication maps. This identifies the target of the projection without
assuming that a common fixed point has already been constructed. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma right_module_of_unitary_averages (T : M →L[ℂ] M)
    (hT : ∀ u : unitary M, finiteRightAverage (fun _ : Fin 1 => (u : M)) T = T) :
    ∀ a b : M, T (a * b) = T a * b := by
  have hu (a : M) (u : unitary M) : T (a * (u : M)) = T a * (u : M) := by
    have h := congrArg (fun S : M →L[ℂ] M => S a * (u : M)) (hT u)
    simpa only [finiteRightAverage_apply, Fin.sum_univ_one, mul_assoc,
      Unitary.star_mul_self_of_mem u.property, mul_one] using h
  intro a b
  obtain ⟨u, c, hb, _⟩ := CStarAlgebra.exists_sum_four_unitary b
  rw [hb]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hu]

lemma right_module_eq_left_multiplication (T : M →L[ℂ] M)
    (hT : ∀ a b : M, T (a * b) = T a * b) :
    T = ContinuousLinearMap.mul ℂ M (T 1) := by
  ext a
  simpa only [one_mul, ContinuousLinearMap.mul_apply'] using hT 1 a

theorem fixed_right_averages_iff (T : M →L[ℂ] M) :
    (∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
      finiteRightAverage m T = T) ↔ T = ContinuousLinearMap.mul ℂ M (T 1) := by
  constructor
  · intro hT
    apply right_module_eq_left_multiplication T
    apply right_module_of_unitary_averages T
    intro u
    exact hT 1 (fun _ => (u : M)) (by
      simp only [Fin.sum_univ_one, Unitary.mul_star_self_of_mem u.property])
  · intro hT n m hm
    conv_lhs => rw [hT]
    rw [finiteRightAverage_mul_left m hm, ← hT]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A simultaneous weak-star fixed point, when constructed, is necessarily
an actual bounded left multiplication map. -/
theorem weak_fixed_right_averages_realize (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : M → WeakDual ℂ X} {C : ℝ} (hC : 0 ≤ C) (hF : F ∈ weakOperatorBall C)
    (hfix : ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
      weakRightAverage e m F = F) :
    ∃ b : M, ‖ContinuousLinearMap.mul ℂ M b‖ ≤ C ∧
      weakOperatorImage e (ContinuousLinearMap.mul ℂ M b) = F := by
  obtain ⟨T, hT, hTF⟩ := weakOperatorBall_realize e hC hF
  have hfixed : ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
      finiteRightAverage m T = T := by
    intro n m hm
    apply weakOperatorImage_injective e
    rw [← weakRightAverage_image, hTF, hfix n m hm]
  have heq := (fixed_right_averages_iff T).mp hfixed
  exact ⟨T 1, heq ▸ hT, heq ▸ hTF⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
