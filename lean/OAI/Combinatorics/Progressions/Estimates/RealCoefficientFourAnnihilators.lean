import OAI.Combinatorics.Progressions.Linear.RealFourAnnihilatorKernel

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_real_coefficientFour_equations (hs : 2 ≤ s) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) :
    ∃ m : ℕ, m ≤ 4 * W.dim ∧ ∃ ℓ : (Fin 4 → W.L) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = D.coefficientFourSpace d ∧
      (∀ k i j, rationalLogHeight
        (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => W.L) k (W.model.basis i)) j) ≤
          coefficientFourAnnihilatorBudget P) ∧
      (∀ v : Fin 4 → ℝ ⊗[ℚ] W.L, v ∈ D.realCoefficientFourSpace d ↔
        ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ)
          ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).symm v) = 0) ∧
      (∀ (U : Submodule ℚ W.L) (v : ℝ ⊗[ℚ] W.L),
        v ∈ (fourPetalSpace U (D.coefficientFourSpace d)).baseChange ℝ ↔
          v ∈ U.baseChange ℝ ∧ ∀ j, realifyFunctional
            (((LinearMap.proj j).comp ℓ).comp
              (LinearMap.single ℚ (fun _ : Fin 4 => W.L) 0)) v = 0) := by
  obtain ⟨m, hm, ℓ, hsurj, hker, hheight⟩ := D.exists_coefficientFour_annihilator hs hP hbP d
  exact ⟨m, hm, ℓ, hsurj, hker, hheight,
    fun v => mem_real_four_annihilator_iff _ ℓ hker v,
    fun U v => mem_real_petal_annihilator_iff U _ ℓ hker v⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
