import OAI.Combinatorics.Progressions.Estimates.NativeRoundedCyclicModel

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem joint_affine_graph_recovery {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧
      (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      (∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i) ∧
      ∃ J' ⊆ H, J'.Nonempty ∧
        δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ)
          (Φ : (Fin r → ℤ) →+ (ZMod N × (∀ i, ZMod (M i))))
          (base : ZMod N × (∀ i, ZMod (M i))),
          (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
          Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
          (let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp Φ
           let α := variableCoefficientLift l base.2
           let β := fun j => variableCoefficientLift l (ψ (Pi.single j 1))
           (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
           (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
           ∀ h ∈ J', ∃ x : Fin r → ℤ,
             (∀ i, |x i| ≤ (R i : ℤ)) ∧
             (h, variableRoundedCoefficient M l (a h)) = base + Φ x ∧
             (∀ y : Fin r → ℤ, (∀ i, |y i| ≤ (R i : ℤ)) →
               (h, variableRoundedCoefficient M l (a h)) = base + Φ y → y = x) ∧
             ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
               |a h i - (α + ∑ j, (x j : ℝ) • β j) i - q i| ≤ 2 * ε i) := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_coordinate_rounding_moduli l hl ε hε hsmall
  let _ : ∀ i, NeZero (M i) := fun i => ⟨(hM i).ne'⟩
  obtain ⟨J', hJH, hJ, hsize, r, R, Φ, base, hrank, hinj, hrepr⟩ :=
    D.variable_graph_affine_model a c M l ε hMsmall hnear
  refine ⟨M, hM, hMsmall, hMerror, J', hJH, hJ, hsize, r, R, Φ, base,
    hrank, hinj, ?_⟩
  dsimp only
  refine ⟨variableCoefficientLift_mem_Ico l hl base.2, ?_, ?_⟩
  · intro j
    exact variableCoefficientLift_mem_Ico l hl _
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    refine ⟨x, hx, heq, ?_, ?_⟩
    · intro y hy hey
      exact hinj hy hx (add_left_cancel (hey.symm.trans heq))
    · obtain ⟨q, hq, herr⟩ := exists_variable_unrounded_affine l hl base.2
        ((AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp Φ) x (a h)
        (congrArg Prod.snd heq)
      exact ⟨q, hq, fun i => (herr i).trans (hMerror i)⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
