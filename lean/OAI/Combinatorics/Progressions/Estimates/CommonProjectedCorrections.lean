import OAI.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

private theorem transport_corrections {X A : Type*} {E Q : X → Prop}
    {V : X → X → A → Prop} {H : A → Prop} {Z : ∀ (_ _ : X) (a : A), H a → Prop}
    (h : ∃ x y, E x ∧ Q y ∧ ∀ a, V x y a)
    (hmem : ∀ x y a (ha : H a), V x y a → Z x y a ha) :
    ∃ x y, E x ∧ Q y ∧ ∀ a (ha : H a), Z x y a ha := by
  obtain ⟨x, y, hx, hy, hv⟩ := h
  exact ⟨x, y, hx, hy, fun a ha => hmem x y a ha (hv a)⟩

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_projected_corrections (D : R.CommonData P) (hs : 1 ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : (pi (I.productModels V.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      (pi (I.productModels V.index)).filtration.SymbolSlowBound
        V.adapted.basis V.adapted.weight V.adapted.layers (fun _ => 1)
        (fun _ => (I.length : ℝ)) (Real.exp P) E ∧
      (pi (I.productModels V.index)).filtration.SymbolRationalGrid
        V.adapted.basis V.adapted.weight V.adapted.layers (fun _ => 1) V.denominator Q ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        (I.projectedCoefficient V.index α).baseChange ℝ
            (I.productSymbol V.index V.adapted.basis V.adapted.weight V.adapted.layers).coord -
          (I.projectedCoefficient V.index α).baseChange ℝ E.coord -
          (I.projectedCoefficient V.index α).baseChange ℝ Q.coord ∈
        (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩).baseChange ℝ := by
  intro I V
  apply transport_corrections (NativeRankInterval.SunflowerWitness.exists_projected_corrections (I := I) V hs)
  intro E Q α hα h
  exact (congrArg (fun U => _ ∈ U.baseChange ℝ)
    (D.horizontalImage_eq t ht ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).mp h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
