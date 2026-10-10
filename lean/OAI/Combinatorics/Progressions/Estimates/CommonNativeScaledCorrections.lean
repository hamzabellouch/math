import OAI.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_uniform_native_scaled_corrections
    (D : R.CommonData P) (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i})) :
    let B := (P + 2) ^ 3 + 2 * P
    ∃ (C : R.CommonData B) (l : ℕ), C.quadruples ⊆ D.quadruples ∧ C.spaces = D.spaces ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
        (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
        (K : ℕ),
        (∀ i j, RationalHeightLE
          (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ
            (W.model.basis j)) i) K) →
        ∀ t (_ht : t ∈ C.quadruples), ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ ((W.dim : ℝ) + 1) * (K + 1) *
            (Real.exp ((B + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
          Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
          ((fun j : Σ _ : Fin 4, ι => (f.baseChange ℝ).repr
            ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
              (W.horizontalCoefficient hs c τ hG α
                (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1)))) j.2) - E - Q) ∈
            realFourCoordinateSpan
              (C.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f) := by
  intro B
  obtain ⟨C, l, hCD, hspaces, hl, hlp, hcorrect⟩ :=
    D.exists_uniform_native_coordinate_corrections (ι := ι) hs hP c τ hG
  refine ⟨C, l, hCD, hspaces, hl, hlp, ?_⟩
  intro α hα f K hf t ht
  obtain ⟨E, Q, hE, hQ, hres⟩ := hcorrect α hα f K hf t ht
  let I := R.interval ⟨t, C.subset ht⟩
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((B + 3) ^ 2)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖E‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    intro j
    simpa only [Real.norm_eq_abs, M, mul_div_assoc] using hE j
  refine ⟨E, Q, ?_, hQ, hres⟩
  have h := I.norm_bound_on_modulus hp α hα hM E hnorm
  simpa only [M, Real.exp_add, mul_div_assoc, mul_assoc] using h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
