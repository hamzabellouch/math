import OAI.Combinatorics.Progressions.Geometry.CubicBoxStepDrop

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeIntegerExpansion.tripleBoxSlice {s : ℕ} {p : ℝ}
    {F : (Fin 6 → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : Fin 6 => 1) s p F)
    (a : Fin 3 → ℤ) : NativeIntegerExpansion (fun _ : Fin 3 => 1) s p
      (fun z => F (Erdos3.tripleBoxSlice a z)) := by
  let A : Fin 6 → Fin 3 → ℤ :=
    ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0], ![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]
  let b : Fin 6 → ℤ := ![0, a 0, 0, a 1, 0, a 2]
  have hmap (z : Fin 3 → ℤ) : integerAffineMap A b z = Erdos3.tripleBoxSlice a z := by
    funext k
    have hlast : (5 : Fin 6) = (4 : Fin 5).succ := rfl
    fin_cases k <;> norm_num [A, b, integerAffineMap, Erdos3.tripleBoxSlice,
      Fin.sum_univ_three, hlast, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  have heq : (fun z => F (integerAffineMap A b z)) =
      (fun z => F (Erdos3.tripleBoxSlice a z)) := by
    funext z
    rw [hmap]
  exact heq ▸ E.affinePullback A b

theorem exists_cubic_kernel_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
      (F : (Fin 6 → ℤ) → ℂ), 0 ≤ q →
      NativeIntegerExpansion (fun _ : Fin 6 => 1) 2 q F →
      (∀ x : Fin 6 → ZMod N, ‖F (fun k => ((x k).val : ℤ))‖ ≤ 1) →
      ∀ {δ ε : ℝ}, 0 < δ → 0 < ε →
      δ ≤ (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
        V.cubicAntisymmetricPair i j h.val y.val ((k.val : ℤ) + shift))).re →
      (𝔼 x : Fin 6 → ZMod N,
        ‖V.cubicAntisymmetricBoxValue i j shift (fun k => ((x k).val : ℤ)) -
          F (fun k => ((x k).val : ℤ))‖) ≤ ε →
      ∃ D G : (Fin 3 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + q + C) ^ C) D) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + q + C) ^ C) G) ∧
        (∀ z, ‖D z‖ ≤ 1) ∧
        (∀ z : Fin 3 → ZMod N, ‖G (fun k => ((z k).val : ℤ))‖ ≤ 1) ∧
        δ ^ 2 / 2 ≤ (𝔼 z : Fin 3 → ZMod N, ‖D (fun k => ((z k).val : ℤ))‖ ^ 2) ∧
        δ ^ 2 / 2 ≤ (𝔼 z : Fin 3 → ZMod N,
          ‖V.cubicAntisymmetricPair i j ((z 1).val : ℤ) ((z 2).val : ℤ)
              (((z 0).val : ℤ) + shift) * D (fun k => ((z k).val : ℤ))‖ ^ 2) ∧
        (𝔼 z : Fin 3 → ZMod N,
          ‖V.cubicAntisymmetricPair i j ((z 1).val : ℤ) ((z 2).val : ℤ)
              (((z 0).val : ℤ) + shift) * D (fun k => ((z k).val : ℤ)) -
            G (fun k => ((z k).val : ℤ))‖) ≤ 2 * ε / δ ^ 2 := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_cubic_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro p q V N _ i j shift F hq EF hFunit δ ε hδ hε hbias herr
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let K := fun k h y : ℤ => V.cubicAntisymmetricPair i j h y (k + shift)
  let Kc := fun k h y : ZMod N => K k.val h.val y.val
  let Fc := fun x : Fin 6 → ZMod N => F (fun k => ((x k).val : ℤ))
  obtain ⟨a, hmass, henergy, herror⟩ := exists_triple_box_anchor_approximation Kc
    (fun k h y => V.cubicAntisymmetricPair_norm i j _ _ _) Fc hδ hε hbias herr
  let b : Fin 3 → ℤ := fun k => ((a k).val : ℤ)
  let D := tripleBoxAnchorFactor K b
  let G := fun z : Fin 3 → ℤ => F (tripleBoxSlice b z)
  obtain ⟨ED⟩ := hanchor V i j shift b
  have hsum : (p + q + A) ^ A + (p + q) ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  have hDb : (p + A) ^ A ≤ (p + q + C) ^ C := by
    have hmono : (p + A) ^ A ≤ (p + q + A) ^ A := by
      apply pow_le_pow_left₀ (by positivity)
      linarith only [hq]
    exact hmono.trans ((le_add_of_nonneg_right (add_nonneg hp hq)).trans hsum)
  have hGb : q ≤ (p + q + C) ^ C := by
    have hpow : 0 ≤ (p + q + A) ^ A := by positivity
    linarith only [hsum, hpow, hp]
  have hcan (z : Fin 3 → ZMod N) :
      (fun k => ((tripleBoxSlice a z k).val : ℤ)) =
        tripleBoxSlice b (fun k => ((z k).val : ℤ)) := by
    funext k
    fin_cases k <;> rfl
  refine ⟨D, G, ⟨ED.mono hDb⟩, ⟨(EF.tripleBoxSlice b).mono hGb⟩, ?_, ?_, hmass, henergy, ?_⟩
  · exact tripleBoxAnchorFactor_norm_le_one K (fun k h y => V.cubicAntisymmetricPair_norm i j _ _ _) b
  · intro z
    simpa only [hcan, G] using hFunit (tripleBoxSlice a z)
  · simpa only [Fc, hcan, Kc, K, D, G, tripleBoxAnchorFactor, b] using herror

end Erdos3

end

end OAI
