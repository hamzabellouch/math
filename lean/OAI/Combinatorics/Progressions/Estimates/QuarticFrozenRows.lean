import OAI.Combinatorics.Progressions.Estimates.QuarticCyclicDiagonalComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem quarticBlockSample_input (z : QuarticCornerBlock) (x : Fin 2 → ℤ) :
    quarticSampledInput (quarticCanonicalSample (quarticBlockCorner z).val) x =
      Sum.elim (fun _ : Fin 4 => quarticInput (x 0) (fun _ => x 1))
        (Sum.elim (fun _ : Fin 6 => quarticInput (x 0) ![x 0, x 1, x 1])
          (Sum.elim (fun _ : Fin 4 => quarticInput (x 0) ![x 0, x 0, x 1])
            (fun _ : Unit => fun _ => x 0))) z := by
  rw [quarticBlockCorner_canonical]
  rcases z with z | z
  · simp only [Sum.elim_inl, quarticSampledInput]
    apply congrArg (quarticInput (x 0))
    funext k
    fin_cases k <;> rfl
  rcases z with z | z
  · simp only [Sum.elim_inl, Sum.elim_inr, quarticSampledInput]
    apply congrArg (quarticInput (x 0))
    funext k
    fin_cases k <;> rfl
  rcases z with z | z
  · simp only [Sum.elim_inl, Sum.elim_inr, quarticSampledInput]
    apply congrArg (quarticInput (x 0))
    funext k
    fin_cases k <;> rfl
  simp only [Sum.elim_inr, quarticSampledInput]
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> rfl

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticHnnnTensor (a : Fin 4 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval 4 a (quarticInput (x 0) (fun _ => x 1))

noncomputable def quarticHhnnTensor (a : Fin 6 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval 6 a (quarticInput (x 0) ![x 0, x 1, x 1])

noncomputable def quarticHhhnTensor (a : Fin 4 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval 4 a (quarticInput (x 0) ![x 0, x 0, x 1])

theorem quarticHnnnTensor_norm (a : Fin 4 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.quarticHnnnTensor a x‖ ≤ 1 := by
  rw [quarticHnnnTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem quarticHhnnTensor_norm (a : Fin 6 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.quarticHhnnTensor a x‖ ≤ 1 := by
  rw [quarticHhnnTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem quarticHhhnTensor_norm (a : Fin 4 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.quarticHhhnTensor a x‖ ≤ 1 := by
  rw [quarticHhhnTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem quarticHnnnTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 4 → Fin W.outputDim, ‖W.quarticHnnnTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval 4 _

theorem quarticHhnnTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 6 → Fin W.outputDim, ‖W.quarticHhnnTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval 6 _

theorem quarticHhhnTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 4 → Fin W.outputDim, ‖W.quarticHhhnTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval 4 _

theorem quarticSymmetricFifteen_merge (a : Fin 4 → Fin W.outputDim)
    (b : Fin 6 → Fin W.outputDim) (c : Fin 4 → Fin W.outputDim)
    (d : Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.quarticSymmetricFifteen (quarticFifteenMerge a b c d) x) =
      W.quarticHnnnTensor a x *
        (W.quarticHhnnTensor b x * (W.quarticHhhnTensor c x * W.eval d (fun _ => x 0))) := by
  let f : QuarticCornerBlock → ℂ :=
    Sum.elim (fun j => W.eval (a j) (quarticInput (x 0) (fun _ => x 1)))
      (Sum.elim (fun j => W.eval (b j) (quarticInput (x 0) ![x 0, x 1, x 1]))
        (Sum.elim (fun j => W.eval (c j) (quarticInput (x 0) ![x 0, x 0, x 1]))
          (fun _ => W.eval d (fun _ => x 0))))
  have hterm (z : QuarticCornerBlock) :
      W.eval (quarticFifteenMerge a b c d (quarticBlockEquiv z))
        (quarticSampledInput (quarticCanonicalSample (quarticBlockEquiv z).val) x) = f z := by
    change W.eval (quarticFifteenMerge a b c d (quarticBlockCorner z))
      (quarticSampledInput (quarticCanonicalSample (quarticBlockCorner z).val) x) = _
    rw [quarticFifteenMerge_block, quarticBlockSample_input]
    rcases z with z | z
    · rfl
    rcases z with z | z
    · rfl
    rcases z with z | z <;> rfl
  rw [quarticSymmetricFifteen, star_star]
  calc
    _ = ∏ z : QuarticCornerBlock,
        W.eval (quarticFifteenMerge a b c d (quarticBlockEquiv z))
          (quarticSampledInput (quarticCanonicalSample (quarticBlockEquiv z).val) x) :=
      (quarticBlockEquiv.prod_comp _).symm
    _ = ∏ z : QuarticCornerBlock, f z := Finset.prod_congr rfl (fun z _ => hterm z)
    _ = _ := by
      simp only [QuarticCornerBlock, Fintype.prod_sum_type, f, Sum.elim_inl, Sum.elim_inr,
        Fintype.prod_unique]
      rfl

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev QuarticMiddleIndex (D : ℕ) := (Fin 6 → Fin D) × (Fin 4 → Fin D)

noncomputable def quarticGroupedFifteenMerge {I : Type*} (a : Fin 4 → I)
    (b : (Fin 6 → I) × (Fin 4 → I)) (c : I) : QuarticNonconstantCorner → I :=
  quarticFifteenMerge a b.1 b.2 c

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticMiddleTensor (b : QuarticMiddleIndex W.outputDim)
    (x : Fin 2 → ℤ) : ℂ := W.quarticHhnnTensor b.1 x * W.quarticHhhnTensor b.2 x

theorem quarticMiddleTensor_norm (b : QuarticMiddleIndex W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.quarticMiddleTensor b x‖ ≤ 1 := by
  rw [quarticMiddleTensor, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.quarticHhnnTensor_norm _ _)).trans
    (W.quarticHhhnTensor_norm _ _)

theorem quarticMiddleTensor_unit (x : Fin 2 → ℤ) :
    ∑ b : QuarticMiddleIndex W.outputDim, ‖W.quarticMiddleTensor b x‖ ^ 2 = 1 := by
  simp only [QuarticMiddleIndex, Fintype.sum_prod_type, quarticMiddleTensor, norm_mul, mul_pow,
    ← Finset.mul_sum, W.quarticHhhnTensor_unit, mul_one, W.quarticHhnnTensor_unit]

theorem quarticSymmetricFifteen_grouped_merge (a : Fin 4 → Fin W.outputDim)
    (b : QuarticMiddleIndex W.outputDim) (c : Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.quarticSymmetricFifteen (quarticGroupedFifteenMerge a b c) x) =
      W.quarticHnnnTensor a x * (W.quarticMiddleTensor b x * W.eval c (fun _ => x 0)) := by
  rw [quarticGroupedFifteenMerge, W.quarticSymmetricFifteen_merge, quarticMiddleTensor]
  ring

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_original_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p)
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 p M.eval
        (fun k x => W.eval k (quarticInput (x 0) (fun _ => x 1))) →
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval W.quarticRoot.quarticHnnnTensor := by
  obtain ⟨A, _, hroot⟩ := exists_explicit_quartic_root_equivalence
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M W E
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + A) ^ A + p
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_left (by positivity)
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_right hp
  have hdiag (x : Fin 2 → ℤ) :
      quarticInput (x 0) (fun _ => x 1) = fun j : QuarticReplicatedIndex => x j.1 := by
    rw [quarticInput_diagonal]
    have hx : correlationInput (x 0) (x 1) = x := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
  have E' : NativeIntegerVectorEquivalence 3 p M.eval
      (fun k x => W.eval k (fun j => x j.1)) := by
    simpa only [hdiag] using E
  have F := (hroot W).coordinatePullback (fun j : QuarticReplicatedIndex => j.1)
  have hright : (fun a (x : Fin 2 → ℤ) =>
      tensorVector W.quarticRoot.eval 4 a (fun j : QuarticReplicatedIndex => x j.1)) =
      W.quarticRoot.quarticHnnnTensor := by
    funext a x
    rw [quarticHnnnTensor, hdiag]
  have F' : NativeIntegerVectorEquivalence 3 t
      (fun k x => W.eval k (fun j => x j.1)) W.quarticRoot.quarticHnnnTensor := by
    rw [← hright]
    exact F.mono hAt
  have H := htrans ht (E'.mono hpt) F' (fun x => W.unit_eval _)
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_hhnn_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (h : ℤ)
      (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 ((p + C) ^ C)
        (fun x => W.eval k (quarticInput h ![h, x (), x ()]))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (fun _ : QuarticReplicatedIndex => 1)
  refine ⟨C, hC, ?_⟩
  intro p W h k
  classical
  let S : Finset QuarticReplicatedIndex := {quarticReplica 1, quarticReplica 2}
  let A : QuarticReplicatedIndex → ℤ := fun j => if j ∈ S then 1 else 0
  let b : QuarticReplicatedIndex → ℤ := fun j => if j ∈ S then 0 else h
  have hA : ∀ j, j ∉ S → A j = 0 := by
    intro j hj
    exact ite_eq_right hj
  obtain ⟨E, _⟩ := hfreeze W S A b k hA
  have hdegree : (∑ i ∈ S, (fun _ : QuarticReplicatedIndex => 1) i) = 2 := by
    norm_num [S, quarticReplica]
  have hin (x : Unit → ℤ) : (fun j => b j + A j * x ()) = quarticInput h ![h, x (), x ()] := by
    funext j
    rcases j with ⟨j, l⟩
    fin_cases j <;> fin_cases l <;> simp [A, b, S, quarticReplica, quarticInput]
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (quarticInput h ![h, x (), x ()])) := by
    funext x
    rw [hin]
  rw [hdegree, heq] at E
  exact ⟨E⟩

theorem exists_quarticHhnnTensor_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (h : ℤ)
      (a : Fin 6 → Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 ((p + C) ^ C)
        (fun x => W.quarticHhnnTensor a ![h, x ()])) := by
  obtain ⟨A, _, hrow⟩ := exists_quartic_hhnn_row_expansion
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 6
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W h a
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨F⟩ := hprod (fun i (x : Unit → ℤ) => W.eval (a i) (quarticInput h ![h, x (), x ()]))
    (by positivity : 0 ≤ (p + A) ^ A) (fun i => hrow W h (a i))
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

theorem exists_quartic_hhhn_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (h : ℤ)
      (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.eval k (quarticInput h ![h, h, x ()]))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (fun _ : QuarticReplicatedIndex => 1)
  refine ⟨C, hC, ?_⟩
  intro p W h k
  classical
  let S : Finset QuarticReplicatedIndex := {quarticReplica 2}
  let A : QuarticReplicatedIndex → ℤ := fun j => if j ∈ S then 1 else 0
  let b : QuarticReplicatedIndex → ℤ := fun j => if j ∈ S then 0 else h
  have hA : ∀ j, j ∉ S → A j = 0 := by
    intro j hj
    exact ite_eq_right hj
  obtain ⟨E, _⟩ := hfreeze W S A b k hA
  have hdegree : (∑ i ∈ S, (fun _ : QuarticReplicatedIndex => 1) i) = 1 := by
    norm_num [S, quarticReplica]
  have hin (x : Unit → ℤ) : (fun j => b j + A j * x ()) = quarticInput h ![h, h, x ()] := by
    funext j
    rcases j with ⟨j, l⟩
    fin_cases j <;> fin_cases l <;> simp [A, b, S, quarticReplica, quarticInput]
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (quarticInput h ![h, h, x ()])) := by
    funext x
    rw [hin]
  rw [hdegree, heq] at E
  exact ⟨E⟩

theorem exists_quarticHhhnTensor_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (h : ℤ)
      (a : Fin 4 → Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.quarticHhhnTensor a ![h, x ()])) := by
  obtain ⟨A, _, hrow⟩ := exists_quartic_hhhn_row_expansion
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 4
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W h a
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨F⟩ := hprod (fun i (x : Unit → ℤ) => W.eval (a i) (quarticInput h ![h, h, x ()]))
    (by positivity : 0 ≤ (p + A) ^ A) (fun i => hrow W h (a i))
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

theorem exists_quarticMiddleTensor_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (h : ℤ)
      (b : QuarticMiddleIndex W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 ((p + C) ^ C)
        (fun x => W.quarticMiddleTensor b ![h, x ()])) := by
  obtain ⟨A, _, htwo⟩ := exists_quarticHhnnTensor_row_expansion
  obtain ⟨B, _, hone⟩ := exists_quarticHhhnTensor_row_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  let T := (X + Polynomial.C A) ^ A + U + (U + 2) ^ 2 + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p W h b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + A) ^ A + raisedNiltestBudget ((p + B) ^ B)
  have ht : 0 ≤ t := by dsimp [t, raisedNiltestBudget]; positivity
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_right (by unfold raisedNiltestBudget; positivity)
  have hBt : raisedNiltestBudget ((p + B) ^ B) ≤ t := le_add_of_nonneg_left (by positivity)
  have E := (Classical.choice (hone W h b.2)).raiseStep (by norm_num : 1 ≤ 2)
    (by positivity : 0 ≤ (p + B) ^ B)
  obtain ⟨F⟩ := hmul ht ((Classical.choice (htwo W h b.1)).mono hAt) (E.mono hBt)
  have hcost : (t + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, T, t, raisedNiltestBudget, add_assoc, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
