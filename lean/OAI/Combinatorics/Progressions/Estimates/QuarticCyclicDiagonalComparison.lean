import OAI.Combinatorics.Progressions.Estimates.QuarticRootExchange

namespace OAI

section

namespace Erdos3

def quarticBlockPermutation (e : Equiv.Perm (Fin 3)) : ReplicatedPermutation (mixedCorrelationDegree 3) :=
  Fin.cases (Equiv.refl _) (fun _ => e)

theorem quarticInput_replica (h : ℤ) (v : Fin 3 → ℤ) (j : Fin 3) :
    quarticInput h v (quarticReplica j) = v j := by
  fin_cases j <;> rfl

theorem quarticInput_permute (e : Equiv.Perm (Fin 3)) (h : ℤ) (v : Fin 3 → ℤ) :
    (fun j => quarticInput h v
      ((replicatedPermutation (mixedCorrelationDegree 3) (quarticBlockPermutation e)).symm j)) =
        quarticInput h (fun i => v (e.symm i)) := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j
  · rfl
  · change Fin 3 at k
    change quarticInput h v (quarticReplica (e.symm k)) =
      quarticInput h (fun i => v (e.symm i)) (quarticReplica k)
    rw [quarticInput_replica, quarticInput_replica]

theorem quartic_eval_permute {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
      f i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = f i x)
    (e : Equiv.Perm (Fin 3)) (i : I) (h : ℤ) (v : Fin 3 → ℤ) :
    f i (quarticInput h (fun j => v (e j))) = f i (quarticInput h v) := by
  have H := hsymm (quarticBlockPermutation e.symm) i (quarticInput h v)
  rw [quarticInput_permute] at H
  simpa only [Equiv.symm_symm] using H

theorem quartic_eval_permutationWord {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
      f i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = f i x)
    (a : Fin 6) (i : I) (h : ℤ) (v : Fin 3 → ℤ) :
    f i (quarticInput h (fun j => v (quarticPermutationWord a j))) = f i (quarticInput h v) :=
  quartic_eval_permute f hsymm (quarticWordPermutation a) i h v

theorem quartic_eval_doubleFirst {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
      f i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = f i x)
    (a : Fin 3) (i : I) (h : ℤ) (v : Fin 3 → ℤ) :
    f i (quarticInput h (fun j => v (quarticDoubleFirstWord a j))) =
      f i (quarticInput h ![v 1, v 1, v 2]) := by
  have heq : (fun j => v (quarticDoubleFirstWord a j)) =
      (fun j => ![v 1, v 1, v 2] (Equiv.swap a 2 j)) := by
    funext j
    fin_cases a <;> fin_cases j <;> rfl
  rw [heq]
  exact quartic_eval_permute f hsymm (Equiv.swap a 2) i h _

theorem quartic_eval_doubleSecond {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
      f i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = f i x)
    (a : Fin 3) (i : I) (h : ℤ) (v : Fin 3 → ℤ) :
    f i (quarticInput h (fun j => v (quarticDoubleSecondWord a j))) =
      f i (quarticInput h ![v 1, v 2, v 2]) := by
  have heq : (fun j => v (quarticDoubleSecondWord a j)) =
      (fun j => ![v 1, v 2, v 2] (Equiv.swap a 0 j)) := by
    funext j
    fin_cases a <;> fin_cases j <;> rfl
  rw [heq]
  exact quartic_eval_permute f hsymm (Equiv.swap a 0) i h _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev QuarticSixFactorIndex (I : Type*) := (Fin 6 → I) × ((Fin 3 → I) × (Fin 3 → I))

noncomputable def quarticSixMain {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : Fin 6 → I) (x : Fin 4 → ℤ) : ℂ :=
  ∏ j, f (a j) (quarticInput (x 0) ![x 1, x 2, x 3])

noncomputable def quarticSixBoundary {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : (Fin 3 → I) × (Fin 3 → I)) (h k l : ℤ) : ℂ :=
  (∏ j, f (a.1 j) (quarticInput h ![k, k, l])) *
    ∏ j, f (a.2 j) (quarticInput h ![k, l, l])

noncomputable def quarticSixFactorVector {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : QuarticSixFactorIndex I) (x : Fin 4 → ℤ) : ℂ :=
  quarticSixMain f a.1 x * quarticSixBoundary f a.2 (x 0) (x 2) (x 3)

def quarticSixFactorCoordinate {I : Type*} (a : QuarticSixFactorIndex I) :
    Fin 6 ⊕ (Fin 3 ⊕ Fin 3) → I :=
  Sum.elim a.1 (Sum.elim a.2.1 a.2.2)

noncomputable def quarticSixFactorReindex {I : Type*} (a : QuarticSixFactorIndex I) :
    QuarticSurvivor → I :=
  fun v => quarticSixFactorCoordinate a (quarticSurvivorClassEquiv.symm v)

theorem quarticSixFactorReindex_class {I : Type*} (a : QuarticSixFactorIndex I)
    (r : Fin 6 ⊕ (Fin 3 ⊕ Fin 3)) :
    quarticSixFactorReindex a (quarticSurvivorClassMap r) = quarticSixFactorCoordinate a r := by
  change quarticSixFactorCoordinate a (quarticSurvivorClassEquiv.symm (quarticSurvivorClassEquiv r)) = _
  rw [Equiv.symm_apply_apply]

theorem quarticSixFactorVector_reindex {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
      f i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = f i x)
    (a : QuarticSixFactorIndex I) (x : Fin 4 → ℤ) :
    quarticSurvivorVector f (quarticSixFactorReindex a) x = quarticSixFactorVector f a x := by
  have hy : (fun j : Fin 3 => x j.succ) = ![x 1, x 2, x 3] := by
    funext j
    fin_cases j <;> rfl
  have hperm (b : Fin 6) (i : I) :
      f i (quarticInput (x 0) (fun j => x (quarticPermutationWord b j).succ)) =
        f i (quarticInput (x 0) (fun j => x j.succ)) :=
    quartic_eval_permutationWord f hsymm b i (x 0) (fun j => x j.succ)
  have hfirst (b : Fin 3) (i : I) :
      f i (quarticInput (x 0) (fun j => x (quarticDoubleFirstWord b j).succ)) =
        f i (quarticInput (x 0) ![x 2, x 2, x 3]) :=
    quartic_eval_doubleFirst f hsymm b i (x 0) (fun j => x j.succ)
  have hsecond (b : Fin 3) (i : I) :
      f i (quarticInput (x 0) (fun j => x (quarticDoubleSecondWord b j).succ)) =
        f i (quarticInput (x 0) ![x 2, x 3, x 3]) :=
    quartic_eval_doubleSecond f hsymm b i (x 0) (fun j => x j.succ)
  change (∏ v : QuarticSurvivor, quarticTerm f v.val (quarticSixFactorReindex a v) x) = _
  rw [quartic_survivor_class_product]
  simp only [quarticSixFactorReindex_class]
  simp only [quarticSurvivorClassMap, quarticTerm, quarticSixFactorCoordinate, Sum.elim_inl, Sum.elim_inr]
  simp only [hperm, hfirst, hsecond]
  change (∏ j : Fin 6, f (a.1 j) (quarticInput (x 0) (fun i => x i.succ))) *
    ((∏ j : Fin 3, f (a.2.1 j) (quarticInput (x 0) ![x 2, x 2, x 3])) *
      ∏ j : Fin 3, f (a.2.2 j) (quarticInput (x 0) ![x 2, x 3, x 3])) = _
  rw [hy]
  rfl

theorem quarticSixFactorIndex_card {I : Type*} [Fintype I] :
    Fintype.card (QuarticSixFactorIndex I) = Fintype.card (QuarticSurvivor → I) := by
  simp only [QuarticSixFactorIndex, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, quarticSurvivor_card]
  ring

theorem quarticSixMain_unit {I : Type*} [Fintype I] (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (x : Fin 4 → ℤ) :
    ∑ a, ‖quarticSixMain f a x‖ ^ 2 = 1 := by
  change (∑ a : Fin 6 → I, ‖∏ j, f (a j) (quarticInput (x 0) ![x 1, x 2, x 3])‖ ^ 2) = 1
  exact finite_product_unit_vector
    (fun (_ : Fin 6) (i : I) => f i (quarticInput (x 0) ![x 1, x 2, x 3])) (fun _ => hf _)

theorem quarticSixBoundary_unit {I : Type*} [Fintype I] (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (h k l : ℤ) :
    ∑ a, ‖quarticSixBoundary f a h k l‖ ^ 2 = 1 := by
  have hprod (v : Fin 3 → ℤ) :
      (∑ a : Fin 3 → I, ‖∏ j, f (a j) (quarticInput h v)‖ ^ 2) = 1 :=
    finite_product_unit_vector (fun (_ : Fin 3) (i : I) => f i (quarticInput h v)) (fun _ => hf _)
  simp only [quarticSixBoundary, Fintype.sum_prod_type, norm_mul, mul_pow,
    ← Finset.mul_sum, hprod, mul_one]

theorem quarticSixFactorVector_unit {I : Type*} [Fintype I] (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (x : Fin 4 → ℤ) :
    ∑ a, ‖quarticSixFactorVector f a x‖ ^ 2 = 1 := by
  simp only [quarticSixFactorVector, Fintype.sum_prod_type, norm_mul, mul_pow,
    ← Finset.mul_sum, quarticSixBoundary_unit f hf, quarticSixMain_unit f hf, mul_one]

theorem quarticSixBoundary_norm {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (a : (Fin 3 → I) × (Fin 3 → I)) (h k l : ℤ) :
    ‖quarticSixBoundary f a h k l‖ ≤ 1 := by
  have hprod (v : Fin 3 → ℤ) (b : Fin 3 → I) : ‖∏ j, f (b j) (quarticInput h v)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hf (b j) _)
  unfold quarticSixBoundary
  rw [norm_mul]
  exact (mul_le_mul (hprod _ _) (hprod _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem quarticSixMain_tensorPower {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (a : Fin 6 → Fin W.outputDim) (x : Fin 4 → ℤ) :
    quarticSixMain W.eval a x =
      (W.tensorPower 6).eval (tensorIndexEquiv W.outputDim 6 a)
        (quarticInput (x 0) ![x 1, x 2, x 3]) := by
  rw [tensorPower_eval]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem tensorPower_quartic_repeated_symmetry {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
      W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval i x)
    (n : ℕ) (e : ReplicatedPermutation (mixedCorrelationDegree 3))
    (i : Fin (W.outputDim ^ n)) (x : QuarticReplicatedIndex → ℤ) :
    (W.tensorPower n).eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) =
      (W.tensorPower n).eval i x := by
  simp only [tensorPower_eval]
  apply Finset.prod_congr rfl
  intro j _
  exact hsymm e _ x

theorem quarticSixMain_norm {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (a : Fin 6 → Fin W.outputDim) (x : Fin 4 → ℤ) :
    ‖quarticSixMain W.eval a x‖ ≤ 1 := by
  rw [quarticSixMain, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_quartic_six_factor_multilinearization :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) =
            W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) := by
  obtain ⟨C, hC, hmulti⟩ := exists_quartic_survivor_multilinearization
  refine ⟨C, hC, ?_⟩
  intro p M
  obtain ⟨W, hdim, hsymm, Ebase, Esecond⟩ := hmulti M
  refine ⟨W, hdim, hsymm, Ebase, ?_⟩
  apply Esecond.of_coordinate_maps _ _ id quarticSixFactorReindex
    (fun _ _ => rfl) _ Esecond.left_dimension _ le_rfl
  · intro a x
    exact (quarticSixFactorVector_reindex W.eval hsymm a x).symm
  · rw [quarticSixFactorIndex_card]
    exact Esecond.right_dimension

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem quartic_six_factor_sample_correlation {J : Type*} [Fintype J] {q r v : ℝ}
    {chi : J → (Fin 4 → ℤ) → ℂ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q)
    (E : NativeIntegerVectorEquivalence 3 r chi (quarticSixFactorVector W.eval))
    (S : Finset ℤ) (h k l : ℤ) (j : J) (f : ℤ → ℂ)
    (hcorr : Real.exp (-v) ≤ ‖𝔼 n ∈ S, f n * star (chi j ![h, n, k, l])‖) :
    ∃ (a : QuarticSixFactorIndex (Fin W.outputDim))
      (z : Fin (E.selectedExpansion j a).count),
      Real.exp (-(v + 2 * r)) ≤ ‖𝔼 n ∈ S,
        f n * star (quarticSixMain W.eval a.1 ![h, n, k, l]) *
          star (((E.selectedExpansion j a).test z).eval ![h, n, k, l])‖ := by
  obtain ⟨a, z, haz⟩ := E.transfer_sample_correlation S (fun n => ![h, n, k, l]) j f
    (fun _ _ => quarticSixFactorVector_unit W.eval W.unit_eval _) hcorr
  let T := (E.selectedExpansion j a).test z
  let F (n : ℤ) := f n * star (quarticSixMain W.eval a.1 ![h, n, k, l]) * star (T.eval ![h, n, k, l])
  have heq : (𝔼 n ∈ S, f n * star (quarticSixFactorVector W.eval a ![h, n, k, l]) *
      star (T.eval ![h, n, k, l])) =
      (𝔼 n ∈ S, F n) * star (quarticSixBoundary W.eval a.2 h k l) := by
    rw [Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro n _
    simp only [F, quarticSixFactorVector, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, star_mul]
    ring
  change Real.exp (-(v + 2 * r)) ≤ ‖𝔼 n ∈ S,
    f n * star (quarticSixFactorVector W.eval a ![h, n, k, l]) * star (T.eval ![h, n, k, l])‖ at haz
  rw [heq, norm_mul, norm_star] at haz
  refine ⟨a, z, haz.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (quarticSixBoundary_norm W.eval W.norm_eval a.2 h k l) (norm_nonneg _)).trans_eq (mul_one _)

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

open scoped BigOperators

def quarticPermuteSample (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2) : Fin 4 → Fin 2 :=
  Fin.cases (π 0) (fun j => π (e j).succ)

namespace NativeMultidegreeNilcharacter

theorem exists_division_quartic_last_slots_equivalence (d : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => (W.rationalDilation ((d : ℚ)⁻¹)).eval i (quarticSampledInput π x))
        (fun i x => (W.rationalDilation ((d : ℚ)⁻¹)).eval i
          (quarticSampledInput (quarticPermuteSample e π) x)) := by
  obtain ⟨A, _, hcompare⟩ := exists_quartic_rational_division_equivalence d
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have heq : (fun i (x : Fin 2 → ℤ) => W.eval i (quarticSampledInput π (fun k => x k / (d : ℤ)))) =
      (fun i x => W.eval i (quarticSampledInput (quarticPermuteSample e π) (fun k => x k / (d : ℤ)))) := by
    funext i x
    symm
    change W.eval i (quarticInput (x (π 0) / (d : ℤ)) (fun j => x (π (e j).succ) / (d : ℤ))) =
      W.eval i (quarticInput (x (π 0) / (d : ℤ)) (fun j => x (π j.succ) / (d : ℤ)))
    exact quartic_eval_permute W.eval hsymm e i (x (π 0) / (d : ℤ)) (fun j => x (π j.succ) / (d : ℤ))
  have F : NativeIntegerVectorEquivalence 3 ((p + A) ^ A)
      (fun i (x : Fin 2 → ℤ) => W.eval i (quarticSampledInput π (fun k => x k / (d : ℤ))))
      (fun i x => (W.rationalDilation ((d : ℚ)⁻¹)).eval i
        (quarticSampledInput (quarticPermuteSample e π) x)) := by
    rw [heq]
    exact (hcompare W (quarticPermuteSample e π)).symm
  have H := htrans hu (hcompare W π) F (fun x => W.unit_eval _)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

theorem exists_division_quartic_tensor_last_slots_equivalence (d n : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => ((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval i (quarticSampledInput π x))
        (fun i x => ((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval i (quarticSampledInput (quarticPermuteSample e π) x)) := by
  obtain ⟨A, _, hdivision⟩ := exists_division_quartic_last_slots_equivalence d
  obtain ⟨B, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_power_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have H := htensor hu (hdivision W hsymm e π)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have E := H.mono hcost
  have hdim : (Fintype.card (Fin ((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _
    have h := E.left_dimension
    simp only [Fintype.card_fun, Fintype.card_fin] at h
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _ at h
    exact h
  apply E.of_coordinate_maps _ _ (tensorIndexEquiv W.outputDim n).symm
    (tensorIndexEquiv W.outputDim n).symm _ _ hdim hdim (le_refl _)
  · intro i x
    exact (W.rationalDilation ((d : ℚ)⁻¹)).tensorPower_eval n i (quarticSampledInput π x)
  · intro i x
    exact (W.rationalDilation ((d : ℚ)⁻¹)).tensorPower_eval n i
      (quarticSampledInput (quarticPermuteSample e π) x)

theorem exists_quartic_root_last_slots_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => W.quarticRoot.eval i (quarticSampledInput π x))
        (fun i x => W.quarticRoot.eval i (quarticSampledInput (quarticPermuteSample e π) x)) := by
  obtain ⟨C, hC, h⟩ := exists_division_quartic_tensor_last_slots_equivalence 4 64
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  exact h W hsymm e π

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticCornerWeight (v : Fin 4 → Fin 2) : ℕ := ∑ k, (v k).val

def quarticCornerSample (v : Fin 4 → Fin 2) : Fin 4 → Fin 2 := fun k => (v k).rev

def quarticCanonicalSample (v : Fin 4 → Fin 2) : Fin 4 → Fin 2 :=
  fun k => if k.val < quarticCornerWeight v then 0 else 1

def quarticTailSortWord (v : Fin 4 → Fin 2) : Fin 6 :=
  if v 1 = 0 then
    if v 2 = 0 then (if v 3 = 0 then 0 else 5)
    else (if v 3 = 0 then 2 else 3)
  else if v 2 = 0 ∧ v 3 = 1 then 1 else 0

def quarticHeadWord (v : Fin 4 → Fin 2) : Fin 6 :=
  if v 1 = 1 then 0 else if v 2 = 1 then 2 else 5

noncomputable def quarticPreExchangeSample (v : Fin 4 → Fin 2) : Fin 4 → Fin 2 :=
  quarticPermuteSample (quarticWordPermutation (quarticHeadWord v)) (quarticCornerSample v)

noncomputable def quarticPostExchangeWord (v : Fin 4 → Fin 2) : Fin 6 :=
  quarticTailSortWord (quarticSwapSample (quarticPermuteSample (quarticWordPermutation (quarticHeadWord v)) v))

theorem quarticCornerSample_input (v : Fin 4 → Fin 2) (x : Fin 2 → ℤ) :
    quarticDiagonalCorner v x = quarticSampledInput (quarticCornerSample v) x := rfl

theorem quarticCanonicalSample_of_first_one (v : Fin 4 → Fin 2) (h0 : v 0 = 1) :
    quarticCanonicalSample v =
      quarticPermuteSample (quarticWordPermutation (quarticTailSortWord v)) (quarticCornerSample v) := by
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext k
    fin_cases k <;> rfl
  have hf (z : Fin 2) : z = 0 ∨ z = 1 := by fin_cases z <;> simp
  rcases hf (v 1) with h1 | h1 <;>
    rcases hf (v 2) with h2 | h2 <;>
      rcases hf (v 3) with h3 | h3
  all_goals
    rw [h0, h1, h2, h3] at hv
    rw [hv]
    decide

theorem quarticCanonicalSample_of_first_zero (v : QuarticNonconstantCorner) (h0 : v.val 0 = 0) :
    quarticCanonicalSample v.val =
      quarticPermuteSample (quarticWordPermutation (quarticPostExchangeWord v.val))
        (quarticSwapSample (quarticPreExchangeSample v.val)) := by
  have hv : v.val = ![v.val 0, v.val 1, v.val 2, v.val 3] := by
    funext k
    fin_cases k <;> rfl
  have hf (z : Fin 2) : z = 0 ∨ z = 1 := by fin_cases z <;> simp
  rcases hf (v.val 1) with h1 | h1 <;>
    rcases hf (v.val 2) with h2 | h2 <;>
      rcases hf (v.val 3) with h3 | h3
  all_goals first
    | (exfalso; apply v.property; funext k; fin_cases k <;> assumption)
    | (rw [h0, h1, h2, h3] at hv; rw [hv]; decide)

theorem quarticCorner_first_zero_of_ne_one (v : Fin 4 → Fin 2) (h : v 0 ≠ 1) : v 0 = 0 := by
  have hlt := (v 0).isLt
  apply Fin.ext
  simp only [Fin.val_zero]
  omega

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticRawCornerFactor (a b : QuarticNonconstantCorner → Fin W.outputDim)
    (v : QuarticNonconstantCorner) (x : Fin 2 → ℤ) : ℂ :=
  W.eval (a v) (quarticDiagonalCorner v.val x) *
    star (W.eval (b v) (quarticSampledInput (quarticCanonicalSample v.val) x))

theorem quarticRawCornerFactor_norm (a b : QuarticNonconstantCorner → Fin W.outputDim)
    (v : QuarticNonconstantCorner) (x : Fin 2 → ℤ) : ‖W.quarticRawCornerFactor a b v x‖ ≤ 1 := by
  rw [quarticRawCornerFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

noncomputable def quarticCornerExchangeFactor
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : QuarticNonconstantCorner → Fin W.outputDim)
    (v : QuarticNonconstantCorner) (x : Fin 2 → ℤ) : ℂ :=
  if v.val 0 = 1 then W.quarticRawCornerFactor a b v x else
    complexCrossContraction
      (W.eval (a v) (quarticDiagonalCorner v.val x))
      (W.eval (b v) (quarticSampledInput (quarticCanonicalSample v.val) x))
      (fun i => W.eval i (quarticSampledInput (quarticPreExchangeSample v.val) x))
      (fun j => W.eval j (quarticSampledInput (quarticSwapSample (quarticPreExchangeSample v.val)) x))
      (fun i j => G (quarticPreExchangeSample v.val) i j x)

theorem quarticCornerExchangeFactor_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : QuarticNonconstantCorner → Fin W.outputDim) (v : QuarticNonconstantCorner)
    (x : Fin 2 → ZMod N) :
    ‖W.quarticCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  by_cases hv : v.val 0 = 1
  · rw [quarticCornerExchangeFactor, ite_eq_left hv]
    exact (W.quarticRawCornerFactor_norm a b v _).trans hQ
  · rw [quarticCornerExchangeFactor, ite_eq_right hv]
    have h := norm_complexCrossContraction_le_card
      (W.eval (a v) (quarticDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (W.eval (b v) (quarticSampledInput (quarticCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i => W.eval i (quarticSampledInput (quarticPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j => W.eval j (quarticSampledInput (quarticSwapSample (quarticPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j => G (quarticPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (W.norm_eval _ _) (W.norm_eval _ _) (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun i j => hG _ i j x)
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem quarticCornerExchangeFactor_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : QuarticNonconstantCorner → Fin W.outputDim) (v : QuarticNonconstantCorner) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRawCornerFactor a b v (fun k => ((x k).val : ℤ)) -
        W.quarticCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 2 * ε := by
  by_cases hv : v.val 0 = 1
  · simpa [quarticCornerExchangeFactor, hv] using mul_nonneg (sq_nonneg (W.outputDim : ℝ)) hε
  · simp only [quarticCornerExchangeFactor, ite_eq_right hv, quarticRawCornerFactor]
    have h := mean_complexCrossContraction_error_le_card
      (fun x : Fin 2 → ZMod N => W.eval (a v) (quarticDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (fun x => W.eval (b v) (quarticSampledInput (quarticCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i x => W.eval i (quarticSampledInput (quarticPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j x => W.eval j (quarticSampledInput (quarticSwapSample (quarticPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j x => G (quarticPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun _ => W.unit_eval _) (fun _ => W.unit_eval _)
      (fun _ _ => W.norm_eval _ _) (fun _ _ => W.norm_eval _ _) (herr (quarticPreExchangeSample v.val))
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

abbrev QuarticCornerBlock := Fin 4 ⊕ (Fin 6 ⊕ (Fin 4 ⊕ Unit))

def quarticBlockAssignment : QuarticCornerBlock → (Fin 4 → Fin 2) :=
  Sum.elim ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
    (Sum.elim ![![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, 0, 1],
        ![0, 1, 1, 0], ![0, 1, 0, 1], ![0, 0, 1, 1]]
      (Sum.elim ![![1, 1, 1, 0], ![1, 1, 0, 1], ![1, 0, 1, 1], ![0, 1, 1, 1]]
        (fun _ => ![1, 1, 1, 1])))

theorem quarticBlockAssignment_nonzero (z : QuarticCornerBlock) :
    quarticBlockAssignment z ≠ fun _ => 0 := by
  rcases z with z | z
  · fin_cases z <;> decide
  rcases z with z | z
  · fin_cases z <;> decide
  rcases z with z | z
  · fin_cases z <;> decide
  cases z
  decide

def quarticBlockCorner (z : QuarticCornerBlock) : QuarticNonconstantCorner :=
  ⟨quarticBlockAssignment z, quarticBlockAssignment_nonzero z⟩

theorem quarticBlockCorner_injective : Function.Injective quarticBlockCorner := by decide

noncomputable def quarticBlockEquiv : QuarticCornerBlock ≃ QuarticNonconstantCorner :=
  Equiv.ofBijective quarticBlockCorner
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨quarticBlockCorner_injective, by simp [QuarticCornerBlock]⟩)

theorem quarticBlockCorner_canonical (z : QuarticCornerBlock) :
    quarticCanonicalSample (quarticBlockCorner z).val =
      Sum.elim (fun _ : Fin 4 => ![0, 1, 1, 1])
        (Sum.elim (fun _ : Fin 6 => ![0, 0, 1, 1])
          (Sum.elim (fun _ : Fin 4 => ![0, 0, 0, 1])
            (fun _ : Unit => ![0, 0, 0, 0]))) z := by
  rcases z with z | z
  · fin_cases z <;> decide
  rcases z with z | z
  · fin_cases z <;> decide
  rcases z with z | z
  · fin_cases z <;> decide
  cases z
  decide

noncomputable def quarticFifteenMerge {I : Type*} (a : Fin 4 → I) (b : Fin 6 → I)
    (c : Fin 4 → I) (d : I) (v : QuarticNonconstantCorner) : I :=
  Sum.elim a (Sum.elim b (Sum.elim c (fun _ => d))) (quarticBlockEquiv.symm v)

theorem quarticFifteenMerge_block {I : Type*} (a : Fin 4 → I) (b : Fin 6 → I)
    (c : Fin 4 → I) (d : I) (z : QuarticCornerBlock) :
    quarticFifteenMerge a b c d (quarticBlockCorner z) =
      Sum.elim a (Sum.elim b (Sum.elim c (fun _ => d))) z := by
  change Sum.elim a (Sum.elim b (Sum.elim c (fun _ => d)))
    (quarticBlockEquiv.symm (quarticBlockEquiv z)) = _
  rw [Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticSymmetricFifteen (a : QuarticNonconstantCorner → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (quarticSampledInput (quarticCanonicalSample v.val) x))

theorem quarticSymmetricFifteen_norm (a : QuarticNonconstantCorner → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quarticSymmetricFifteen a x‖ ≤ 1 := by
  rw [quarticSymmetricFifteen, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem quarticSymmetricFifteen_unit (x : Fin 2 → ℤ) :
    ∑ a : QuarticNonconstantCorner → Fin W.outputDim, ‖W.quarticSymmetricFifteen a x‖ ^ 2 = 1 := by
  simp only [quarticSymmetricFifteen, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : QuarticNonconstantCorner, ∑ a : Fin W.outputDim,
        ‖W.eval a (quarticSampledInput (quarticCanonicalSample v.val) x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem quarticMixedFifteen_cross_symmetric
    (a b : QuarticNonconstantCorner → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.quarticMixedFifteen a x * star (W.quarticSymmetricFifteen b x) =
      star (∏ v, W.quarticRawCornerFactor a b v x) := by
  simp only [quarticMixedFifteen, quarticSymmetricFifteen, quarticRawCornerFactor,
    Finset.prod_mul_distrib, star_prod, star_mul, star_star]
  ring

noncomputable def quarticFifteenExchangeProduct
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : QuarticNonconstantCorner → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.quarticCornerExchangeFactor G a b v x)

theorem quarticFifteenExchangeProduct_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : QuarticNonconstantCorner → Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quarticFifteenExchangeProduct G a b (fun k => ((x k).val : ℤ))‖ ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ 15 := by
  rw [quarticFifteenExchangeProduct, norm_star, norm_prod]
  calc
    _ ≤ ∏ _ : QuarticNonconstantCorner, (W.outputDim : ℝ) ^ 2 * B :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun v _ => W.quarticCornerExchangeFactor_norm G hB hG a b v x)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, quarticNonconstantCorner_card]

theorem quarticFifteenExchangeProduct_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : QuarticNonconstantCorner → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticMixedFifteen a (fun k => ((x k).val : ℤ)) *
          star (W.quarticSymmetricFifteen b (fun k => ((x k).val : ℤ))) -
        W.quarticFifteenExchangeProduct G a b (fun k => ((x k).val : ℤ))‖) ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ 15 * (15 * ((W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  have h := mean_prod_error_le
    (fun v (x : Fin 2 → ZMod N) => W.quarticRawCornerFactor a b v (fun k => ((x k).val : ℤ)))
    (fun v (x : Fin 2 → ZMod N) => W.quarticCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))) hQ
    (fun v x => (W.quarticRawCornerFactor_norm a b v _).trans hQ)
    (fun v x => W.quarticCornerExchangeFactor_norm G hB hG a b v x)
    (fun v => W.quarticCornerExchangeFactor_mean_error G hε herr a b v)
  simpa only [W.quarticMixedFifteen_cross_symmetric, quarticFifteenExchangeProduct,
    ← star_sub, norm_star, quarticNonconstantCorner_card, Nat.cast_ofNat] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticWrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (QuarticNonconstantCorner → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticNonconstantCorner → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.quarticDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def quarticCyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (QuarticNonconstantCorner → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticNonconstantCorner → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.quarticWrappedDiagonalCorrection N F a b x

theorem quarticWrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (QuarticNonconstantCorner → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticNonconstantCorner → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
        W.quarticWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.quarticWrappedDiagonalDerivative N a x * star (W.quarticSymmetricFifteen b x) -
        W.quarticWrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.quarticDiagonalDerivative (a.1, k) x * star (W.quarticSymmetricFifteen b x) -
        F (a.1, k) b x‖ := by
    have heq : W.quarticWrappedDiagonalDerivative N a x * star (W.quarticSymmetricFifteen b x) -
        W.quarticWrappedDiagonalCorrection N F a b x =
        ∑ k, W.quarticDiagonalWrapCoefficient N a.2 k x *
          (W.quarticDiagonalDerivative (a.1, k) x * star (W.quarticSymmetricFifteen b x) -
            F (a.1, k) b x) := by
      rw [W.quarticWrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [quarticWrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.quarticDiagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.quarticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.quarticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem quarticCyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (QuarticNonconstantCorner → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticNonconstantCorner → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticCyclicDiagonalDerivative a x * star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
        W.quarticCyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.quarticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))))
    (W.quarticWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.quarticWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (W.quarticDiagonalDerivative_norm a _)).trans
        (W.quarticSymmetricFifteen_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.quarticWrappedDiagonalDerivative_norm N a _)).trans
        (W.quarticSymmetricFifteen_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.quarticCyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.quarticWrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [quarticCyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem exists_quarticCyclicDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (QuarticNonconstantCorner → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
          ((p + q + e + C) ^ C) (W.quarticCyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_quarticDiagonalWrapCoefficient_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + (X + 6) ^ 2 + 13
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + (v + 6) ^ 2 + 13
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; nlinarith [sq_nonneg (v + 6)]
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    have hs : 0 ≤ (v + 6) ^ 2 := sq_nonneg _
    dsimp [r, v] at *
    linarith
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hpow : (e + 6) ^ 2 ≤ (v + 6) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) 2
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hev : e ≤ v := by dsimp [v]; linarith
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 t
      (W.quarticWrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 t
      (fun x => ∑ k, W.quarticDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := ((Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).raiseStep
    (by norm_num : 1 ≤ 3) (by positivity : 0 ≤ e + 4)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.quarticWrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.quarticCyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, quarticCyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
