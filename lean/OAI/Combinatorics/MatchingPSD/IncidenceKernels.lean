import OAI.Combinatorics.MatchingPSD.TableMoments

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

omit [Fintype G] in
lemma sum_smul_eq (g : G) (f : X → ℝ) : ∑ x, f (g • x) = ∑ x, f x :=
  Equiv.sum_comp (MulAction.toPerm g) f

omit [Fintype X] in
lemma sum_group_smul_eq (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (f : X → ℝ) (x : X) : ∑ g : G, f (g • x) = ∑ g : G, f (g • x₀) := by
  obtain ⟨h, rfl⟩ := ht x
  simp_rw [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g => f (g • x₀))

lemma group_smul_sum_card (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (f : X → ℝ) :
    (Fintype.card G : ℝ) * ∑ x, f x =
      (Fintype.card X : ℝ) * ∑ g : G, f (g • x₀) := by
  calc
    _ = ∑ g : G, ∑ x, f (g • x) := by simp only [sum_smul_eq, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x, ∑ g : G, f (g • x) := Finset.sum_comm
    _ = _ := by simp_rw [sum_group_smul_eq x₀ ht, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]

omit [Fintype G] in
lemma invariant_kernel_sum (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : X → X → ℝ) (hK : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    (∑ x, ∑ y, K x y) = (Fintype.card X : ℝ) * ∑ y, K x₀ y := by
  have he (x : X) : ∑ y, K x y = ∑ y, K x₀ y := by
    obtain ⟨g, rfl⟩ := ht x
    rw [← sum_smul_eq g (fun y => K (g • x₀) y)]
    simp_rw [hK]
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma invariant_kernel_double_sum_group (x₀ : X)
    (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : X → X → ℝ) (hK : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    (Fintype.card G : ℝ) * (∑ x, ∑ y, K x y) =
      (Fintype.card X : ℝ) ^ 2 * ∑ g : G, K x₀ (g • x₀) := by
  rw [invariant_kernel_sum x₀ ht K hK]
  have h := group_smul_sum_card x₀ ht (K x₀)
  nlinarith [h]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

omit [DecidableEq X] in
lemma trace_normalized_kernel_sq (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x) :
    Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
      (Matrix.of fun x y => K x y / Fintype.card X)) =
      (∑ x, ∑ y, K x y ^ 2) / (Fintype.card X : ℝ) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hs y x]
  ring

omit [DecidableEq X] in
lemma trace_normalized_invariant_kernel_sq (x₀ : X)
    (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x)
    (hi : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
      (Matrix.of fun x y => K x y / Fintype.card X)) =
      (∑ g : G, K x₀ (g • x₀) ^ 2) / (Fintype.card G : ℝ) := by
  have : Nonempty X := ⟨x₀⟩
  rw [trace_normalized_kernel_sq K hs]
  have h := invariant_kernel_double_sum_group x₀ ht
    (fun x y => K x y ^ 2) (fun g x y => congrArg (fun a : ℝ => a ^ 2) (hi g x y))
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hg : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_div_iff (pow_ne_zero _ hx) hg).mpr
  nlinarith [h]

end KernelTrace

section Incidence
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

noncomputable def incidence (P : X → Z → Prop) : Matrix Z X ℝ :=
  by classical exact fun z x => if P x z then 1 else 0

noncomputable def commonIncidence (P : X → Z → Prop) (x y : X) : ℝ :=
  by classical exact (Fintype.card {z // P x z ∧ P y z} : ℝ)

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_eq (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = ∑ z, incidence P z x * incidence P z y := by
  classical
  simp only [commonIncidence, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : P x z <;> by_cases hy : P y z <;> simp [incidence, hx, hy]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_symm (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = commonIncidence P y x := by
  simp only [commonIncidence_eq, mul_comm]

noncomputable def incidenceKernel (P : X → Z → Prop) (D : ℝ) : Matrix X X ℝ :=
  fun x y => (Fintype.card Z : ℝ) / D ^ 2 * commonIncidence P x y

noncomputable def incidenceOperator (P : X → Z → Prop) (D : ℝ) : Matrix X X ℝ :=
  fun x y => incidenceKernel P D x y / Fintype.card X

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma incidenceKernel_symm (P : X → Z → Prop) (D : ℝ) (x y : X) :
    incidenceKernel P D x y = incidenceKernel P D y x := by
  unfold incidenceKernel
  rw [commonIncidence_symm P x y]

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_eq (P : X → Z → Prop) (D : ℝ) :
    incidenceOperator P D =
      ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) •
        ((incidence P).transpose * incidence P) := by
  ext x y
  simp only [incidenceOperator, incidenceKernel, commonIncidence_eq, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  ring

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_posSemidef (P : X → Z → Prop) (D : ℝ) :
    (incidenceOperator P D).PosSemidef := by
  rw [incidenceOperator_eq]
  apply Matrix.PosSemidef.smul
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (incidence P)
  · positivity

noncomputable def conditionalAverage (P : X → Z → Prop) (E : ℝ) (f : X → ℝ) (z : Z) : ℝ :=
  (∑ x, incidence P z x * f x) / E

omit [DecidableEq X] [DecidableEq Z] in
lemma conditionalAverage_energy [Nonempty X] [Nonempty Z]
    (P : X → Z → Prop) (D : ℝ) (hD : D ≠ 0) (f : X → ℝ) :
    (∑ z, conditionalAverage P ((Fintype.card X : ℝ) * D / Fintype.card Z) f z ^ 2) /
      Fintype.card Z =
    (∑ x, f x * (incidenceOperator P D *ᵥ f) x) / Fintype.card X := by
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hz : (Fintype.card Z : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change _ = (f ⬝ᵥ (incidenceOperator P D *ᵥ f)) / Fintype.card X
  rw [incidenceOperator_eq, Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [conditionalAverage, div_pow, ← Finset.sum_div, smul_eq_mul]
  change (∑ z, ((incidence P *ᵥ f) z) ^ 2) /
    (((Fintype.card X : ℝ) * D) ^ 2 / (Fintype.card Z : ℝ) ^ 2) / Fintype.card Z =
    ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) *
      (∑ z, (incidence P *ᵥ f) z * (incidence P *ᵥ f) z) / Fintype.card X
  simp only [← pow_two]
  field_simp

end Incidence
end MatchingSmoothing

end OAI
