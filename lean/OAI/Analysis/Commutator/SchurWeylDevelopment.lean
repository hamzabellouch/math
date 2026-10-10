import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def tensorPower (A : Matrix I I 𝕜) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => ∏ j, A (a j) (b j)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
@[simp] lemma tensorPower_apply (A : Matrix I I 𝕜) (a b : J → I) :
    tensorPower A a b = ∏ j, A (a j) (b j) := rfl

omit [Fintype I] [DecidableEq J] in
lemma tensorPower_diagonal (d : I → 𝕜) :
    tensorPower (J := J) (Matrix.diagonal d) =
      Matrix.diagonal (fun a : J → I => ∏ j, d (a j)) := by
  classical
  ext a b
  by_cases h : a = b
  · subst b; simp
  · have hex : ∃ j, a j ≠ b j := Function.ne_iff.mp h
    obtain ⟨j, hj⟩ := hex
    rw [Matrix.diagonal_apply_ne _ h]
    change (∏ j, Matrix.diagonal d (a j) (b j)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ hj

omit [Fintype I] [DecidableEq J] in
@[simp] lemma tensorPower_one : tensorPower (J := J) (1 : Matrix I I 𝕜) = 1 := by
  rw [← Matrix.diagonal_one, tensorPower_diagonal]
  simp

omit [DecidableEq I] in
lemma tensorPower_mul (A B : Matrix I I 𝕜) :
    tensorPower (J := J) (A * B) = tensorPower A * tensorPower B := by
  classical
  ext a b
  simp only [tensorPower_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

def permutationMatrix (σ : Equiv.Perm J) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => if a = b ∘ σ.symm then 1 else 0

lemma tensorPower_commute_permutation (A : Matrix I I 𝕜) (σ : Equiv.Perm J) :
    tensorPower A * permutationMatrix σ = permutationMatrix σ * tensorPower A := by
  classical
  ext a b
  simp only [Matrix.mul_apply, permutationMatrix, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (b ∘ σ.symm)]
  · rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (a ∘ σ)]
    · have ha : a = (a ∘ σ) ∘ σ.symm := by ext j; simp
      rw [ite_eq_left ha, one_mul]
      dsimp [tensorPower]
      simpa using (Equiv.prod_comp σ.symm fun j => A (a (σ j)) (b j))
    · intro c _ hc
      have hn : a ≠ c ∘ σ.symm := by
        intro he
        apply hc
        ext j
        simpa using congrFun he (σ j) |>.symm
      simp [hn]
    · simp
  · intro c _ hc
    simp [hc]
  · simp

def assignmentMatrix (b c : J → I) : Matrix I I 𝕜 :=
  fun r s => ∑ j, if s = b j ∧ r = c j then 1 else 0

omit [Fintype I] [DecidableEq J] in
lemma assignmentMatrix_column (b c : J → I) (hb : Function.Injective b) (r : I) (j : J) :
    assignmentMatrix (𝕜 := 𝕜) b c r (b j) = if r = c j then 1 else 0 := by
  classical
  unfold assignmentMatrix
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have hn : b j ≠ b k := fun h => hk (hb h).symm
    simp [hn]
  · simp

omit [Fintype I] [DecidableEq J] in
lemma tensorPower_assignment (b c : J → I) (hb : Function.Injective b) (a : J → I) :
    tensorPower (assignmentMatrix (𝕜 := 𝕜) b c) a b = if a = c then 1 else 0 := by
  classical
  simp only [tensorPower_apply, assignmentMatrix_column b c hb]
  by_cases h : a = c
  · subst c; simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma eq_zero_of_commute_of_column_zero (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) 𝕜)
    (hS : ∀ A : Matrix I I 𝕜, S * tensorPower A = tensorPower A * S)
    (hzero : ∀ a, S a b = 0) : S = 0 := by
  classical
  ext a c
  have he := congrArg (fun X : Matrix (J → I) (J → I) 𝕜 => X a b)
    (hS (assignmentMatrix b c))
  simp only [Matrix.mul_apply, tensorPower_assignment b c hb, hzero, mul_zero,
    Finset.sum_const_zero, mul_ite, mul_one] at he
  simpa using he

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma exists_permutation_of_range (a b : J → I) (hb : Function.Injective b)
    (h : ∀ j, ∃ k, a k = b j) :
    ∃ σ : Equiv.Perm J, a = b ∘ σ.symm := by
  classical
  choose g hg using h
  have hgi : Function.Injective g := by
    intro j k he
    apply hb
    rw [← hg j, ← hg k, he]
  let σ : Equiv.Perm J := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hgi, rfl⟩)
  refine ⟨σ, funext fun j => ?_⟩
  have he := hg (σ.symm j)
  change a (σ (σ.symm j)) = b (σ.symm j) at he
  simpa using he

lemma column_support_permutations [Nontrivial 𝕜]
    (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) 𝕜)
    (hS : ∀ d : I → 𝕜, S * tensorPower (Matrix.diagonal d) =
      tensorPower (Matrix.diagonal d) * S)
    (a : J → I) (ha : S a b ≠ 0) :
    ∃ σ : Equiv.Perm J, a = b ∘ σ.symm := by
  classical
  apply exists_permutation_of_range a b hb
  intro j
  by_contra hn
  push Not at hn
  let d : I → 𝕜 := fun r => if r = b j then 0 else 1
  have hd₁ : (∏ k, d (a k)) = 1 := by simp [d, hn]
  have hd₀ : (∏ k, d (b k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [d])
  have he := congrArg (fun X : Matrix (J → I) (J → I) 𝕜 => X a b) (hS d)
  rw [tensorPower_diagonal] at he
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hd₀, hd₁, mul_zero, one_mul] at he
  exact ha he.symm

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma permutation_label_injective (b : J → I) (hb : Function.Injective b) :
    Function.Injective (fun σ : Equiv.Perm J => b ∘ σ.symm) := by
  intro σ ρ he
  have hs : σ.symm = ρ.symm := by
    ext j
    exact hb (congrFun he j)
  exact congrArg Equiv.symm hs

theorem commutant_tensorPower [Nontrivial 𝕜]
    (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) 𝕜)
    (hS : ∀ A : Matrix I I 𝕜, S * tensorPower A = tensorPower A * S) :
    S = ∑ σ : Equiv.Perm J, S (b ∘ σ.symm) b • permutationMatrix σ := by
  classical
  let Q : Matrix (J → I) (J → I) 𝕜 := ∑ σ : Equiv.Perm J, S (b ∘ σ.symm) b • permutationMatrix σ
  have hQ : ∀ A : Matrix I I 𝕜, Q * tensorPower A = tensorPower A * Q := by
    intro A
    dsimp [Q]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul,
      tensorPower_commute_permutation]
  have hcol : ∀ a, S a b = Q a b := by
    intro a
    by_cases ha : S a b = 0
    · dsimp [Q]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, permutationMatrix]
      rw [ha]
      symm
      apply Finset.sum_eq_zero
      intro σ _
      split_ifs with h
      · rw [← h, ha, zero_mul]
      · exact mul_zero _
    · obtain ⟨σ, rfl⟩ := column_support_permutations b hb S (fun d => hS _) a ha
      dsimp [Q]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, permutationMatrix]
      rw [Finset.sum_eq_single σ]
      · simp
      · intro ρ _ hρ
        have hn : b ∘ σ.symm ≠ b ∘ ρ.symm := fun he =>
          hρ ((permutation_label_injective b hb he).symm)
        simp [hn]
      · simp
  have hz : S - Q = 0 := eq_zero_of_commute_of_column_zero b hb _
    (fun A => by rw [Matrix.sub_mul, Matrix.mul_sub, hS A, hQ A])
    (fun a => by simp [hcol a])
  exact sub_eq_zero.mp hz

lemma complex_unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hi : Set.InjOn (fun x : ℝ => (Circle.exp x : ℂ)) (Set.Icc 0 1) :=
    Circle.coe_injective.comp_injOn (Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three]))
  exact ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image hi).mono
    (by rintro _ ⟨x, _, rfl⟩; exact Circle.norm_coe _)

lemma diagonal_unitary (d : I → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    Matrix.diagonal d ∈ unitary (Matrix I I ℂ) := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  simp [Pi.star_apply, RCLike.star_def, Complex.mul_conj', hd]

lemma commute_diagonal_of_unitary
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S) (d : I → ℂ) :
    S * tensorPower (Matrix.diagonal d) = tensorPower (Matrix.diagonal d) * S := by
  classical
  rw [tensorPower_diagonal]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  let p : MvPolynomial I ℂ := MvPolynomial.C (S a b) * ∏ j, MvPolynomial.X (b j)
  let q : MvPolynomial I ℂ := (∏ j, MvPolynomial.X (a j)) * MvPolynomial.C (S a b)
  have hpq : p = q := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1})
      (fun _ => complex_unit_circle_infinite)
    intro z hz
    have he := congrArg (fun X : Matrix (J → I) (J → I) ℂ => X a b)
      (hS ⟨Matrix.diagonal z, diagonal_unitary z (fun i => hz i (Set.mem_univ _))⟩)
    rw [tensorPower_diagonal] at he
    simpa [p, q] using he
  have he := congrArg (MvPolynomial.eval d) hpq
  simpa [p, q] using he

lemma commute_hermitian_of_unitary
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S)
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    S * tensorPower A = tensorPower A * S := by
  have hU : Commute S (tensorPower (hA.eigenvectorUnitary : Matrix I I ℂ)) :=
    hS hA.eigenvectorUnitary
  have hD : Commute S (tensorPower (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))) :=
    commute_diagonal_of_unitary S hS _
  have hUs : Commute S (tensorPower ((star hA.eigenvectorUnitary : unitary (Matrix I I ℂ)) : Matrix I I ℂ)) :=
    hS (star hA.eigenvectorUnitary)
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simpa only [tensorPower_mul, Unitary.coe_star] using ((hU.mul_right hD).mul_right hUs).eq

omit [DecidableEq I] in
lemma commute_complexification
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ A : Matrix I I ℂ, A.IsHermitian → S * tensorPower A = tensorPower A * S)
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (z : ℂ) :
    S * tensorPower (A + z • B) = tensorPower (A + z • B) * S := by
  classical
  ext a b
  let P (r s : I) : MvPolynomial Unit ℂ := MvPolynomial.C (A r s) +
    MvPolynomial.X () * MvPolynomial.C (B r s)
  let p : MvPolynomial Unit ℂ := ∑ c : J → I,
    MvPolynomial.C (S a c) * ∏ j, P (c j) (b j)
  let q : MvPolynomial Unit ℂ := ∑ c : J → I,
    (∏ j, P (a j) (c j)) * MvPolynomial.C (S c b)
  have hpq : p = q := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro x hx
    obtain ⟨t, ht⟩ := hx () (Set.mem_univ _)
    have hs : (A + (t : ℂ) • B).IsHermitian := by
      exact hA.add (hB.smul (by change star (t : ℂ) = (t : ℂ); simp))
    have he := congrArg (fun X : Matrix (J → I) (J → I) ℂ => X a b) (hS _ hs)
    simpa [p, q, P, Matrix.mul_apply, tensorPower, ← ht] using he
  have he := congrArg (MvPolynomial.eval (fun _ => z)) hpq
  simpa [p, q, P, Matrix.mul_apply, tensorPower] using he

lemma commute_all_of_unitary
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S) (A : Matrix I I ℂ) :
    S * tensorPower A = tensorPower A * S := by
  have hre : (realPart A : Matrix I I ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (realPart A).property
  have him : (imaginaryPart A : Matrix I I ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (imaginaryPart A).property
  simpa only [realPart_add_I_smul_imaginaryPart] using
    commute_complexification S (commute_hermitian_of_unitary S hS)
      (realPart A) (imaginaryPart A) hre him Complex.I

theorem commutant_unitary_tensorPower (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S) :
    S = ∑ σ : Equiv.Perm J, S (b ∘ σ.symm) b • permutationMatrix σ :=
  commutant_tensorPower b hb S (commute_all_of_unitary S hS)

end Kadison.SchurWeyl
end

end OAI
