import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

universe uι uκ uβ uV
variable {ι : Type uι} {κ : Type uκ} {β : Type uβ} {V : Type uV}
variable [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℂ V]

/-- The scalar polynomial obtained by feeding a multilinear form vector variables,
with `block i` specifying which vector variable occurs in its `i`th argument. -/
def multilinearPolynomial (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) : MvPolynomial (β × κ) ℂ := by
  classical
  exact ∑ k : ι → κ,
    MvPolynomial.C (L (fun i => e (k i))) *
      ∏ i, MvPolynomial.X (block i, k i)

/-- Evaluation of the multilinear polynomial on arbitrary coordinate assignments. -/
theorem eval_multilinearPolynomial
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) (z : β × κ → ℂ) :
    MvPolynomial.eval z (multilinearPolynomial L e block) =
      L (fun i => ∑ k, z (block i, k) • e k) := by
  classical
  simp only [multilinearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, MvPolynomial.eval_X]
  rw [L.map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [L.map_smul_univ]
  simp only [smul_eq_mul]
  exact mul_comm _ _

/-- With basis coordinates, evaluation is literal evaluation on the chosen vector blocks. -/
theorem eval_multilinearPolynomial_basis
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : Module.Basis κ ℂ V) (block : ι → β) (v : β → V) :
    MvPolynomial.eval (fun z : β × κ => e.repr (v z.1) z.2)
      (multilinearPolynomial L e block) = L (fun i => v (block i)) := by
  rw [eval_multilinearPolynomial]
  simp only [e.sum_repr]

/-- Pointwise vanishing on vector blocks implies the corresponding polynomial identity. -/
theorem multilinearPolynomial_eq_zero
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β)
    (h : ∀ v : β → V, L (fun i => v (block i)) = 0) :
    multilinearPolynomial L e block = 0 := by
  apply MvPolynomial.funext
  intro z
  rw [eval_multilinearPolynomial, map_zero]
  exact h (fun j => ∑ k, z (j, k) • e k)

/-- Conversely, a polynomial identity gives the vector-valued identity by basis evaluation. -/
theorem multilinearPolynomial_eq_zero_iff
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : Module.Basis κ ℂ V) (block : ι → β) :
    multilinearPolynomial L e block = 0 ↔
      ∀ v : β → V, L (fun i => v (block i)) = 0 := by
  constructor
  · intro h v
    rw [← eval_multilinearPolynomial_basis L e block v, h, map_zero]
  · exact multilinearPolynomial_eq_zero L e block

/-- Reindexing the labels by a symmetry of the multilinear form leaves its polynomial unchanged. -/
theorem multilinearPolynomial_perm
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) (σ : Equiv.Perm ι)
    (hσ : ∀ x : ι → V, L (fun i => x (σ i)) = L x) :
    multilinearPolynomial L e (fun i => block (σ i)) =
      multilinearPolynomial L e block := by
  apply MvPolynomial.funext
  intro z
  rw [eval_multilinearPolynomial, eval_multilinearPolynomial]
  exact hσ (fun i => ∑ k, z (block i, k) • e k)

/-- Equal labels make replacing either of two symmetric slots give the same polynomial. -/
theorem multilinearPolynomial_update_eq [DecidableEq ι]
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) (i j : ι) (dst : β)
    (hij : block i = block j)
    (hsym : ∀ x : ι → V, L (fun k => x (Equiv.swap i j k)) = L x) :
    multilinearPolynomial L e (Function.update block i dst) =
      multilinearPolynomial L e (Function.update block j dst) := by
  classical
  have hp := multilinearPolynomial_perm L e (Function.update block i dst)
    (Equiv.swap i j) hsym
  have hlabels :
      (fun k => Function.update block i dst (Equiv.swap i j k)) =
        Function.update block j dst := by
    funext k
    by_cases hi : k = i
    · subst k
      by_cases heq : i = j
      · subst j
        rw [Equiv.swap_apply_left, Function.update_self]
      · simp [heq, Ne.symm heq, hij]
    · by_cases hj : k = j
      · subst k
        simp
      · simp [Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
  rw [hlabels] at hp
  exact hp.symm

/-- The derivative's sum over interchangeable source slots is a scalar multiple of one term. -/
theorem multilinearPolynomial_sum_updates [DecidableEq ι]
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) (s : Finset ι) (j : ι) (dst : β)
    (hlabel : ∀ i ∈ s, block i = block j)
    (hsym : ∀ i ∈ s, ∀ x : ι → V,
      L (fun k => x (Equiv.swap i j k)) = L x) :
    (∑ i ∈ s, multilinearPolynomial L e (Function.update block i dst)) =
      (s.card : ℂ) • multilinearPolynomial L e (Function.update block j dst) := by
  calc
    (∑ i ∈ s, multilinearPolynomial L e (Function.update block i dst)) =
        ∑ _i ∈ s, multilinearPolynomial L e (Function.update block j dst) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact multilinearPolynomial_update_eq L e block i j dst (hlabel i hi) (hsym i hi)
    _ = _ := by
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]

end Problem346

end

end OAI
