import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.TensorPolarization

namespace OAI

noncomputable section

namespace Foulkes.Polarization
open MvPolynomial

def renameRow {a n : ℕ} (σ : Equiv.Perm (Fin a)) : P a n →ₐ[ℂ] P a n :=
  MvPolynomial.rename (fun ij : Fin a × Fin n => (σ ij.1, ij.2))

@[simp] lemma renameRow_comp {a n : ℕ} (σ τ : Equiv.Perm (Fin a)) (f : P a n) :
    renameRow σ (renameRow τ f) = renameRow (σ * τ) f := by
  simp [renameRow, rename_rename, Function.comp_def, Equiv.Perm.mul_apply]

@[simp] lemma renameRow_rowForm {a n : ℕ} (σ : Equiv.Perm (Fin a)) (i : Fin a)
    (v : Fin n → ℂ) : renameRow σ (rowForm i v) = rowForm (σ i) v := by
  simp [renameRow, rowForm]

lemma renameRow_pureRows {a n j : ℕ} (σ : Equiv.Perm (Fin a)) (v : Fin a → Fin n → ℂ) :
    renameRow σ (pureRows j v) = pureRows j (fun i => v (σ.symm i)) := by
  simp only [pureRows, map_prod, map_pow, renameRow_rowForm]
  apply Fintype.prod_equiv σ
  intro i
  simp

lemma renameRow_mem_W {a n j : ℕ} (σ : Equiv.Perm (Fin a)) {f : P a n}
    (hf : f ∈ W a n j) : renameRow σ f ∈ W a n j := by
  have hle : Submodule.span ℂ (Set.range (pureRows (a := a) (n := n) j)) ≤
      (W a n j).comap (renameRow σ).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change renameRow σ (pureRows j v) ∈ W a n j
    rw [renameRow_pureRows]
    exact pureRows_mem _
  apply hle
  rwa [← W_eq_span_pureRows]

@[simp] lemma renameRow_z {a n : ℕ} (σ : Equiv.Perm (Fin a)) (v : Fin n → ℂ) :
    renameRow σ (z (a := a) v) = z v := by
  simp only [z, map_prod, renameRow_rowForm]
  exact Equiv.prod_comp σ (fun i => rowForm i v)

def rowInvariants (a n : ℕ) : Subalgebra ℂ (P a n) where
  carrier := {f | ∀ σ : Equiv.Perm (Fin a), renameRow σ f = f}
  zero_mem' := by intro σ; simp
  add_mem' := by intro f g hf hg σ; simp only [map_add, hf σ, hg σ]
  one_mem' := by intro σ; simp
  mul_mem' := by intro f g hf hg σ; simp only [map_mul, hf σ, hg σ]
  algebraMap_mem' := by intro c σ; simp

def R (a n j : ℕ) : Submodule ℂ (P a n) := W a n j ⊓ (rowInvariants a n).toSubmodule

def A (a n : ℕ) : Subalgebra ℂ (P a n) := Algebra.adjoin ℂ (R a n 1 : Set (P a n))

def average (a n : ℕ) : P a n →ₗ[ℂ] P a n :=
  (a.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin a), (renameRow σ).toLinearMap

lemma average_apply {a n : ℕ} (f : P a n) :
    average a n f = (a.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin a), renameRow σ f := by
  simp [average, LinearMap.sum_apply]

lemma average_invariant {a n : ℕ} (f : P a n) (τ : Equiv.Perm (Fin a)) :
    renameRow τ (average a n f) = average a n f := by
  simp only [average_apply, map_smul, map_sum, renameRow_comp]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => renameRow σ f)

lemma average_mem_R {a n j : ℕ} {f : P a n} (hf : f ∈ W a n j) :
    average a n f ∈ R a n j := by
  constructor
  · rw [average_apply]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro σ _
    exact renameRow_mem_W σ hf
  · exact average_invariant f

lemma average_eq {a n : ℕ} {f : P a n}
    (hf : f ∈ rowInvariants a n) : average a n f = f := by
  change ∀ σ : Equiv.Perm (Fin a), renameRow σ f = f at hf
  have ha : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  simp only [average_apply, hf, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ ha, one_smul]

lemma average_zpow_mul {a n L : ℕ} (v : Fin n → ℂ) (f : P a n) :
    average a n (z v ^ L * f) = z v ^ L * average a n f := by
  simp only [average_apply, map_mul, map_pow, renameRow_z, ← Finset.mul_sum]
  rw [mul_smul_comm]

lemma z_mem_R {a n : ℕ} (v : Fin n → ℂ) : z (a := a) v ∈ R a n 1 := by
  constructor
  · simpa using z_pow_mem (a := a) (L := 1) v
  · exact fun σ => renameRow_z σ v

lemma z_mem_A {a n : ℕ} (v : Fin n → ℂ) : z (a := a) v ∈ A a n :=
  Algebra.subset_adjoin (z_mem_R v)

def invariantPolarizedSpan (a n j L : ℕ) : Submodule ℂ (P a n) :=
  Submodule.span ℂ {p | ∃ (v : Fin n → ℂ) (f : P a n),
    f ∈ R a n (j - L) ∧ z v ^ L * f = p}

theorem R_polarization {a n j L : ℕ} (ha : 1 ≤ a) (hj : a * L ≤ j) :
    R a n j = invariantPolarizedSpan a n j L := by
  classical
  apply le_antisymm
  · intro f hf
    have hle : polarizedSpan a n j L ≤
        (invariantPolarizedSpan a n j L).comap (average a n) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, g, hg, rfl⟩
      change average a n (z v ^ L * g) ∈ invariantPolarizedSpan a n j L
      rw [average_zpow_mul]
      exact Submodule.subset_span ⟨v, average a n g, average_mem_R hg, rfl⟩
    have hmem := hle ((W_polarization ha hj).le hf.1)
    change average a n f ∈ invariantPolarizedSpan a n j L at hmem
    rwa [average_eq hf.2] at hmem
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, f, hf, rfl⟩
    constructor
    · apply (W_polarization ha hj).ge
      exact Submodule.subset_span ⟨v, f, hf.1, rfl⟩
    · intro σ
      simp only [map_mul, map_pow, renameRow_z, hf.2 σ]

def lowDegreeModule (a n : ℕ) : Submodule (A a n) (P a n) :=
  Submodule.span (A a n) {f | ∃ k : ℕ, k < a ∧ f ∈ R a n k}

theorem module_generation {a n : ℕ} (ha : 1 ≤ a) (j : ℕ) {f : P a n}
    (hf : f ∈ R a n j) : f ∈ lowDegreeModule a n := by
  classical
  induction j using Nat.strong_induction_on generalizing f with
  | h j ih =>
    by_cases hj : j < a
    · exact Submodule.subset_span ⟨j, hj, hf⟩
    have hja : a ≤ j := Nat.le_of_not_lt hj
    have hsub : j - 1 < j := by omega
    have hle : invariantPolarizedSpan a n j 1 ≤ (lowDegreeModule a n).restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, g, hg, rfl⟩
      change z v ^ 1 * g ∈ lowDegreeModule a n
      rw [pow_one]
      exact (lowDegreeModule a n).smul_mem (⟨z v, z_mem_A v⟩ : A a n) (ih (j - 1) hsub hg)
    apply hle
    apply (R_polarization ha (by simpa using hja)).le hf

lemma A_le_rowInvariants (a n : ℕ) : A a n ≤ rowInvariants a n := by
  apply Algebra.adjoin_le
  intro f hf
  exact hf.2

lemma AComponent_le_R (a n j : ℕ) :
    W a n j ⊓ (A a n).toSubmodule ≤ R a n j := by
  intro f hf
  exact ⟨hf.1, A_le_rowInvariants a n hf.2⟩

end Foulkes.Polarization

end

end OAI
