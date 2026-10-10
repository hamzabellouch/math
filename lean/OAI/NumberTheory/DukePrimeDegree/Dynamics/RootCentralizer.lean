import OAI.NumberTheory.DukePrimeDegree.Dynamics.QuotientReturn
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ExceptionalPolynomial

namespace OAI

/-!
# The root-pair centralizer

The common centralizer of opposite elementary root groups has a scalar
block on their two coordinates. This gives the concrete matrix form
needed to apply the integral scalar-block obstruction to orbit returns.
-/

noncomputable section
open Set Matrix
open scoped Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

def rootPairCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Subgroup (G n) :=
  Subgroup.centralizer {Matrix.SpecialLinearGroup.transvection hij 1,
    Matrix.SpecialLinearGroup.transvection hij.symm 1}

lemma rootPairCentralizer_isClosed {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    IsClosed (rootPairCentralizer hij : Set (G n)) :=
  Set.isClosed_centralizer _

lemma mem_rootPairCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g ∈ rootPairCentralizer hij ↔
      g * Matrix.SpecialLinearGroup.transvection hij 1 =
        Matrix.SpecialLinearGroup.transvection hij 1 * g ∧
      g * Matrix.SpecialLinearGroup.transvection hij.symm 1 =
        Matrix.SpecialLinearGroup.transvection hij.symm 1 * g := by
  constructor
  · intro h
    have hc := Subgroup.mem_centralizer_iff.mp h
    exact ⟨(hc _ (by simp)).symm, (hc _ (by simp)).symm⟩
  · rintro ⟨h₁, h₂⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    rcases (Set.mem_insert_iff.mp ha) with h | h
    · subst a
      exact h₁.symm
    · rw [Set.mem_singleton_iff] at h
      subst a
      exact h₂.symm

lemma rootPairCentralizer_entries {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : g ∈ rootPairCentralizer hij) :
    g.val i i = g.val j j ∧ g.val i j = 0 ∧ g.val j i = 0 ∧
      ∀ r : Fin n, r ≠ i → r ≠ j →
        g.val r i = 0 ∧ g.val r j = 0 ∧ g.val i r = 0 ∧ g.val j r = 0 := by
  obtain ⟨h₁, h₂⟩ := (mem_rootPairCentralizer hij g).mp hg
  obtain ⟨hc₁, hr₁, hd⟩ := (commutes_root_one_iff hij g).mp h₁
  obtain ⟨hc₂, hr₂, _⟩ := (commutes_root_one_iff hij.symm g).mp h₂
  exact ⟨hd, hc₂ i hij, hc₁ j hij.symm,
    fun r hri hrj => ⟨hc₁ r hri, hc₂ r hrj, hr₂ r hri, hr₁ r hrj⟩⟩

/-- Reindexing the common centralizer of opposite roots separates its
scalar two-dimensional block from the complementary matrix. -/
theorem rootPairCentralizer_block {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (g : G n) (hg : g ∈ rootPairCentralizer hij) :
    ∃ c : ℝ, ∃ B : Matrix (Fin m) (Fin m) ℝ,
      Matrix.reindex e e g.val =
        Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B := by
  let i := e.symm (Sum.inl 0)
  let j := e.symm (Sum.inl 1)
  let c := g.val i i
  let B : Matrix (Fin m) (Fin m) ℝ := fun r s => g.val (e.symm (Sum.inr r)) (e.symm (Sum.inr s))
  obtain ⟨hd, h01, h10, ho⟩ := rootPairCentralizer_entries hij g hg
  have hn (r : Fin m) : e.symm (Sum.inr r) ≠ i ∧ e.symm (Sum.inr r) ≠ j := by
    constructor
    all_goals intro heq; apply_fun e at heq; simp [i, j] at heq
  refine ⟨c, B, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · fin_cases r <;> fin_cases s
    · rfl
    · simpa [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal, i, j] using h01
    · simpa [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal, i, j] using h10
    · simpa [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal, c, i, j] using hd.symm
  · fin_cases r
    · exact (ho _ (hn s).1 (hn s).2).2.2.1
    · exact (ho _ (hn s).1 (hn s).2).2.2.2
  · fin_cases s
    · exact (ho _ (hn r).1 (hn r).2).1
    · exact (ho _ (hn r).1 (hn r).2).2.1
  · rfl

/-- The scalar-block obstruction after the coordinate reindexing used for
an arbitrary opposite-root pair in the arithmetic quotient. -/
theorem reindexed_integral_scalar_block {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (q : G n) (γ : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (c : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (hsep : B.charpoly.Separable)
    (hblock : Matrix.reindex e e
      (q⁻¹ * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * q).val =
        Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B) :
    c = 1 ∨ c = -1 := by
  have hcancel : q.val * (q⁻¹).val = 1 := by
    change (q * q⁻¹).val = 1
    simp
  have hconj :
      (q⁻¹ * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * q).val.charpoly =
        γ.val.charpoly.map (algebraMap ℤ ℝ) := by
    change ((q⁻¹).val * γ.val.map (Int.castRingHom ℝ) * q.val).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hcancel, one_mul, Matrix.charpoly_map]
    rfl
  have hpoly : γ.val.charpoly.map (algebraMap ℤ ℝ) =
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B).charpoly := by
    rw [← hconj, ← Matrix.charpoly_reindex e]
    exact congrArg Matrix.charpoly hblock
  apply integer_sl_double_factor γ c B.charpoly B.charpoly_monic hsep
  rw [hpoly, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  simp [pow_two]

end DukePrimeDegree

end

end OAI
