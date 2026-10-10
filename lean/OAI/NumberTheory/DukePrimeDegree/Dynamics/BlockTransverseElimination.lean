import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockRootGroup
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCurveExtraction

namespace OAI

/-!
# Removing block directions by actual invariant roots

This is a sequence-level Gaussian elimination. No Lie-subgroup
classification or membership of the entire block group is assumed.
Every correction is a product of the specified within-block roots.
Pivots are eventually nonzero because the matrices tend to the identity.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def BlockZeroPattern {n : ℕ} (P : Finset (Fin n × Fin n)) (g : G n) : Prop :=
  ∀ p ∈ P, g.val p.1 p.2 = 0

lemma blockZeroPattern_translate {n : ℕ} (P : Finset (Fin n × Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ j, (j, b) ∈ P → (j, a) ∈ P)
    {g : G n} (hg : BlockZeroPattern P g) (t : ℝ) :
    BlockZeroPattern P (g * Matrix.SpecialLinearGroup.transvection hab t) := by
  intro p hp
  rw [root_mul_entry, hg p hp]
  by_cases hb : p.2 = b
  · have hz := hg (p.1, a) (hP p.1 (by simpa only [← hb, Prod.mk.eta] using hp))
    simp only [hb, ite_true, hz, zero_mul, add_zero]
  · simp only [hb, ite_false, add_zero]

/-- An elimination schedule records only zeros that must be preserved;
nonzero pivots are supplied locally by convergence to the identity. -/
inductive BlockEliminationChain {n : ℕ} (r : Setoid (Fin n)) :
    Finset (Fin n × Fin n) → Type
  | done {P} : BlockEliminationChain r P
  | step {P} (a b : Fin n) (hab : a ≠ b) (hr : r a b)
      (hP : ∀ j, (j, b) ∈ P → (j, a) ∈ P)
      (tail : BlockEliminationChain r (insert (a, b) P)) : BlockEliminationChain r P

namespace BlockEliminationChain

variable {n : ℕ} {r : Setoid (Fin n)} {P : Finset (Fin n × Fin n)}

def finalEntries : {P : Finset (Fin n × Fin n)} →
    BlockEliminationChain r P → Finset (Fin n × Fin n)
  | P, .done => P
  | _, .step _ _ _ _ _ tail => tail.finalEntries

def append : {P : Finset (Fin n × Fin n)} →
    (c : BlockEliminationChain r P) → BlockEliminationChain r c.finalEntries →
      BlockEliminationChain r P
  | _, .done, d => d
  | _, .step a b hab hr hP tail, d => .step a b hab hr hP (tail.append d)

@[simp] lemma finalEntries_append (c : BlockEliminationChain r P)
    (d : BlockEliminationChain r c.finalEntries) :
    (c.append d).finalEntries = d.finalEntries := by
  induction c with
  | done => rfl
  | step a b hab hr hP tail ih => exact ih d

/-- The correction converges to one, belongs to the actual root-generated
subgroup at every index, and eventually clears the entire schedule. -/
theorem normalize_sequence (c : BlockEliminationChain r P)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hzero : ∀ᶠ k in atTop, BlockZeroPattern P (g k)) :
    ∃ s b : ℕ → G n,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧
      (∀ k, b k ∈ blockRootGroup r) ∧
      ∀ᶠ k in atTop, BlockZeroPattern c.finalEntries (s k) := by
  induction c generalizing g with
  | done =>
      exact ⟨g, fun _ => 1, hg, tendsto_const_nhds, fun _ => (mul_one _).symm,
        fun _ => (blockRootGroup r).one_mem, hzero⟩
  | @step P a b hab hr hP tail ih =>
      let t : ℕ → ℝ := fun k => -(g k).val a b / (g k).val a a
      let u : ℕ → G n := fun k => Matrix.SpecialLinearGroup.transvection hab (t k)
      have hentry (i j : Fin n) : Tendsto (fun k => (g k).val i j) atTop
          (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) := by
        have hc : Continuous (fun h : G n => h.val i j) := by fun_prop
        exact hc.continuousAt.tendsto.comp hg
      have hdiag : Tendsto (fun k => (g k).val a a) atTop (𝓝 1) := by
        simpa only [Matrix.one_apply_eq] using hentry a a
      have hoff : Tendsto (fun k => (g k).val a b) atTop (𝓝 0) := by
        simpa only [Matrix.one_apply_ne hab] using hentry a b
      have ht : Tendsto t atTop (𝓝 0) := by
        simpa only [t, Pi.div_def, Pi.neg_def, neg_zero, zero_div] using
          hoff.neg.div hdiag one_ne_zero
      have hu : Tendsto u atTop (𝓝 1) := by
        simpa only [u, Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
          (continuous_rootTransvection hab).continuousAt.tendsto.comp ht
      have hq : Tendsto (fun k => g k * u k) atTop (𝓝 1) := by
        simpa only [mul_one] using hg.mul hu
      have hnonzero : ∀ᶠ k in atTop, (g k).val a a ≠ 0 :=
        hdiag.eventually_ne one_ne_zero
      have hqzero : ∀ᶠ k in atTop,
          BlockZeroPattern (insert (a, b) P) (g k * u k) := by
        filter_upwards [hzero, hnonzero] with k hk hn
        intro p hp
        rcases Finset.mem_insert.mp hp with hp | hp
        · subst p
          dsimp only [u]
          rw [root_mul_entry]
          simp only [ite_true]
          dsimp only [t]
          field_simp
          ring
        · exact blockZeroPattern_translate P hab hP hk (t k) p hp
      obtain ⟨s, b', hs, hb', he, hmem, hz⟩ := ih _ hq hqzero
      refine ⟨s, fun k => u k * b' k, hs, ?_, ?_, ?_, hz⟩
      · simpa only [mul_one] using hu.mul hb'
      · intro k
        rw [he k, mul_assoc]
      · intro k
        exact (blockRootGroup r).mul_mem (root_mem_blockRootGroup r a b hab hr (t k)) (hmem k)

end BlockEliminationChain
end DukePrimeDegree

end

end OAI
