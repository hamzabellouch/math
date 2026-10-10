import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupedGoodWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectPrefixTuples

namespace OAI

/-! # Paths for individual blocks of a successful sampled word

The initial point of each block is the exact product of all preceding
blocks. This is needed when successive blocks use different profile labels.
-/

namespace PolycyclicRecognition

variable {G : Type*} [Group G]

/-- Restrict successful sheets to any complete block, retaining its true
starting state rather than restarting the full word at the identity. -/
theorem WordSheetsGood.ofFn_block {A : Set G} {x : G} {h : ℕ}
    (u : ℕ → List G)
    (hg : WordSheetsGood A x (List.ofFn (fun j : Fin h => u j.val)).flatten)
    (i : Fin h) :
    WordSheetsGood A (x * wordPrefix (fun j => (u j).prod) i.val) (u i.val) := by
  induction h generalizing x u with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    rw [List.ofFn_succ, List.flatten_cons] at hg
    obtain ⟨hfirst, htail⟩ := (wordSheetsGood_append_iff A x _ _).mp hg
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.val_zero, wordPrefix_zero, mul_one] using hfirst
    · simp only [Fin.val_succ, wordPrefix_succ_left, ← mul_assoc]
      exact ih (fun k => u (k + 1)) htail j

variable [PseudoMetricSpace G] [IsTopologicalGroup G]
  {I : Type*} (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1) (d₀ : G) (r : ℝ)

/-- Each block has its own controlled path through the good sheets. The
whole-word success condition supplies all the block starting states. -/
theorem successful_block_path
    (A S : Set G) (P : I → ℝ → Prop) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i b, P i b → n * f i b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b t ∈ S)
    {h : ℕ} (u : ℕ → List (I × ℝ)) (n : G)
    (hparam : ∀ i : Fin h, ∀ z ∈ u i.val, P z.1 z.2)
    (hgood : WordSheetsGood A n
      (List.ofFn (fun j : Fin h => (u j.val).map (fun z => f z.1 z.2))).flatten)
    (i : Fin h) :
    let blockProduct := fun j => ((u j).map (fun z => f z.1 z.2)).prod
    ∃ γ : Path (n * wordPrefix blockProduct i.val * d₀)
      ((n * wordPrefix blockProduct i.val) * blockProduct i.val * d₀),
      PathMetricBound γ (L * 2 ^ (u i.val).length) (κ * 2 ^ (u i.val).length) ∧
      ∀ t, γ t ∈ S := by
  dsimp only
  let x := n * wordPrefix (fun j => ((u j).map (fun z => f z.1 z.2)).prod) i.val
  have hg : WordSheetsGood A x ((u i.val).map (fun z => f z.1 z.2)) :=
    hgood.ofFn_block (fun j => (u j).map (fun z => f z.1 z.2)) i
  obtain ⟨hb, hrange⟩ := supportWordPath_good_bound d f hd hf hd₀ hf₀ d₀ r
    A S P hL hκ hbase hstep (u i.val) (hparam i) x hg
  exact ⟨supportWordPath d f hd hf hd₀ hf₀ d₀ r (u i.val) x, hb, hrange⟩

end PolycyclicRecognition

end OAI
