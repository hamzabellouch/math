import OAI.Analysis.KadisonKastler.CountableUnitaryAssembly

namespace OAI

/-! # Conjugacy on a countable Hilbert direct sum

The decomposition and reconstruction properties below describe a given
block decomposition. They do not assert that an arbitrary algebra admits
one. Coordinate conjugacies assemble without changing their uniform bound.
-/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def RepresentsBlockOperators (F : ∀ n, E n →L[ℂ] E n)
    (T : lp E 2 →L[ℂ] lp E 2) : Prop :=
  ∀ f n, (T f) n = F n (f n)

omit [∀ n, CompleteSpace (E n)] in
theorem RepresentsBlockOperators.unique {F : ∀ n, E n →L[ℂ] E n}
    {T S : lp E 2 →L[ℂ] lp E 2}
    (hT : RepresentsBlockOperators F T) (hS : RepresentsBlockOperators F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  exact (hT f n).trans (hS f n).symm

structure BlockAlgebraDecomposition (M : ∀ n, VonNeumannAlgebra (E n))
    (A : VonNeumannAlgebra (lp E 2)) : Prop where
  decompose : ∀ T ∈ A, ∃ F : ∀ n, E n →L[ℂ] E n,
    (∀ n, ‖F n‖ ≤ ‖T‖) ∧ (∀ n, F n ∈ M n) ∧ RepresentsBlockOperators F T
  reconstruct : ∀ (F : ∀ n, E n →L[ℂ] E n) (C : ℝ), 0 ≤ C →
    (∀ n, ‖F n‖ ≤ C) → (∀ n, F n ∈ M n) →
    ∃ T ∈ A, RepresentsBlockOperators F T

theorem l2FiberUnitary_star_apply (U : ∀ n, unitary (E n →L[ℂ] E n))
    (f : lp E 2) (n : ℕ) :
    ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2) f) n =
      (star (U n) : E n →L[ℂ] E n) (f n) := by
  let g := l2FiberUnitaryApply (fun n => star (U n)) f
  have hug : (l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) g = f := by
    apply lp.ext
    funext i
    exact congrArg (fun T : E i →L[ℂ] E i => T (f i)) (U i).property.2
  have h := congrArg (fun T : lp E 2 →L[ℂ] lp E 2 => T g)
    (l2FiberUnitary U).property.1
  calc
    ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2) f) n =
        ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2)
          ((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) g)) n := by rw [hug]
    _ = g n := congrArg (fun x : lp E 2 => x n) h
    _ = _ := rfl

theorem blockOperator_conjugation_inclusion
    {M N : ∀ n, VonNeumannAlgebra (E n)} {A B : VonNeumannAlgebra (lp E 2)}
    (hA : BlockAlgebraDecomposition M A) (hB : BlockAlgebraDecomposition N B)
    (U : ∀ n, unitary (E n →L[ℂ] E n))
    (hU : ∀ n, Conjugates (U n) (M n) (N n)) :
    ∀ T ∈ A, unitaryConj (l2FiberUnitary U) T ∈ B := by
  intro T hT
  obtain ⟨F, hFn, hFM, hFT⟩ := hA.decompose T hT
  let G : ∀ n, E n →L[ℂ] E n := fun n => unitaryConj (U n) (F n)
  obtain ⟨S, hS, hSG⟩ := hB.reconstruct G ‖T‖ (norm_nonneg _)
    (fun n => by simpa only [G, norm_unitaryConj] using hFn n)
    (fun n => (hU n).subset ⟨F n, hFM n, rfl⟩)
  have hTG : RepresentsBlockOperators G (unitaryConj (l2FiberUnitary U) T) := by
    intro f n
    change ((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2)
      (T ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2) f))) n = _
    rw [l2FiberUnitary_apply, hFT, l2FiberUnitary_star_apply]
    rfl
  rw [hTG.unique hSG]
  exact hS

theorem conjugates_l2FiberUnitary
    {M N : ∀ n, VonNeumannAlgebra (E n)} {A B : VonNeumannAlgebra (lp E 2)}
    (hA : BlockAlgebraDecomposition M A) (hB : BlockAlgebraDecomposition N B)
    (U : ∀ n, unitary (E n →L[ℂ] E n))
    (hU : ∀ n, Conjugates (U n) (M n) (N n)) :
    Conjugates (l2FiberUnitary U) A B := by
  have hs : l2FiberUnitary (fun n => star (U n)) = star (l2FiberUnitary U) := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    exact (l2FiberUnitary_star_apply U f n).symm
  have hf := blockOperator_conjugation_inclusion hA hB U hU
  have hr := blockOperator_conjugation_inclusion hB hA (fun n => star (U n))
    (fun n => (hU n).symm)
  rw [hs] at hr
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact hf T hT
  · intro S hS
    refine ⟨unitaryConj (star (l2FiberUnitary U)) S, hr S hS, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj (star (l2FiberUnitary U)) S

theorem exists_bounded_conjugacy_of_block_implementers
    {M N : ∀ n, VonNeumannAlgebra (E n)} {A B : VonNeumannAlgebra (lp E 2)}
    (hA : BlockAlgebraDecomposition M A) (hB : BlockAlgebraDecomposition N B)
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ n, ∃ u : unitary (E n →L[ℂ] E n),
      Conjugates u (M n) (N n) ∧ ‖(u : E n →L[ℂ] E n) - 1‖ ≤ a) :
    ∃ u : unitary (lp E 2 →L[ℂ] lp E 2),
      Conjugates u A B ∧ ‖(u : lp E 2 →L[ℂ] lp E 2) - 1‖ ≤ a := by
  choose U hc hn using hex
  exact ⟨l2FiberUnitary U, conjugates_l2FiberUnitary hA hB U hc,
    norm_l2FiberUnitary_sub_one_le U ha hn⟩

end

end KadisonKastler

end OAI
