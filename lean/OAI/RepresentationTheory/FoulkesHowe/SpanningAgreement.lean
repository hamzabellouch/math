import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Module

namespace Problem346

/-- Equality on chosen basis generators extends to all generator tuples when each
coordinate of the generator function has a linear extension. -/
theorem multilinear_agreement_of_basis
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X K : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i) (B : ∀ i, Basis (K i) R (M i))
    (t : ∀ i, K i → X i) (ht : ∀ i k, s i (t i k) = B i k)
    (F : (∀ i, X i) → W) (G : MultilinearMap R M W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y))
    (hbase : ∀ k : ∀ i, K i, F (fun i => t i (k i)) = G (fun i => B i (k i))) :
    ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by
  classical
  have aux : ∀ (S : Finset I) (x : ∀ i, X i),
      (∀ i, i ∉ S → ∃ k, x i = t i k) → F x = G (fun i => s i (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      choose k hk using fun i => hx i (Finset.notMem_empty i)
      have he : x = fun i => t i (k i) := funext hk
      rw [he, hbase]
      simp only [ht]
    | @insert i S hi ih =>
      intro x hx
      obtain ⟨L, hL⟩ := hlinear x i
      have heq : L = G.toLinearMap (fun j => s j (x j)) i := by
        apply (B i).ext
        intro k
        rw [← ht i k, hL]
        rw [ih (Function.update x i (t i k))]
        · simp only [MultilinearMap.toLinearMap_apply]
          congr 1
          funext j
          by_cases hji : j = i
          · subst j
            simp [ht]
          · simp [Function.update_of_ne hji]
        · intro j hj
          by_cases hji : j = i
          · subst j
            exact ⟨k, by simp⟩
          · obtain ⟨l, hl⟩ := hx j (by simp [hji, hj])
            exact ⟨l, by simpa [Function.update_of_ne hji] using hl⟩
      have h := congrArg (fun L : M i →ₗ[R] W => L (s i (x i))) heq
      simpa only [hL, Function.update_eq_self, MultilinearMap.toLinearMap_apply] using h
  intro x
  exact aux Finset.univ x (by simp)

/-- Construct the extension when a basis consists of specified generators. -/
theorem exists_multilinear_extension_of_basis
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X K : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i) (B : ∀ i, Basis (K i) R (M i))
    (t : ∀ i, K i → X i) (ht : ∀ i k, s i (t i k) = B i k)
    (F : (∀ i, X i) → W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y)) :
    ∃ G : MultilinearMap R M W, ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by
  let L : (PiTensorProduct R M) →ₗ[R] W :=
    (Basis.piTensorProduct B).constr R (fun k => F (fun i => t i (k i)))
  let G : MultilinearMap R M W := L.compMultilinearMap (PiTensorProduct.tprod R)
  refine ⟨G, multilinear_agreement_of_basis s B t ht F G hlinear ?_⟩
  intro k
  change F (fun i => t i (k i)) = L (PiTensorProduct.tprod R (fun i => B i (k i)))
  rw [← Basis.piTensorProduct_apply]
  dsimp only [L]
  rw [Basis.constr_basis]

/-- Separate linear extendibility on spanning generators gives a multilinear extension. -/
theorem exists_multilinear_extension_of_spanning
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i)
    (hspan : ∀ i, Submodule.span R (Set.range (s i)) = ⊤)
    (F : (∀ i, X i) → W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y)) :
    ∃ G : MultilinearMap R M W, ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by
  classical
  have hs (i : I) : ⊤ ≤ Submodule.span R (Set.range (s i)) := by rw [hspan i]
  let B := fun i => Basis.ofSpan (hs i)
  have hpre : ∀ i k, ∃ x, s i x = B i k := by
    intro i k
    exact Basis.ofSpan_subset (hs i) (Set.mem_range_self k)
  choose t ht using hpre
  exact exists_multilinear_extension_of_basis s B t ht F hlinear

end Problem346

end

end OAI
