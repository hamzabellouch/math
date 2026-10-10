import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanControlledProducts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts
import Mathlib.GroupTheory.SemidirectProduct

namespace OAI

/-! # Cartan logarithms of bounded words

The Cartan group is nilpotent. The finite Dynkin identity therefore gives a
polynomial bound on the logarithm of every prefix of a bounded word. We also
record the exact semidirect-product word formula used to apply the controlled
Cartan estimates to such prefixes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

/-- Ordered product of the first `m` letters of a word. -/
def wordPrefix {G : Type*} [Monoid G] (u : ℕ → G) (m : ℕ) : G :=
  (List.ofFn (fun i : Fin m => u i.val)).prod

@[simp] theorem wordPrefix_zero {G : Type*} [Monoid G] (u : ℕ → G) :
    wordPrefix u 0 = 1 := rfl

theorem wordPrefix_succ {G : Type*} [Monoid G] (u : ℕ → G) (m : ℕ) :
    wordPrefix u (m + 1) = wordPrefix u m * u m := by
  unfold wordPrefix
  rw [List.ofFn_succ', List.prod_concat]
  rfl

theorem semidirect_wordPrefix_right {N D : Type*} [Group N] [Group D]
    (φ : D →* MulAut N) (u : ℕ → N) (v : ℕ → D) (m : ℕ) :
    (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).right = wordPrefix v m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wordPrefix_succ, SemidirectProduct.mul_right, ih, wordPrefix_succ]

/-- The nilpotent component of a semidirect word is the ordered product of
the nilpotent increments acted on by the actual Cartan prefixes. -/
theorem semidirect_wordPrefix_left {N D : Type*} [Group N] [Group D]
    (φ : D →* MulAut N) (u : ℕ → N) (v : ℕ → D) (m : ℕ) :
    (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).left =
      wordPrefix (fun i => φ (wordPrefix v i) (u i)) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wordPrefix_succ, SemidirectProduct.mul_left, ih,
      semidirect_wordPrefix_right, wordPrefix_succ]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

/-- The Cartan logarithm in the actual nilpotent exponential coordinates. -/
def cartanLog (d : D) : H := eD.symm ((Equiv.ofBijective ExpD hbijD).symm d)

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
@[simp] theorem cartanLog_exp (h : H) : cartanLog H eD ExpD hbijD (ExpD (eD h)) = h := by
  unfold cartanLog
  change eD.symm ((Equiv.ofBijective ExpD hbijD).symm
    ((Equiv.ofBijective ExpD hbijD) (eD h))) = h
  rw [Equiv.symm_apply_apply, eD.symm_apply_apply]

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
theorem exp_cartanLog (d : D) : ExpD (eD (cartanLog H eD ExpD hbijD d)) = d := by
  unfold cartanLog
  rw [eD.apply_symm_apply]
  exact (Equiv.ofBijective ExpD hbijD).apply_symm_apply d

/-- Bounded Cartan increments have polynomial logarithmic coordinates.
The nilpotence bound comes from the Cartan subalgebra itself. -/
theorem exists_cartan_word_log_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ (A : ℝ) (c : ℕ), 0 ≤ A ∧ ∀ (u : ℕ → D) (m : ℕ),
      (∀ i < m, u i ∈ exponentialCoordinateBox (ExpD ∘ eD) (finBasis ℝ H) R) →
      ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (wordPrefix u m))‖ ≤
        A * (1 + (m : ℝ)) ^ c := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound (finBasis ℝ H)
  let A : ℝ := (c : ℝ) * 2 ^ c *
    (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c * (1 + R) ^ c
  refine ⟨A, c, by dsimp [A]; positivity, ?_⟩
  intro u m hu
  obtain ⟨x, hx, hbound⟩ := product_mem_exponentialCoordinateBox dynkinD eD ExpD hExpD hc
    (finBasis ℝ H) hK hR hbracket (fun i : Fin m => u i.val) (fun i => hu i.val i.isLt)
  change ExpD (eD x) = wordPrefix u m at hx
  rw [← hx, cartanLog_exp]
  simpa only [Fintype.card_fin, A] using hbound

end PolycyclicRecognition

end

end OAI
