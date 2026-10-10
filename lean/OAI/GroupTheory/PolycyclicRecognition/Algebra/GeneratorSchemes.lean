import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProductChart

namespace OAI

/-! # Finite generator schemes with locally open endpoint maps

A conjugated-generator basis gives a single finite scheme, with fixed
conjugating words, whose endpoint map covers a neighborhood of the identity.
The logarithm of that map has the identity-rank differential proved from BCH.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type*} [Group G]

local instance generatorSchemeNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance generatorSchemeNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

/-- Reverse a generator word and negate its one-parameter amplitudes. -/
def inverseGeneratorWord (w : List (I × ℝ)) : List (I × ℝ) :=
  w.reverse.map (fun p => (p.1, -p.2))

variable (X : I → L) (Exp : L → G)

theorem generatorGroupWord_append (u v : List (I × ℝ)) :
    generatorGroupWord X Exp (u ++ v) =
      generatorGroupWord X Exp u * generatorGroupWord X Exp v := by
  simp only [generatorGroupWord, List.map_append, List.prod_append]

theorem generatorGroupWord_inverse (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (w : List (I × ℝ)) :
    generatorGroupWord X Exp (inverseGeneratorWord w) = (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp [inverseGeneratorWord]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, generatorGroupWord_append, generatorGroupWord_cons,
      generatorGroupWord_nil, mul_one, mul_inv_rev] at *
    rw [ih]
    congr 1
    simpa only [neg_smul] using hneg (t • X i)

/-- Fixed conjugating words with one variable generator inserted in each. -/
def generatorSchemeWord {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) : List (I × ℝ) :=
  (List.ofFn (fun k => w k ++ [(i k, t k)] ++ inverseGeneratorWord (w k))).flatten

/-- The word length is fixed even though the inserted amplitudes vary. -/
theorem length_generatorSchemeWord {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    (generatorSchemeWord w i t).length = ∑ k, (2 * (w k).length + 1) := by
  simp [generatorSchemeWord, inverseGeneratorWord, List.length_flatten,
    List.map_ofFn, List.sum_ofFn]
  congr 1
  funext k
  omega

/-- Endpoint of the expanded scheme is exactly the product in the chosen
basis directions. -/
theorem generatorScheme_endpoint {n : ℕ}
    (b : Basis (Fin n) ℝ L) (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hb : ∀ k (s : ℝ), Exp (s • b k) =
      generatorGroupWord X Exp (w k) * Exp (s • X (i k)) *
        (generatorGroupWord X Exp (w k))⁻¹)
    (t : Fin n → ℝ) :
    generatorGroupWord X Exp (generatorSchemeWord w i t) = basisExponentialProduct Exp b t := by
  unfold generatorSchemeWord generatorGroupWord
  rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn]
  change (List.ofFn (fun k => generatorGroupWord X Exp
    (w k ++ [(i k, t k)] ++ inverseGeneratorWord (w k)))).prod = _
  congr 1
  apply congrArg List.ofFn
  funext k
  rw [generatorGroupWord_append, generatorGroupWord_append, generatorGroupWord_inverse X Exp hneg]
  simpa only [generatorGroupWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] using (hb k (t k)).symm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual finite scheme and a neighborhood covered with bounded
variable amplitudes. All the hypotheses are algebraic representation/BCH
identities; local surjectivity is proved, not assumed. -/
theorem exists_local_generator_scheme
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤)
    (hExp : Function.Bijective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {c : ℕ} (coeff : DynkinCoefficients c (finrank ℝ L))
    (hprod : ∀ Z : Fin (finrank ℝ L) → L,
      (List.ofFn (fun k => Exp (Z k))).prod = Exp (finiteDynkinPolynomial coeff Z)) :
    ∃ (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I)
      (ε : ℝ), 0 < ε ∧ ∀ v : L, ‖v‖ < ε →
      ∃ t : Fin (finrank ℝ L) → ℝ, ‖t‖ < 1 ∧
        generatorGroupWord X Exp (generatorSchemeWord w i t) = Exp v := by
  obtain ⟨b, w, i, hb⟩ := exists_generatorGroupWord_basis X Exp j ρ hρ hmatch hX
  obtain ⟨ε, hε, hcover⟩ := exists_ball_subset_basisProductLog_image Exp b hExp hzero coeff hprod
  refine ⟨w, i, ε, hε, ?_⟩
  intro v hv
  obtain ⟨t, ht, he⟩ := hcover (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  refine ⟨t, by simpa only [Metric.mem_ball, dist_zero_right] using ht, ?_⟩
  rw [generatorScheme_endpoint X Exp b w i hneg hb]
  exact ((Equiv.ofBijective Exp hExp).apply_symm_apply _).symm.trans (congrArg Exp he)

end PolycyclicRecognition

end

end OAI
