import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.NumberTheory.NumberField.Basic
import OAI.NumberTheory.SiegelZeros.Characters.SquarefreeRadicands
import OAI.NumberTheory.SiegelZeros.Determinants.DeterminantComparison

namespace OAI

namespace SiegelZeros


namespace W10

open Module

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

abbrev rootField (a b : K) := IntermediateField.adjoin ℚ ({a, b} : Set K)

local instance rootFieldModuleSMul (a b : K) : SMul ℚ (rootField a b) :=
  (inferInstance : Module ℚ (rootField a b)).toSMul

omit [CharZero K] in
theorem leftRoot_mem (a b : K) : a ∈ rootField a b :=
  IntermediateField.subset_adjoin ℚ _ (by simp)

omit [CharZero K] in
theorem rightRoot_mem (a b : K) : b ∈ rootField a b :=
  IntermediateField.subset_adjoin ℚ _ (by simp)

def adjoinGenerators (a b : K) (i : Fin 4) : rootField a b :=
  ⟨generators a b i, by
    fin_cases i
    · exact (rootField a b).one_mem
    · exact leftRoot_mem a b
    · exact rightRoot_mem a b
    · exact (rootField a b).mul_mem (leftRoot_mem a b) (rightRoot_mem a b)⟩

omit [CharZero K] in
@[simp] theorem coe_adjoinGenerators (a b : K) (i : Fin 4) :
    ((adjoinGenerators a b i : rootField a b) : K) = generators a b i := rfl

omit [CharZero K] in
theorem adjoinGenerators_linearIndependent (a b : K)
    (hli : LinearIndependent ℚ (generators a b)) :
    LinearIndependent ℚ (adjoinGenerators a b) := by
  let inclusion : rootField a b →+ K :=
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  apply LinearIndependent.of_comp inclusion.toRatLinearMap
  simpa [Function.comp_def, inclusion] using hli

omit [CharZero K] in
theorem rootField_toSubalgebra (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    (rootField a b).toSubalgebra = Algebra.adjoin ℚ ({a, b} : Set K) := by
  have hai : IsIntegral ℚ a := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [ha]
    simpa using (isIntegral_algebraMap (R := ℚ) (A := K) (x := d))
  have hbi : IsIntegral ℚ b := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hb]
    simpa using (isIntegral_algebraMap (R := ℚ) (A := K) (x := (2 : ℚ)))
  apply IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hai.isAlgebraic
  · exact hbi.isAlgebraic

noncomputable def adjoinBasisOfCoordinates (a b : K)
    (hli : LinearIndependent ℚ (generators a b))
    (hspan : ∀ x : rootField a b, ∃ c : Fin 4 → ℚ,
      ∑ i, c i • adjoinGenerators a b i = x) : Basis (Fin 4) ℚ (rootField a b) :=
  Basis.mk (adjoinGenerators_linearIndependent a b hli) (by
    intro x _
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mpr (hspan x))

omit [CharZero K] in
@[simp] theorem adjoinBasisOfCoordinates_apply (a b : K)
    (hli : LinearIndependent ℚ (generators a b))
    (hspan : ∀ x : rootField a b, ∃ c : Fin 4 → ℚ,
      ∑ i, c i • adjoinGenerators a b i = x) (i : Fin 4) :
    adjoinBasisOfCoordinates a b hli hspan i = adjoinGenerators a b i := by
  exact Basis.mk_apply _ _ i

omit [CharZero K] in
theorem rootField_finrank_of_coordinates (a b : K)
    (hli : LinearIndependent ℚ (generators a b))
    (hspan : ∀ x : rootField a b, ∃ c : Fin 4 → ℚ,
      ∑ i, c i • adjoinGenerators a b i = x) :
    Module.finrank ℚ (rootField a b) = 4 := by
  simpa using Module.finrank_eq_card_basis (adjoinBasisOfCoordinates a b hli hspan)

omit [CharZero K] in
theorem rootField_coordinates (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (x : rootField a b) :
    ∃ c : Fin 4 → ℚ, ∑ i, c i • adjoinGenerators a b i = x := by
  have ha' : a * a = algebraMap ℚ K d := by simpa [pow_two] using ha
  have hb' : b * b = 2 := by simpa [pow_two] using hb
  have hx : (x : K) ∈ Algebra.adjoin ℚ ({a, b} : Set K) := by
    rw [← rootField_toSubalgebra a b d ha hb]
    exact x.property
  rw [← WeightedTorusJets.W11.evalAlg_range d a b ha' hb'] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨![z.re.re, z.re.im, z.im.re, z.im.im], ?_⟩
  apply Subtype.ext
  rw [← hz]
  simp [Fin.sum_univ_succ, adjoinGenerators, generators, Algebra.smul_def,
    WeightedTorusJets.W11.evalAlg, WeightedTorusJets.W11.evalBiquad,
    WeightedTorusJets.W11.evalQuadratic]
  ring

noncomputable def rootFieldBasis (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators a b)) : Basis (Fin 4) ℚ (rootField a b) :=
  adjoinBasisOfCoordinates a b hli (rootField_coordinates a b d ha hb)

omit [CharZero K] in
@[simp] theorem rootFieldBasis_apply (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators a b)) (i : Fin 4) :
    rootFieldBasis a b d ha hb hli i = adjoinGenerators a b i := by
  simp [rootFieldBasis]

noncomputable def coordinateFieldEquiv (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators a b)) :
    WeightedTorusJets.W11.Biquad d ≃ₐ[ℚ] rootField a b := by
  let e : WeightedTorusJets.W11.Biquad d ≃+* rootField a b :=
    (WeightedTorusJets.W11.adjoinEquiv d a b (by simpa [pow_two] using ha)
    (by simpa [pow_two] using hb) hli).toRingEquiv.trans
      (Subalgebra.equivOfEq _ _ (rootField_toSubalgebra a b d ha hb).symm).toRingEquiv
  exact { e with commutes' := fun r => e.toRingHom.map_rat_algebraMap r }

omit [CharZero K] in
@[simp] theorem coordinateFieldEquiv_apply (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators a b)) (z : WeightedTorusJets.W11.Biquad d) :
    ((coordinateFieldEquiv a b d ha hb hli z : rootField a b) : K) =
      WeightedTorusJets.W11.evalAlg d a b (by simpa [pow_two] using ha)
        (by simpa [pow_two] using hb) z := rfl

noncomputable def squarefreeRootFieldBasis (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) : Basis (Fin 4) ℚ (rootField a b) :=
  rootFieldBasis a b (d : ℚ) (by simpa using ha) hb
    (generators_linearIndependent_squarefree a b d hd hd1 hd2 ha hb)

theorem squarefreeRootField_finrank (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    Module.finrank ℚ (rootField a b) = 4 := by
  simpa using Module.finrank_eq_card_basis
    (squarefreeRootFieldBasis a b d hd hd1 hd2 ha hb)

private theorem finiteRatModule_of_basis {V : Type*} [AddCommGroup V]
    {m : Module ℚ V} (b : @Basis (Fin 4) ℚ V _ _ m) (m' : Module ℚ V) :
    @Module.Finite ℚ V _ _ m' := by
  cases Subsingleton.elim m m'
  exact @Module.Finite.of_basis ℚ V (Fin 4) _ _ m _ b

theorem squarefreeRootField_numberField (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) : NumberField (rootField a b) where
  to_charZero := inferInstance
  to_finiteDimensional := finiteRatModule_of_basis
    (squarefreeRootFieldBasis a b d hd hd1 hd2 ha hb) _

omit [CharZero K] in
theorem adjoinGenerators_isIntegral (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (i : Fin 4) :
    IsIntegral ℤ (adjoinGenerators a b i) := by
  apply (isIntegral_algebraMap_iff (R := ℤ) (A := rootField a b) (B := K)).mp
  change IsIntegral ℤ (generators a b i)
  exact generators_isIntegral a b d ha hb i

theorem squarefreeRootFieldBasis_isIntegral (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (i : Fin 4) :
    IsIntegral ℤ (squarefreeRootFieldBasis a b d hd hd1 hd2 ha hb i) := by
  simpa [squarefreeRootFieldBasis] using adjoinGenerators_isIntegral a b d ha hb i

end W10



namespace WeightedTorusJets.W11
open SiegelZeros.W10

def signAlg (d : ℚ) (s t : Bool) : Biquad d ≃ₐ[ℚ] Biquad d :=
  { signAction d s t with
    commutes' := fun r => by
      change signAction d s t ⟨⟨r, 0⟩, 0⟩ = ⟨⟨r, 0⟩, 0⟩
      cases s <;> cases t <;> ext <;> simp [signAction, sigma, tau, flip] }

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

noncomputable def fieldSignAction (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) (s t : Bool) :
    rootField ar br ≃ₐ[ℚ] rootField ar br :=
  let e := coordinateFieldEquiv ar br d ha hb hli
  (e.symm.trans (signAlg d s t)).trans e

omit [CharZero K] in
@[simp] theorem fieldSignAction_on_model (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) (s t : Bool) (z : Biquad d) :
    fieldSignAction ar br d ha hb hli s t (coordinateFieldEquiv ar br d ha hb hli z) =
      coordinateFieldEquiv ar br d ha hb hli (signAction d s t z) := by
  simp [fieldSignAction, signAlg]

omit [CharZero K] in
theorem fieldSignAction_comp (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) (s t u v : Bool)
    (z : rootField ar br) :
    fieldSignAction ar br d ha hb hli s t (fieldSignAction ar br d ha hb hli u v z) =
      fieldSignAction ar br d ha hb hli (Bool.xor s u) (Bool.xor t v) z := by
  obtain ⟨x, rfl⟩ := (coordinateFieldEquiv ar br d ha hb hli).surjective z
  simp only [fieldSignAction_on_model, signAction_comp]

omit [CharZero K] in
theorem fieldSignAction_injective (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) :
    Function.Injective (fun st : Bool × Bool =>
      fieldSignAction ar br d ha hb hli st.1 st.2) := by
  intro st uv h
  apply signAction_injective d
  apply RingEquiv.ext
  intro z
  apply (coordinateFieldEquiv ar br d ha hb hli).injective
  have hz := congrArg (fun f : rootField ar br ≃ₐ[ℚ] rootField ar br =>
    f (coordinateFieldEquiv ar br d ha hb hli z)) h
  simpa only [fieldSignAction_on_model] using hz

omit [CharZero K] in
theorem fieldSigma_theta (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) (n : Fin 4 → ℚ) :
    fieldSignAction ar br d ha hb hli true false
      (coordinateFieldEquiv ar br d ha hb hli (theta d n)) =
        coordinateFieldEquiv ar br d ha hb hli (theta d ![n 0, -n 1, n 2, -n 3]) := by
  rw [fieldSignAction_on_model]
  simp [signAction, sigma_theta]

noncomputable def squarefreeFieldSignAction (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) (s t : Bool) :
    rootField ar br ≃ₐ[ℚ] rootField ar br :=
  fieldSignAction ar br (d : ℚ) (by simpa using ha) hb
    (generators_linearIndependent_squarefree ar br d hd hd1 hd2 ha hb) s t

omit [CharZero K] in
@[simp] theorem coordinateFieldEquiv_a (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) :
    coordinateFieldEquiv ar br d ha hb hli (a d) = adjoinGenerators ar br 1 := by
  apply Subtype.ext
  simp [generators]

omit [CharZero K] in
@[simp] theorem coordinateFieldEquiv_b (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) :
    coordinateFieldEquiv ar br d ha hb hli (b d) = adjoinGenerators ar br 2 := by
  apply Subtype.ext
  simp [generators]

omit [CharZero K] in
@[simp] theorem fieldSignAction_a (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) (s t : Bool) :
    fieldSignAction ar br d ha hb hli s t (adjoinGenerators ar br 1) =
      if s then -adjoinGenerators ar br 1 else adjoinGenerators ar br 1 := by
  rw [← coordinateFieldEquiv_a ar br d ha hb hli, fieldSignAction_on_model]
  cases s <;> cases t <;> simp [signAction]

omit [CharZero K] in
@[simp] theorem fieldSignAction_b (ar br : K) (d : ℚ)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2)
    (hli : LinearIndependent ℚ (generators ar br)) (s t : Bool) :
    fieldSignAction ar br d ha hb hli s t (adjoinGenerators ar br 2) =
      if t then -adjoinGenerators ar br 2 else adjoinGenerators ar br 2 := by
  rw [← coordinateFieldEquiv_b ar br d ha hb hli, fieldSignAction_on_model]
  cases s <;> cases t <;> simp [signAction]

@[simp] theorem squarefreeFieldSignAction_a (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) (s t : Bool) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb s t
      (adjoinGenerators ar br 1) =
        if s then -adjoinGenerators ar br 1 else adjoinGenerators ar br 1 := by
  exact fieldSignAction_a ar br (d : ℚ) (by simpa using ha) hb
    (generators_linearIndependent_squarefree ar br d hd hd1 hd2 ha hb) s t

@[simp] theorem squarefreeFieldSignAction_b (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) (s t : Bool) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb s t
      (adjoinGenerators ar br 2) =
        if t then -adjoinGenerators ar br 2 else adjoinGenerators ar br 2 := by
  exact fieldSignAction_b ar br (d : ℚ) (by simpa using ha) hb
    (generators_linearIndependent_squarefree ar br d hd hd1 hd2 ha hb) s t

theorem squarefreeSigma_a (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb true false
      (adjoinGenerators ar br 1) = -adjoinGenerators ar br 1 := by simp

theorem squarefreeSigma_b (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb true false
      (adjoinGenerators ar br 2) = adjoinGenerators ar br 2 := by simp

theorem squarefreeTau_a (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb false true
      (adjoinGenerators ar br 1) = adjoinGenerators ar br 1 := by simp

theorem squarefreeTau_b (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb false true
      (adjoinGenerators ar br 2) = -adjoinGenerators ar br 2 := by simp

theorem squarefreeSigmaTau_a (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb true true
      (adjoinGenerators ar br 1) = -adjoinGenerators ar br 1 := by simp

theorem squarefreeSigmaTau_b (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb true true
      (adjoinGenerators ar br 2) = -adjoinGenerators ar br 2 := by simp

end WeightedTorusJets.W11



noncomputable section

namespace SiegelZerosAwei.W36

open scoped BigOperators
open _root_.OAI.SiegelZeros.W10

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

def rootA (a b : K) : rootField a b := ⟨a, leftRoot_mem a b⟩

def rootB (a b : K) : rootField a b := ⟨b, rightRoot_mem a b⟩

omit [CharZero K] in
theorem rootA_sq (a b : K) (d : ℤ) (ha : a ^ 2 = (d : K)) :
    rootA a b ^ 2 = (d : rootField a b) := by
  apply Subtype.ext
  exact ha

omit [CharZero K] in
theorem rootB_sq (a b : K) (hb : b ^ 2 = 2) :
    rootB a b ^ 2 = 2 := by
  apply Subtype.ext
  exact hb

def concreteDirections (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    Fin 3 → rootField a b →+* rootField a b :=
  ![RingHom.id _,
    (WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb
      true false).toRingHom,
    (WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb
      true true).toRingHom]

def concreteThetaMatrix {m : ℕ} (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (orders : Fin m → Fin 3 → ℕ) (n : Fin m → Fin 4 → ℕ) :
    Matrix (Fin m) (Fin m) (rootField a b) :=
  thetaRowMatrix (concreteDirections a b d hd hd1 hd2 ha hb)
    (rootA a b) (rootB a b) orders n

private theorem finrankRatModule_eq_four {V : Type*} [AddCommGroup V]
    {m : Module ℚ V} (h : @Module.finrank ℚ V _ _ m = 4) (m' : Module ℚ V) :
    @Module.finrank ℚ V _ _ m' = 4 := by
  cases Subsingleton.elim m m'
  exact h

theorem concrete_archimedean_norm_bound {m : ℕ} (hm : 0 < m)
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (q N : ℕ)
    (orders : Fin m → Fin 3 → ℕ) (n : Fin m → Fin 4 → ℕ)
    (hq : 1 ≤ q) (hN : 0 < N) (hheight : |(d : ℝ)| ≤ (q : ℝ))
    (hn : ∀ j i, n j i ≤ N)
    (hne : (concreteThetaMatrix a b d hd hd1 hd2 ha hb orders n).det ≠ 0) :
    (1 / 4 : ℝ) * Real.log
        |(Algebra.norm ℚ
          (concreteThetaMatrix a b d hd hd1 hd2 ha hb orders n).det : ℝ)| ≤
      (m : ℝ) / 2 * Real.log m +
      (∑ i, ((orders i 0 + orders i 1 + orders i 2 : ℕ) : ℝ)) *
        (Real.log N + (1 / 2 : ℝ) * Real.log q + Real.log 8) := by
  let := squarefreeRootField_numberField a b d hd hd1 hd2 ha hb
  exact archimedean_norm_bound hm
    (concreteDirections a b d hd hd1 hd2 ha hb) (rootA a b) (rootB a b) d q N
    orders n (rootA_sq a b d ha) (rootB_sq a b hb) hq hN hheight hn
    (finrankRatModule_eq_four (squarefreeRootField_finrank a b d hd hd1 hd2 ha hb) _) hne

end SiegelZerosAwei.W36

end


end SiegelZeros

end OAI
