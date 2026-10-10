import OAI.Analysis.FreeGroupFactor.TraceCocycle

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι}

def wordHom (U : ι → unitary A) : FreeGroup ι →* A :=
  (unitary A).subtype.comp (FreeGroup.lift U)

@[simp] theorem wordHom_of (U : ι → unitary A) (i : ι) :
    wordHom U (FreeGroup.of i) = (U i : A) := by
  simp [wordHom]

@[simp] theorem wordHom_inv (U : ι → unitary A) (g : FreeGroup ι) :
    wordHom U g⁻¹ = star (wordHom U g) := by
  change ((FreeGroup.lift U g⁻¹ : unitary A) : A) = _
  rw [map_inv]
  rfl

theorem wordHom_word [DecidableEq ι]
    (U : ι → unitary A) (g : FreeGroup ι) :
    wordHom U g = PolynomialFlow.word g (fun i => (U i : A)) := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := g)]
  change ((FreeGroup.lift U (FreeGroup.mk g.toWord) : unitary A) : A) = _
  rw [FreeGroup.lift_mk]
  rw [Submonoid.coe_list_prod]
  simp only [List.map_map, Function.comp_def]
  unfold PolynomialFlow.word PolynomialFlow.wordList
  apply congrArg List.prod
  apply List.map_congr_left
  intro ib _
  rcases ib with ⟨i, b⟩
  cases b <;> rfl

def algebraHom (U : ι → unitary A) : MonoidAlgebra ℂ (FreeGroup ι) →ₐ[ℂ] A :=
  MonoidAlgebra.lift ℂ A (FreeGroup ι) (wordHom U)

@[simp] theorem algebraHom_of (U : ι → unitary A) (g : FreeGroup ι) :
    algebraHom U (MonoidAlgebra.of ℂ (FreeGroup ι) g) = wordHom U g := by
  simp [algebraHom]

@[simp] theorem eval_encode [DecidableEq ι]
    (U : ι → unitary A) (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encode p) = algebraHom U p := by
  calc
    _ = algebraHom U (NCPolynomial.eval
        (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (AlgebraPolynomial.signed ib))
        (AlgebraPolynomial.encode p)) := by
      rw [AlgebraPolynomial.map_eval]
      congr 1
      funext ib
      exact (algebraHom_of U _).symm
    _ = algebraHom U p := by rw [AlgebraPolynomial.eval_encode]

def coefficientHom {G : Type uG} (ρ : G → A) : (G →₀ ℂ) →ₗ[ℂ] A :=
  Finsupp.linearCombination ℂ ρ

@[simp] theorem coefficientHom_single {G : Type uG} (ρ : G → A) (g : G) (c : ℂ) :
    coefficientHom ρ (Finsupp.single g c) = c • ρ g := by
  exact Finsupp.linearCombination_single _ _ _

theorem algebraHom_ofCoeff (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) :
    algebraHom U (MonoidAlgebra.ofCoeff p) = coefficientHom (wordHom U) p := by
  simp [algebraHom, MonoidAlgebra.lift_apply, coefficientHom, Finsupp.linearCombination_apply]

theorem coefficientHom_shift {G : Type uG} [Group G] (ρ : G →* A)
    (g : G) (p : G →₀ ℂ) :
    coefficientHom ρ (TraceCocycle.shift g p) =
      ρ g * coefficientHom ρ p * ρ g⁻¹ := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq, mul_add, add_mul]
  | single b c =>
    have hs : TraceCocycle.shift g (Finsupp.single b c) =
        Finsupp.single (g * b * g⁻¹) c := by
      simp only [TraceCocycle.shift, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_single]
      rfl
    rw [hs, coefficientHom_single, coefficientHom_single]
    simp only [map_mul, smul_mul_assoc, mul_smul_comm]

theorem derivative_of (h : ι → TraceCocycle.CF (FreeGroup ι)) (g : FreeGroup ι) :
    TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g) =
      MonoidAlgebra.ofCoeff (TraceCocycle.cocycle h g) *
        MonoidAlgebra.of ℂ (FreeGroup ι) g := by
  ext b
  simp [MonoidAlgebra.of_apply]

theorem eval_derivative_of (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (g : FreeGroup ι) :
    algebraHom U (TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g)) =
      coefficientHom (wordHom U) (TraceCocycle.cocycle h g) * wordHom U g := by
  rw [derivative_of, map_mul, algebraHom_ofCoeff, algebraHom_of]

theorem eval_encodedField_pos [DecidableEq ι] (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (i : ι) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encodedField h (i, true)) =
      coefficientHom (wordHom U) (h i) * (U i : A) := by
  rw [AlgebraPolynomial.encodedField, eval_encode, eval_derivative_of]
  simp only [AlgebraPolynomial.signed, ↓reduceIte, TraceCocycle.cocycle_of, wordHom_of]

theorem eval_encodedField_neg [DecidableEq ι] (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (i : ι) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encodedField h (i, false)) =
      -(star (U i : A) * coefficientHom (wordHom U) (h i)) := by
  rw [AlgebraPolynomial.encodedField, eval_encode, eval_derivative_of]
  simp only [AlgebraPolynomial.signed, Bool.false_eq_true, ↓reduceIte,
    TraceCocycle.cocycle_inv, TraceCocycle.cocycle_of, map_neg, coefficientHom_shift,
    wordHom_inv, inv_inv, wordHom_of, neg_mul]
  rw [mul_assoc, mul_assoc, (U i).property.2, mul_one]

end UnitaryEvaluation
end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

def extendUnitary (U : ι → unitary A) (C : unitary A) : Option ι → unitary A :=
  fun o => o.elim C U

def laurentValue (C : unitary A) (l : ℤ →₀ ℂ) : A :=
  coefficientHom (fun k : ℤ => ((C ^ k : unitary A) : A)) l

@[simp] theorem wordHom_extend (U : ι → unitary A) (C : unitary A) (g : FreeGroup ι) :
    wordHom (extendUnitary U C) (FreeGroup.map Option.some g) = wordHom U g := by
  have he : (wordHom (extendUnitary U C)).comp (FreeGroup.map Option.some) = wordHom U := by
    apply FreeGroup.ext_hom
    intro i
    simp [extendUnitary]
  exact DFunLike.congr_fun he g

@[simp] theorem coefficientHom_laurent (U : ι → unitary A) (C : unitary A) (l : ℤ →₀ ℂ) :
    coefficientHom (wordHom (extendUnitary U C))
      (TraceCocycle.laurent (FreeGroup.of none) l) = laurentValue C l := by
  induction l using Finsupp.induction_linear with
  | zero => simp [TraceCocycle.laurent, laurentValue]
  | add p q hp hq => simpa [TraceCocycle.laurent, laurentValue, map_add] using congrArg₂ (· + ·) hp hq
  | single k c =>
    simp only [TraceCocycle.laurent, Finsupp.linearCombination_single, map_smul,
      coefficientHom_single, one_smul, laurentValue]
    congr 1
    change ((FreeGroup.lift (extendUnitary U C) (FreeGroup.of none ^ k) : unitary A) : A) = _
    rw [map_zpow, FreeGroup.lift_apply_of]
    rfl

 theorem coefficientHom_fieldCoefficients [DecidableEq ι]
    (U : ι → unitary A) (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (i : ι) :
    coefficientHom (wordHom (extendUnitary U C)) (TraceCocycle.fieldCoefficients h l (some i)) =
      Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (fun j => (U j : A)) := by
  classical
  simp only [TraceCocycle.fieldCoefficients, PolynomialFlow.hamiltonian, Finsupp.sum,
    map_sum, map_smul, coefficientHom_shift, coefficientHom_laurent,
    wordHom_inv, wordHom_extend, Finset.smul_sum]
  simp only [wordHom_word]
  apply Finset.sum_congr rfl
  intro g hg
  rw [smul_smul, mul_comm]

def signedTrajectory (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (ib : Option ι × Bool) : A :=
  wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C) (AlgebraPolynomial.signed ib)

 theorem signedTrajectory_some_pos (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (i : ι) :
    signedTrajectory X hU C t (some i, true) = X t i := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_some_neg (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (i : ι) :
    signedTrajectory X hU C t (some i, false) = star (X t i) := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_none_pos (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) :
    signedTrajectory X hU C t (none, true) = C := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_none_neg (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) :
    signedTrajectory X hU C t (none, false) = star (C : A) := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_ode [Fintype ι] [DecidableEq ι]
    (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue C l))
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field (laurentValue C l) h (X t)) t)
    (t : ℝ) (ib : Option ι × Bool) :
    HasDerivAt (fun s => signedTrajectory X hU C s ib)
      (NCPolynomial.eval (signedTrajectory X hU C t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t := by
  have hpos (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,true)) =
      coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
        (TraceCocycle.fieldCoefficients h l j) *
        (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) :=
    eval_encodedField_pos _ _ _
  have hneg (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,false)) =
      -(star (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) *
        coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
          (TraceCocycle.fieldCoefficients h l j)) :=
    eval_encodedField_neg _ _ _
  rcases ib with ⟨i,b⟩
  cases i with
  | none =>
    cases b
    · rw [hneg]
      simp only [TraceCocycle.fieldCoefficients, map_zero, mul_zero, neg_zero]
      simpa only [signedTrajectory_none_neg] using hasDerivAt_const t (star (C : A))
    · rw [hpos]
      simp only [TraceCocycle.fieldCoefficients, map_zero, zero_mul]
      simpa only [signedTrajectory_none_pos] using hasDerivAt_const t (C : A)
  | some i =>
    have hi := hasDerivAt_pi.mp (hX t) i
    cases b
    · rw [hneg, coefficientHom_fieldCoefficients]
      have hs := hi.star
      have he : star (PolynomialFlow.field (laurentValue C l) h (X t) i) =
          -(star (X t i) * (Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (X t))) := by
        simp only [PolynomialFlow.field, star_smul, star_mul, Complex.star_def,
          Complex.conj_I, (PolynomialFlow.selfAdjoint_hamiltonian _ hS _ _).star_eq,
          neg_smul, mul_smul_comm]
      rw [he] at hs
      simpa only [signedTrajectory_some_neg, extendUnitary, Option.elim_some] using hs
    · rw [hpos, coefficientHom_fieldCoefficients]
      simpa only [signedTrajectory_some_pos, extendUnitary, Option.elim_some,
        PolynomialFlow.field, smul_mul_assoc] using hi

end FreeGroupFactorMain.UnitaryEvaluation

end

end OAI
