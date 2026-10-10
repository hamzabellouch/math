import OAI.Analysis.GroupDeterminants.IntegralTransfer

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ComplexRegular
variable {G : Type} [Group G] {n : ℕ}

def shiftFunctions : G →* Module.End ℂ (G → ℂ) where
  toFun g := {
    toFun f h := f (g⁻¹ * h)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by ext f h; simp
  map_mul' g h := by ext f a; simp [mul_assoc]

def convolutionHom : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ (G → ℂ) :=
  MonoidAlgebra.lift ℂ (Module.End ℂ (G → ℂ)) G shiftFunctions

theorem convolutionHom_apply (a : MonoidAlgebra ℂ G) (f : G → ℂ) (h : G) :
    convolutionHom a f h = a.coeff.sum fun g z => z * f (g⁻¹ * h) := by
  simp only [convolutionHom, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

local instance functionModule : Module (MonoidAlgebra ℂ G) (G → ℂ) :=
  Module.compHom (G → ℂ) convolutionHom.toRingHom

open scoped Matrix.Module

def complexOperator (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    Hilbert G n →L[ℂ] Hilbert G n :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j).coeff.sum
    (fun g z => z • elementaryOperator i j g)

theorem complexOperator_apply (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G))
    (ξ : Hilbert G n) (i : Fin n) (h : G) :
    complexOperator A ξ (i, h) = ∑ j : Fin n,
      (A i j).coeff.sum fun g z => z * ξ (j, g⁻¹ * h) := by
  classical
  simp only [complexOperator, Finsupp.sum, sum_apply,
    smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, elementaryOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · simp

theorem complexOperator_curry (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G))
    (ξ : Hilbert G n) :
    Function.curry (complexOperator A ξ) = A • Function.curry (ξ : Fin n × G → ℂ) := by
  funext i h
  rw [Matrix.Module.smul_apply]
  simp only [Finset.sum_apply]
  rw [Function.curry_apply, complexOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact (convolutionHom_apply (A i j) (fun g => ξ (j, g)) h).symm

theorem complexOperator_mul (A B : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (A * B) = complexOperator A * complexOperator B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext a
  obtain ⟨i, h⟩ := a
  have he : Function.curry (complexOperator (A * B) ξ) =
      Function.curry (complexOperator A (complexOperator B ξ)) := by
    rw [complexOperator_curry, mul_smul, complexOperator_curry, complexOperator_curry]
  exact congrFun (congrFun he i) h

theorem complexOperator_one : complexOperator (1 : Matrix (Fin n) (Fin n)
    (MonoidAlgebra ℂ G)) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext a
  obtain ⟨i, h⟩ := a
  have he := complexOperator_curry (1 : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) ξ
  rw [one_smul] at he
  exact congrFun (congrFun he i) h

theorem complexOperator_add (A B : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (A + B) = complexOperator A + complexOperator B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext a
  obtain ⟨i, h⟩ := a
  have he : Function.curry (complexOperator (A + B) ξ) =
      Function.curry (complexOperator A ξ) + Function.curry (complexOperator B ξ) := by
    rw [complexOperator_curry, add_smul, complexOperator_curry, complexOperator_curry]
  exact congrFun (congrFun he i) h

theorem complexOperator_zero : complexOperator (0 : Matrix (Fin n) (Fin n)
    (MonoidAlgebra ℂ G)) = 0 := by
  simp [complexOperator, MonoidAlgebra.coeff_zero]

def complexRepresentation : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G) →+*
    (Hilbert G n →L[ℂ] Hilbert G n) where
  toFun := complexOperator
  map_one' := complexOperator_one
  map_mul' := complexOperator_mul
  map_zero' := complexOperator_zero
  map_add' := complexOperator_add

theorem complexOperator_isUnit {A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)}
    (hA : IsUnit A) : IsUnit (complexOperator A) := hA.map complexRepresentation

theorem complexOperator_integer (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    complexOperator (A.map (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))) =
      regularOperator A := by
  classical
  unfold complexOperator regularOperator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (MonoidAlgebra.map (Int.castRingHom ℂ).toAddMonoidHom (A i j)).coeff.sum _ = _
  rw [MonoidAlgebra.coeff_map]
  exact Finsupp.sum_mapRange_index
    (h := fun groupElement coefficient => coefficient • elementaryOperator i j groupElement)
    (fun groupElement => zero_smul ℂ (elementaryOperator i j groupElement))

theorem regularOperator_isUnit {A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)}
    (hA : IsUnit (rationalMatrix A)) : IsUnit (regularOperator A) := by
  let f : MonoidAlgebra ℚ G →+* MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapRingHom G (Rat.castHom ℂ)
  have h := complexOperator_isUnit (hA.map f.mapMatrix)
  have hf : f.comp (MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)) =
      MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) := by
    rw [← MonoidAlgebra.mapRingHom_comp]
    congr 1
  change IsUnit (complexOperator (A.map
    (f.comp (MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ))))) at h
  rw [hf, complexOperator_integer] at h
  exact h

def groupTraceCLM : (Hilbert G n →L[ℂ] Hilbert G n) →L[ℂ] ℂ :=
  ∑ i : Fin n, (innerSL ℂ (identityVector i)).comp
    (ContinuousLinearMap.apply ℂ (Hilbert G n) (identityVector i))

theorem groupTraceCLM_apply (T : Hilbert G n →L[ℂ] Hilbert G n) :
    groupTraceCLM T = groupTrace T := by
  simp [groupTraceCLM, groupTrace]

theorem groupTrace_complex (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    groupTrace (complexOperator A) = ∑ i : Fin n, (A i i).coeff 1 := by
  classical
  unfold groupTrace
  apply Finset.sum_congr rfl
  intro i _
  have hi (ξ : Hilbert G n) : inner ℂ (identityVector i) ξ = ξ (i, 1) := by
    simp [identityVector, lp.inner_single_left, RCLike.inner_apply]
  rw [hi, complexOperator_apply]
  rw [Finset.sum_eq_single i]
  · rw [(A i i).coeff.sum_eq_single 1]
    · simp [identityVector_apply]
    · intro g _ hg
      simp [identityVector_apply, hg]
    · simp
  · intro j _ hji
    simp [identityVector_apply, hji]
  · simp

theorem coefficient_mul_comm (a b : MonoidAlgebra ℂ G) :
    (a * b).coeff 1 = (b * a).coeff 1 := by
  rw [MonoidAlgebra.coeff_mul_apply_left a b, MonoidAlgebra.coeff_mul_apply_right b a]
  simp only [mul_one, one_mul, mul_comm]

theorem groupTrace_complex_mul_comm
    (A B : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    groupTrace (complexOperator A * complexOperator B) =
      groupTrace (complexOperator B * complexOperator A) := by
  classical
  rw [← complexOperator_mul, ← complexOperator_mul, groupTrace_complex, groupTrace_complex]
  simp only [Matrix.mul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact coefficient_mul_comm _ _

end ComplexRegular

end GroupRingDeterminant

end

end OAI
