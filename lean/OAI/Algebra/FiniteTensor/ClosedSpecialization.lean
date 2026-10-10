import Mathlib
import OAI.Algebra.FiniteTensor.PositiveObstruction
import OAI.Algebra.FiniteTensor.ScalarModels

namespace OAI

/-! Closed-point specialization of finite-type tensor models. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading

 
theorem intJacobson : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro I hI
  by_cases h : I = ⊥
  · subst I
    apply le_antisymm
    · intro x hx
      have hu := Ideal.mem_jacobson_bot.mp hx (3 : ℤ)
      rcases Int.isUnit_eq_one_or hu with h | h <;>
        simp only [Ideal.mem_bot] <;> omega
    · exact Ideal.le_jacobson
  · let : I.IsMaximal := hI.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

 

theorem field_finiteType_char_ne_zero (E : Type*) [Field E]
    [Algebra.FiniteType ℤ E] : ringChar E ≠ 0 := by
  let : IsJacobsonRing ℤ := intJacobson
  let : Module.Finite ℤ E := finite_of_finite_type_of_isJacobsonRing ℤ E
  intro hz
  have : CharP E 0 := hz ▸ (inferInstance : CharP E (ringChar E))
  have : CharZero E := CharP.charP_to_charZero E
  exact Int.not_isField (isField_of_isIntegral_of_isField
    (FaithfulSMul.algebraMap_injective ℤ E) (Field.toIsField E))

 

theorem exists_odd_closed_point (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra.FiniteType ℤ A] (h2 : IsUnit (2 : A)) :
    ∃ I : Ideal A, I.IsMaximal ∧ (ringChar (A ⧸ I)).Prime ∧ ringChar (A ⧸ I) ≠ 2 := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal A
  let : I.IsMaximal := hI
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Algebra.FiniteType ℤ (A ⧸ I) := Algebra.FiniteType.quotient ℤ I
  have hp : (ringChar (A ⧸ I)).Prime :=
    (CharP.char_is_prime_or_zero (A ⧸ I) (ringChar (A ⧸ I))).resolve_right
      (@field_finiteType_char_ne_zero (A ⧸ I) (Ideal.Quotient.field I) (by
        convert (Algebra.FiniteType.quotient ℤ I) using 1
        rfl))
  refine ⟨I,hI,hp,?_⟩
  intro heq
  have hu : IsUnit (2 : A ⧸ I) := by
    simpa only [map_ofNat] using (Ideal.Quotient.mk I).isUnit_map h2
  apply hu.ne_zero
  have hz := CharP.cast_eq_zero (A ⧸ I) (ringChar (A ⧸ I))
  simpa only [heq,Nat.cast_ofNat] using hz

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
universe u
variable {l : ℕ} (σ : Fin l → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

 

theorem no_tensor_model_field (K : Type*) [Field K] (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : p ≠ 2) {m d c : ℕ} (e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c)
    (hm : 5 ≤ m) (active : Fin m ↪ Fin l) (M : TensorModel K σ m d c e active) : False := by
  have h2 : (2 : K) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2
  let : Invertible (2 : K) := invertibleOfNonzero h2
  have hc := PD4Tensor.joinedMatrix_complementary e
    (fun i j => augmentation K m (MvPowerSeries.coeff (Finsupp.single j 1) (M.H i)))
    (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (M.G i)) M.tangent_unit.ne_zero
  exact PD4Tensor.TruncatedForms.formal_active_obstruction_any K σ p e hm
    M.F active M.b M.H M.G M.H_zero M.G_zero hc.1 hc.2.1 hc.2.2
    M.left_vanishing M.right_vanishing M.left_triple M.right_triple

 

theorem no_tensor_model_finiteType (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra.FiniteType ℤ A] (h2 : IsUnit (2 : A)) {m d c : ℕ}
    (e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c) (hm : 5 ≤ m) (active : Fin m ↪ Fin l) :
    IsEmpty (TensorModel A σ m d c e active) := by
  constructor
  intro M
  obtain ⟨I,hI,hp,hp2⟩ := exists_odd_closed_point A h2
  let : I.IsMaximal := hI
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Fact (ringChar (A ⧸ I)).Prime := ⟨hp⟩
  exact no_tensor_model_field σ (A ⧸ I) (ringChar (A ⧸ I)) hp2 e hm active
    (M.map (Ideal.Quotient.mk I))

end
end PD4Tensor.Spreading
end

end OAI
