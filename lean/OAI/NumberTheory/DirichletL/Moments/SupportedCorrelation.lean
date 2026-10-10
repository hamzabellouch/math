import OAI.NumberTheory.DirichletL.Moments.CommonSupport
import OAI.NumberTheory.DirichletL.Moments.Mask

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

def supportedModulusCharacter (d : O) (hd : Supported (Ideal.span {d})) :
    MulChar (Residue d) ℂ where
  toFun x := Quotient.liftOn' x (fun z => idealRowHom z (Ideal.span {d})) (by
    intro x y hxy
    exact idealRowHom_congr_mod _ x y ((Ideal.span {d}).quotientRel_def.mp hxy))
  map_one' := idealRowHom_one_supported _ hd
  map_mul' := by
    intro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact idealRowHom_argument_mul x y _
  map_nonunit' := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change idealRowHom x (Ideal.span {d}) = 0
    by_contra hn
    have hm := idealRowHom_sixth_mask x (Ideal.span {d}) hd
    rw [idealRowHom_argument_pow x 6 _ hd, Ideal.isCoprime_span_singleton_iff] at hm
    have hcop : IsCoprime d x := by
      by_contra h
      rw [ite_eq_right h] at hm
      exact (pow_ne_zero 6 hn) hm
    exact hx (isUnit_residue_of_coprime d x hcop)

@[simp] theorem supportedModulusCharacter_mk (d : O)
    (hd : Supported (Ideal.span {d})) (x : O) :
    supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) = idealRowHom x (Ideal.span {d}) := rfl

lemma supported_mul_elements (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) :
    Supported (Ideal.span {d * a}) := by
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact (supported_mul_iff _ _).mpr ⟨hd, ha⟩

theorem supportedModulusCharacter_mul (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) (x : O) :
    supportedModulusCharacter (d * a) (supported_mul_elements d a hd ha) (Ideal.Quotient.mk _ x) =
      supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ x) := by
  simp only [supportedModulusCharacter_mk, ← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma sexticReciprocityPhase_symm (a b : O) :
    sexticReciprocityPhase a b = sexticReciprocityPhase b a := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

@[simp] lemma star_sexticReciprocityPhase (a b : O) :
    star (sexticReciprocityPhase a b) = sexticReciprocityPhase a b := by
  simp only [sexticReciprocityPhase, star_intCast]

theorem supported_opposite_phase (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcop : IsCoprime a b) [Fintype (Residue a)] :
    idealRowHom a (Ideal.span {b}) * star (idealRowHom b (Ideal.span {a})) =
      sexticReciprocityPhase a b := by
  rw [idealRowHom_primary_reciprocity b a hpb hpa hb ha,
    sexticReciprocityPhase_symm b a, mul_assoc]
  have hunit := isUnit_residue_of_coprime a b hcop
  have hn := (supportedModulusCharacter a ha).apply_ne_zero_iff.mpr hunit
  change idealRowHom b (Ideal.span {a}) ≠ 0 at hn
  have heq : idealRowHom b (Ideal.span {a}) * star (idealRowHom b (Ideal.span {a})) = 1 := by
    change supportedModulusCharacter a ha (Ideal.Quotient.mk _ b) *
      star (supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)) = 1
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ hn
  rw [heq, mul_one]

def supportedCorrelation (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v}))
    [Fintype (Residue u)] [Fintype (Residue v)] (j : O) : ℂ :=
  fullModulusCorrelation u v (supportedModulusCharacter u hu) (supportedModulusCharacter v hv) j

theorem supported_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))] (j : O) :
    supportedCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      supportedCorrelation D E hD hE j * sexticReciprocityPhase a E *
        star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
        idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b})) := by
  unfold supportedCorrelation
  rw [fullModulusCorrelation_complete_support D E a b hcopA hcopB hab
    (supportedModulusCharacter D hD) (supportedModulusCharacter E hE)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)
    (supportedModulusCharacter (D * a) (supported_mul_elements D a hD ha))
    (supportedModulusCharacter (E * b) (supported_mul_elements E b hE hb))
    (supportedModulusCharacter_mul D a hD ha) (supportedModulusCharacter_mul E b hE hb) j]
  simp only [supportedModulusCharacter_mk]
  rw [supported_opposite_phase a E ha hE hpa hpE (IsCoprime.mul_left_iff.mp hcopA).2.symm,
    supported_opposite_phase D b hD hb hpD hpb (IsCoprime.mul_left_iff.mp hcopB).1,
    supported_opposite_phase a b ha hb hpa hpb hab,
    sexticReciprocityPhase_symm D b, star_sexticReciprocityPhase]

lemma supported_element_ne_zero (d : O) (hd : Supported (Ideal.span {d})) : d ≠ 0 := by
  intro h
  exact hd.1 (by simp [h])

def actualCorrelation (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (j : O) : ℂ := by
  letI := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  letI := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  letI : Fintype (Residue u) := Fintype.ofFinite _
  letI : Fintype (Residue v) := Fintype.ofFinite _
  exact supportedCorrelation u v hu hv j

def completeSupportExtension (D E : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (j a b : O) : ℂ :=
  actualCorrelation D E hD hE j * sexticReciprocityPhase a E *
    star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
    idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b}))

theorem actual_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    (j : O) :
    actualCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      completeSupportExtension D E hD hE j a b := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero D hD)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero E hE)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero D hD) (supported_element_ne_zero a ha))
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero E hE) (supported_element_ne_zero b hb))
  let : Fintype (Residue D) := Fintype.ofFinite _
  let : Fintype (Residue E) := Fintype.ofFinite _
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (D * a)) := Fintype.ofFinite _
  let : Fintype (Residue (E * b)) := Fintype.ofFinite _
  exact supported_complete_common_support D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB hab j

theorem actual_complete_support_mobius (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (j : O) :
    (if IsCoprime a b then actualCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j else 0) =
      completeSupportExtension D E hD hE j a b *
        ∑ T ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {b}),
          if T ∣ Ideal.span {a} then (UniqueFactorizationMonoid.moebius T : ℂ) else 0 := by
  rw [← CenteredMomentMask.ideal_coprime_mobius (Ideal.span {a}) (Ideal.span {b}) hb.1,
    Ideal.isCoprime_span_singleton_iff]
  by_cases hab : IsCoprime a b
  · rw [ite_eq_left hab, ite_eq_left hab, mul_one]
    exact actual_complete_common_support D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB hab j
  · simp only [hab, ite_false, mul_zero]

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI
