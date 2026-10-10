import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace AdicCofinal
variable {R : Type*} [CommRing R]

lemma factor_eval (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  have hn : (I ^ n • ⊤ : Ideal R) = I ^ n := by simp
  have hm : (I ^ m • ⊤ : Ideal R) = I ^ m := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x hn.le,
    ← AdicCompletion.factor_eval_eq_evalₐ I x hm.le]
  have hx := congrArg (Ideal.Quotient.factor hm.le) (x.property h)
  simpa only [AdicCompletion.eval_apply, AdicCompletion.transitionMap,
    Submodule.factorPow, Submodule.mapQ_eq_factor, Submodule.factor_eq_factor,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply] using hx

def family (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ J ^ n :=
  (Ideal.Quotient.factor (hc n)).comp (AdicCompletion.evalₐ I (n+c)).toRingHom

lemma family_compatible (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (family I J c hc n) =
      family I J c hc m := by
  ext x
  have hx := factor_eval I (Nat.add_le_add_right h c) x
  have hy := congrArg (Ideal.Quotient.factor (hc m)) hx
  simpa only [family, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply] using hy

noncomputable def map (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n) :
    AdicCompletion I R →+* AdicCompletion J R :=
  AdicCompletion.liftRingHom J (family I J c hc) (family_compatible I J c hc)

@[simp] lemma eval_map (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (map I J c hc x) =
      Ideal.Quotient.factor (hc n) (AdicCompletion.evalₐ I (n+c) x) := by
  exact AdicCompletion.evalₐ_liftRingHom J (family I J c hc)
    (family_compatible I J c hc) n x

lemma map_map (I J : Ideal R) (c d : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n)
    (hd : ∀ n, J ^ (n + d) ≤ I ^ n) (x : AdicCompletion I R) :
    map J I d hd (map I J c hc x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [eval_map]
  have he := factor_eval I (show n ≤ (n+d)+c by omega) x
  simpa only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply] using he

noncomputable def equiv (I J : Ideal R) (c d : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n)
    (hd : ∀ n, J ^ (n + d) ≤ I ^ n) :
    AdicCompletion I R ≃+* AdicCompletion J R :=
  { map I J c hc with
    invFun := map J I d hd
    left_inv := map_map I J c d hc hd
    right_inv := map_map J I d c hd hc }

@[simp] lemma equiv_of (I J : Ideal R) (c d : ℕ)
    (hc : ∀ n, I ^ (n + c) ≤ J ^ n)
    (hd : ∀ n, J ^ (n + d) ≤ I ^ n) (r : R) :
    equiv I J c d hc hd (AdicCompletion.of I R r) = AdicCompletion.of J R r := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n (map I J c hc _) = _
  simp

end AdicCofinal
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace AdicFunctor
variable {R S : Type*} [CommRing R] [CommRing S]

lemma map_pow_le (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hf) n

def quotient (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) : R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap _ f (map_pow_le I J f hf n)

lemma quotient_compatible (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (quotient I J f hf n) =
    (quotient I J f hf m).comp (Ideal.Quotient.factorPow I h) := by
  ext x
  rfl

def family (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
  (quotient I J f hf n).comp (AdicCompletion.evalₐ I n).toRingHom

lemma family_compatible (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (family I J f hf n) =
      family I J f hf m := by
  ext x
  have he := congrArg (fun g : R ⧸ I ^ n →+* S ⧸ J ^ m ↦
    g (AdicCompletion.evalₐ I n x)) (quotient_compatible I J f hf h)
  simpa only [RingHom.comp_apply,AdicCofinal.factor_eval,family,
    AlgHom.toRingHom_eq_coe,RingHom.coe_coe] using he

noncomputable def map (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (family I J f hf) (family_compatible I J f hf)

@[simp] lemma eval_map (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (map I J f hf x) =
      quotient I J f hf n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J (family I J f hf)
    (family_compatible I J f hf) n x

@[simp] lemma map_of (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (r : R) :
    map I J f hf (AdicCompletion.of I R r) = AdicCompletion.of J S (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [quotient]

end AdicFunctor
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
