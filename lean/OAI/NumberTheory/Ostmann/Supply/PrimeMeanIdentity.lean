import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersPrimitiveBound
import OAI.NumberTheory.Ostmann.Supply.PrimePowerTransferBasic

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Ostmann.ZeroDensity MeasureTheory Set
open scoped BigOperators
local instance {q : ℕ} : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

def weightedPrimeSum (φ : ℝ→ℝ) (X : ℝ) (W : ℕ→ℝ) : ℝ :=
  ∑n∈Finset.Ioc 0 ⌊X⌋₊,if n.Prime then Real.log n*W n*φ ((n:ℝ)/X) else 0

def principalFamily (Q : ℕ) (hQ : 0<Q) : PrimitiveFamily Q :=
  ⟨⟨0,hQ⟩,1,DirichletCharacter.isPrimitive_one_level_one⟩

theorem primitiveFamily_principal_iff (Q : ℕ) (hQ : 0<Q) (χ : PrimitiveFamily Q) :
    χ.2.1=1 ↔ χ=principalFamily Q hQ := by
  constructor
  · intro hχ
    rcases χ with ⟨⟨q,hq⟩,χ,hprim⟩
    change χ=1 at hχ
    have hq0 : q=0 := by
      have hcond : χ.conductor=q+1 := hprim
      rw [hχ,DirichletCharacter.conductor_one] at hcond
      omega
    subst q
    subst χ
    rfl
  · rintro rfl
    rfl

theorem smoothPrimeError_add_main {q : ℕ} (χ : DirichletCharacter ℂ q)
    {φ : ℝ→ℝ} (hs : tsupport φ ⊆ Ioo (1/2:ℝ) 1) {X : ℝ} (hX : 0<X) :
    smoothPrimeError χ φ X+(if χ=1 then ((X*∫t in Ioi (0:ℝ),φ t:ℝ):ℂ) else 0) =
      ∑n∈Finset.Ioc 0 ⌊X⌋₊,(if n.Prime then (Real.log n:ℂ)*χ n else 0)*
        (φ ((n:ℝ)/X):ℂ) := by
  classical
  unfold smoothPrimeError
  rw [sub_add_cancel]
  exact smooth_tsum_eq_finite _ hs hX

theorem weightedPrimeSum_expansion_generic {α : Type*} [Fintype α]
    (q : α→ℕ) (χ : ∀i,DirichletCharacter ℂ (q i)) (c : α→ℂ)
    (W : ℕ→ℝ) {φ : ℝ→ℝ} (hs : tsupport φ ⊆ Ioo (1/2:ℝ) 1) {X : ℝ} (hX : 0<X)
    (hexp : ∀n:ℕ,n.Prime → φ ((n:ℝ)/X)≠0 →
      (W n:ℂ)=∑i:α,c i*χ i n) :
    (weightedPrimeSum φ X W:ℂ)=∑i:α,c i*
      (smoothPrimeError (χ i) φ X+
        if χ i=1 then ((X*∫t in Ioi (0:ℝ),φ t:ℝ):ℂ) else 0) := by
  classical
  simp_rw [smoothPrimeError_add_main _ hs hX,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [weightedPrimeSum,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp,ite_true]
    by_cases hφ : φ ((n:ℝ)/X)=0
    · simp only [hφ,Complex.ofReal_zero,mul_zero,Finset.sum_const_zero]
    · simp only [Complex.ofReal_mul]
      rw [hexp n hp hφ,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
  · simp only [hp,ite_false,Complex.ofReal_zero,zero_mul,mul_zero,Finset.sum_const_zero]

theorem weightedPrimeSum_expansion {Q : ℕ} (c : PrimitiveFamily Q→ℂ)
    (W : ℕ→ℝ) {φ : ℝ→ℝ} (hs : tsupport φ ⊆ Ioo (1/2:ℝ) 1) {X : ℝ} (hX : 0<X)
    (hexp : ∀n:ℕ,n.Prime → φ ((n:ℝ)/X)≠0 →
      (W n:ℂ)=∑χ:PrimitiveFamily Q,c χ*χ.2.1 n) :
    (weightedPrimeSum φ X W:ℂ)=∑χ:PrimitiveFamily Q,c χ*
      (smoothPrimeError χ.2.1 φ X+
        if χ.2.1=1 then ((X*∫t in Ioi (0:ℝ),φ t:ℝ):ℂ) else 0) :=
  weightedPrimeSum_expansion_generic (α:=PrimitiveFamily Q)
    (fun χ : PrimitiveFamily Q => χ.1.val+1)
    (fun χ : PrimitiveFamily Q => χ.2.1) c W hs hX hexp

theorem sum_primitive_principal_term {Q : ℕ} (hQ : 0<Q) (c : PrimitiveFamily Q→ℂ) (M : ℂ) :
    (∑χ:PrimitiveFamily Q,c χ*(if χ.2.1=1 then M else 0))=c (principalFamily Q hQ)*M := by
  classical
  simp_rw [primitiveFamily_principal_iff Q hQ,mul_ite,mul_zero]
  simp

theorem weightedPrimeSum_sub_main {Q : ℕ} (hQ : 0<Q) (c : PrimitiveFamily Q→ℂ)
    (W : ℕ→ℝ) {φ : ℝ→ℝ} (hs : tsupport φ ⊆ Ioo (1/2:ℝ) 1) {X : ℝ} (hX : 0<X)
    (hexp : ∀n:ℕ,n.Prime → φ ((n:ℝ)/X)≠0 →
      (W n:ℂ)=∑χ:PrimitiveFamily Q,c χ*χ.2.1 n) :
    (weightedPrimeSum φ X W:ℂ)-c (principalFamily Q hQ)*
      ((X*∫t in Ioi (0:ℝ),φ t:ℝ):ℂ)=∑χ:PrimitiveFamily Q,c χ*smoothPrimeError χ.2.1 φ X := by
  rw [weightedPrimeSum_expansion c W hs hX hexp]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [sum_primitive_principal_term hQ c,add_sub_cancel_right]

end Ostmann.Supply

end

end OAI
