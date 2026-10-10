import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeConstant
import OAI.NumberTheory.CubicMoment.Estimates.PrimeToThreeIdeals

namespace OAI

/-! Finite Euler factors for the actual residue-unit counts in the cubic
Eisenstein constant term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaIdealTotient (ν : EisensteinIdealExponent) : ℕ :=
  Nat.card (Residues (idealExponentGenerator ν))ˣ

lemma cubicTheta_units_one : Nat.card (Residues (1:Eisenstein))ˣ=1 := by
  have he : modulus (1:Eisenstein)=⊤ := Ideal.span_singleton_one
  let : Subsingleton (Residues (1:Eisenstein)) := by
    unfold Residues
    rw [he]
    infer_instance
  exact Nat.card_unique

lemma cubicThetaIdealTotient_zero : cubicThetaIdealTotient 0=1 := by
  unfold cubicThetaIdealTotient
  rw [show idealExponentGenerator 0=1 by simp [idealExponentGenerator]]
  exact cubicTheta_units_one

lemma cubicThetaIdealTotient_add {ν κ : EisensteinIdealExponent}
    (h : ∀ p, ν p=0 ∨ κ p=0) :
    cubicThetaIdealTotient (ν+κ)=cubicThetaIdealTotient ν*cubicThetaIdealTotient κ := by
  unfold cubicThetaIdealTotient
  rw [idealExponentGenerator_add]
  apply cubicTheta_coprime_units_card
  rw [isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν)
    (idealExponentGenerator_ne_zero κ),idealExponentOf_generator,idealExponentOf_generator]
  exact h

lemma cubicThetaIdealTotient_single (p : EisensteinIdealPrime) (n : ℕ) :
    cubicThetaIdealTotient (Finsupp.single p (n+1))=
      normNat (idealPrimeRepresentative p)^n*(normNat (idealPrimeRepresentative p)-1) := by
  unfold cubicThetaIdealTotient idealExponentGenerator
  rw [Finsupp.prod_single_index (h:=fun p k => idealPrimeRepresentative p^k) (pow_zero _),
    cubicTheta_power_units_card (idealPrimeRepresentative_irreducible p).ne_zero]
  have he := cubicTheta_primePower_units_card (idealPrimeRepresentative_irreducible p).prime 0
  rw [show (0+1:ℕ)=1 from rfl,pow_one,pow_zero] at he
  simp only [pow_one] at he
  exact congrArg (fun k => normNat (idealPrimeRepresentative p)^n*k) he

lemma cubicThetaIdealTotient_single_real (p : EisensteinIdealPrime) {n : ℕ} (hn : n≠0) :
    (cubicThetaIdealTotient (Finsupp.single p n):ℝ)=
      idealExponentNorm (Finsupp.single p n)*
        (1-1/(normNat (idealPrimeRepresentative p):ℝ)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [cubicThetaIdealTotient_single,idealExponentNorm_single]
  have hN : 0 < (normNat (idealPrimeRepresentative p):ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (normNat_ne_zero (idealPrimeRepresentative_irreducible p).ne_zero))
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (normNat_ne_zero (idealPrimeRepresentative_irreducible p).ne_zero)),Nat.cast_one,pow_succ]
  field_simp

lemma cubicThetaIdealTotient_euler (ν : EisensteinIdealExponent) :
    (cubicThetaIdealTotient ν:ℝ)=idealExponentNorm ν*
      ∏ p ∈ ν.support, (1-1/(normNat (idealPrimeRepresentative p):ℝ)) := by
  induction ν using Finsupp.induction with
  | zero => simp [cubicThetaIdealTotient_zero,idealExponentNorm,idealExponentGenerator]
  | @single_add p n ν hp hn ih =>
    have hν : ν p=0 := Finsupp.notMem_support_iff.mp hp
    have hs : (Finsupp.single p n+ν).support=insert p ν.support := by
      ext q
      by_cases hqp : q=p
      · subst q
        simp [Finsupp.mem_support_iff,hν,hn]
      · simp [Finsupp.mem_support_iff,hqp]
    have hcop : ∀ q, (Finsupp.single p n) q=0 ∨ ν q=0 := by
      intro q
      by_cases hqp : q=p
      · subst q; exact Or.inr hν
      · left; simp [hqp]
    rw [cubicThetaIdealTotient_add hcop,Nat.cast_mul,cubicThetaIdealTotient_single_real p hn,
      ih,idealExponentNorm_add,hs,Finset.prod_insert hp]
    ring

end CubicFirstMoment

end

end OAI
