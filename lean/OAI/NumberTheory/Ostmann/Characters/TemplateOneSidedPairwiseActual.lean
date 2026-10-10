import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPairwise

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def twoPrimeSampleAssignment {Q : ℕ} (p : I → PrimeUpTo Q) (L S : I)
    (q r : PrimeUpTo Q) : I → PrimeUpTo Q := Function.update (Function.update p L q) S r

omit [Fintype I] in
theorem twoPrimeSampleAssignment_val [Fintype I] {Q : ℕ} (p : I → PrimeUpTo Q) (L S : I)
    (q r : PrimeUpTo Q) (i : I) :
    (twoPrimeSampleAssignment p L S q r i).val =
      twoPrimeAssignment (fun i => (p i).val) L S q.val r.val i := by
  simp only [twoPrimeSampleAssignment,twoPrimeAssignment,Function.update_apply]
  split_ifs <;> rfl

theorem prime_coprime_of_log_lt {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hlog : Real.log q < Real.log r) : q.Coprime r := by
  apply (Nat.coprime_primes hq hr).mpr
  intro he
  rw [he] at hlog
  exact (lt_irrefl _) hlog

theorem prime_coprime_of_log_bands {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {a b : ℝ} (hqa : Real.log q ≤ a) (hab : a < b) (hbr : b ≤ Real.log r) : q.Coprime r :=
  prime_coprime_of_log_lt hq hr ((hqa.trans_lt hab).trans_le hbr)

theorem samplePrimeSupport_twoPrime_indicator (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (p : T.Constituent width → PrimeUpTo Q) (L S : T.Constituent width) (hLS : L ≠ S)
    (q r : PrimeUpTo Q) (hqr : q.val.Coprime r.val) :
    (if samplePrimeSupport T width (twoPrimeSampleAssignment p L S q r) then (1:ℂ) else 0) =
      longPrimeSupportMask (fun i => (p i).val) L S q.val *
        shortPrimeSupportMask (fun i => (p i).val) L S r.val := by
  unfold samplePrimeSupport
  simp_rw [twoPrimeSampleAssignment_val]
  exact twoPrimeAssignment_support_indicator_of_coprime _ L S hLS q.val r.val hqr

theorem samplePrimeSupport_twoPrime_value (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (p : T.Constituent width → PrimeUpTo Q) (L S : T.Constituent width) (hLS : L ≠ S)
    (q r : PrimeUpTo Q) (hqr : q.val.Coprime r.val) (z : ℂ) :
    (if samplePrimeSupport T width (twoPrimeSampleAssignment p L S q r) then z else 0) =
      longPrimeSupportMask (fun i => (p i).val) L S q.val *
        shortPrimeSupportMask (fun i => (p i).val) L S r.val * z := by
  rw [←samplePrimeSupport_twoPrime_indicator T width p L S hLS q r hqr]
  split_ifs <;> simp

omit [Fintype I] [DecidableEq I] in
theorem pairwise_coprime_comp_perm [Fintype I] [DecidableEq I] (p : I → ℕ) (σ : Equiv.Perm I) :
    Pairwise (fun i h => (p (σ i)).Coprime (p (σ h))) ↔
      Pairwise (fun i h => (p i).Coprime (p h)) := by
  constructor
  · intro h i v hiv
    have hh := h (show σ.symm i ≠ σ.symm v from fun he => hiv (σ.symm.injective he))
    simpa only [Equiv.apply_symm_apply] using hh
  · intro h i v hiv
    exact h (fun he => hiv (σ.injective he))

theorem samplePrimeSupport_comp_perm (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (p : T.Constituent width → PrimeUpTo Q) (σ : Equiv.Perm (T.Constituent width)) :
    samplePrimeSupport T width (p ∘ σ) ↔ samplePrimeSupport T width p :=
  by
    simpa only [samplePrimeSupport,Function.comp_apply] using
      pairwise_coprime_comp_perm (fun i => (p i).val) σ

theorem samplePrimeSupport_pair_indicator (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (p : T.Constituent width → PrimeUpTo Q) (σ ρ : Equiv.Perm (T.Constituent width)) :
    (if samplePrimeSupport T width (p ∘ σ) ∧ samplePrimeSupport T width (p ∘ ρ)
      then (1:ℂ) else 0) = if samplePrimeSupport T width p then 1 else 0 := by
  simp only [samplePrimeSupport_comp_perm T width p σ,samplePrimeSupport_comp_perm T width p ρ,and_self]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
