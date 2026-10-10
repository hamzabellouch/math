import Mathlib
import OAI.Analysis.Commutator.CyclePairTrace

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J I : Type*} [Fintype J] [LinearOrder J] [Fintype I] [DecidableEq I]

def endpointPairingPerm (σ : Pairing J) : Equiv.Perm (Option J) := Equiv.optionCongr σ.val

omit [Fintype J] [LinearOrder J] in
@[simp] lemma endpointPairingPerm_none (σ : Pairing J) : endpointPairingPerm σ none = none := rfl

omit [Fintype J] [LinearOrder J] in
@[simp] lemma endpointPairingPerm_some (σ : Pairing J) (j : J) :
    endpointPairingPerm σ (some j) = some (σ j) := rfl

def optionPairRepresentative (σ : Pairing J) : Option J → Option (Pairing.Representatives σ)
  | none => none
  | some j => some ⟨Pairing.repr σ j, Pairing.repr_lt_apply σ j⟩

omit [Fintype J] in
lemma optionPairRepresentative_apply (σ : Pairing J) (j : Option J) :
    optionPairRepresentative σ (endpointPairingPerm σ j) = optionPairRepresentative σ j := by
  cases j with
  | none => rfl
  | some j => simp only [endpointPairingPerm_some, optionPairRepresentative,
      Pairing.repr_apply]

def endpointPairingCycleEquiv (σ : Pairing J) :
    cycleSet (endpointPairingPerm σ) ≃ Option (Pairing.Representatives σ) where
  toFun := Quotient.lift (optionPairRepresentative σ)
    (fun _ _ h => constant_on_cycle (endpointPairingPerm σ)
      (optionPairRepresentative σ) (optionPairRepresentative_apply σ) h)
  invFun
    | none => cycleMap (endpointPairingPerm σ) none
    | some r => cycleMap (endpointPairingPerm σ) (some r.1)
  left_inv q := by
    refine Quotient.inductionOn q (fun j => ?_)
    cases j with
    | none => rfl
    | some j =>
      change cycleMap (endpointPairingPerm σ) (some (Pairing.repr σ j)) =
        cycleMap (endpointPairingPerm σ) (some j)
      rcases le_total j (σ j) with h | h
      · rw [Pairing.repr, min_eq_left h]
      · rw [Pairing.repr, min_eq_right h]
        exact cycleMap_apply (endpointPairingPerm σ) (some j)
  right_inv r := by
    cases r with
    | none => rfl
    | some r =>
      change some (⟨Pairing.repr σ r, _⟩ : Pairing.Representatives σ) = some r
      congr 1
      apply Subtype.ext
      exact Pairing.repr_representative σ r

lemma cycleCount_endpointPairing (σ : Pairing J) :
    cycleCount (endpointPairingPerm σ) = Fintype.card (Pairing.Representatives σ) + 1 := by
  have hh := Fintype.card_congr (endpointPairingCycleEquiv σ)
  simpa only [cycleCount, Fintype.card_option] using hh

theorem rawCycleTrace_option {𝕜 : Type*} [CommRing 𝕜]
    (σ : Equiv.Perm J) (A : Option J → Matrix I I 𝕜) :
    rawCycleTrace (Equiv.optionCongr σ) A =
      Matrix.trace (A none) * rawCycleTrace σ (fun j => A (some j)) := by
  classical
  rw [rawCycleTrace_eq_sum, rawCycleTrace_eq_sum]
  simp only [Fintype.prod_option, Equiv.optionCongr_apply, Option.map_none, Option.map_some]
  calc
    _ = ∑ b : I × (J → I), A none b.1 b.1 * ∏ j, A (some j) (b.2 (σ j)) (b.2 j) := by
      exact Fintype.sum_equiv Equiv.piOptionEquivProd _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rfl

theorem cycleTrace_endpointPairing (σ : Pairing J) (A : Option J → Matrix I I ℂ) :
    cycleTrace (endpointPairingPerm σ) A =
      (Fintype.card I : ℂ)⁻¹ * Matrix.trace (A none) *
        Pairing.contraction σ (fun X Y => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
          (fun j => A (some j)) := by
  classical
  rw [cycleTrace, cycleCount_endpointPairing]
  change (Fintype.card I : ℂ)⁻¹ ^ (Fintype.card (Pairing.Representatives σ) + 1) *
    rawCycleTrace (Equiv.optionCongr σ.val) A = _
  rw [rawCycleTrace_option, rawCycleTrace_pairing, pow_succ]
  have hc : Pairing.contraction σ
      (fun (X Y : Matrix I I ℂ) => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
        (fun j => A (some j)) =
      (Fintype.card I : ℂ)⁻¹ ^ Fintype.card (Pairing.Representatives σ) *
        ∏ r : Pairing.Representatives σ, Matrix.trace (A (some r.1) * A (some (σ r))) := by
    unfold Pairing.contraction
    rw [Finset.prod_subtype (p := fun j => j < σ j) (F := inferInstance) _ (by simp)]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
  rw [hc]
  ring

end Kadison.SchurWeyl
end

end OAI
