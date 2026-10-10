import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UsedPrimeReciprocal
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TokenSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FactorialTotal
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ChargePivotAbsorption

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma finite_sum_instance_transfer {α : Type*} (I J : Fintype α) (f : α → ℝ) {C : ℝ}
    (hb : @Finset.sum α ℝ _ (@Finset.univ α I) f ≤ C) :
    @Finset.sum α ℝ _ (@Finset.univ α J) f ≤ C := by
  have he : @Finset.univ α J = @Finset.univ α I := by ext x; simp only [mem_univ]
  rw [he]
  exact hb

namespace RecordPacket
lemma charged_code_sum_native {w : ClosedLine h ℓ} {n N : ℕ}
    (K : ℝ) (hK : 0 < K) (hB : UnorderedTokenBound S K τ) (pC pZ : S.Index) :
    (∑ c : FlatCode S w C₀ B L n N, chargedCodeWeight (D := D) K pC pZ c) ≤
      (Fintype.card (ListMetadata ℓ L n):ℝ) * exceptionalCost S ℓ L n N C₀ B *
        factorialTotal S w pC pZ := by
  have hb := charged_code_sum (D := D) (w₀ := w) (L := L) (n := n) (N := N) K hK hB pC pZ
  exact finite_sum_instance_transfer _ _ _ hb
end RecordPacket

noncomputable local instance integrationTokenDec (w : ClosedLine h ℓ) : DecidableEq (TokenType w) := Classical.decEq _

noncomputable def returnCharge (S : PrimeSystem) (T : ℝ) : ℝ :=
  kappa * (S.harmonicCore - T*Real.sqrt S.harmonicCore)

noncomputable def originCharge (S : PrimeSystem) (T : ℝ) : ℝ :=
  returnCharge S T - S.harmonicCore*betaC*(Real.exp kappa-1)

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

lemma nativeWeight_product (x : RecordPacket D L w₀ hh r hr₀ n N) :
    x.nativeWeight = usedPrimeReciprocal x.line x.primitives *
      ∏ p : S.Index, recordTreeWeight x.line hh x.primitives x.record p := by
  exact prod_mul_distrib

theorem majorant_factorization (T err : ℝ) (x : RecordPacket D L w₀ hh r hr₀ n N) :
    traceIntegrationMajorant x.line hh x.primitives x.record T err =
      Real.exp (err-returnCharge S T*(r:ℝ)) *
        Real.exp (-S.harmonicCore*bandDefect w₀ betaC-S.harmonicCenter*bandDefect w₀ betaZ) *
          chargedWeight (originCharge S T) x := by
  unfold traceIntegrationMajorant chargeConstant chargedWeight originCharge returnCharge
  rw [x.returns,x.geometry.bandDefect betaC,x.geometry.bandDefect betaZ,x.nativeWeight_product]
  rw [show (-kappa*(S.harmonicCore-T*Real.sqrt S.harmonicCore)*
      ((r:ℝ)+(recordU x.line x.record.1).card)) =
      -(kappa*(S.harmonicCore-T*Real.sqrt S.harmonicCore))*(r:ℝ)-
      (kappa*(S.harmonicCore-T*Real.sqrt S.harmonicCore))*
        (recordU x.line x.record.1).card by ring]
  rw [← Real.exp_add,← Real.exp_add]
  rw [← mul_assoc,← mul_assoc,← Real.exp_add]
  congr 2
  ring_nf

lemma factorial_background_bound (hh : 0 < h) (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) :
    Real.exp (-S.harmonicCore*bandDefect w₀ betaC-S.harmonicCenter*bandDefect w₀ betaZ) *
      factorialTotal S w₀ pC pZ ≤
      Real.exp (-theta/2*S.harmonicCenter*(goodEdges w₀).card+
        theta*S.harmonicCenter*(badEdges w₀).card) := by
  let vC := S.harmonicCore
  let vZ := S.harmonicCenter
  have hvC : 0 ≤ vC := by unfold vC harmonicCore; exact sum_nonneg (fun p _ => by positivity)
  have hvZ : 0 ≤ vZ := by unfold vZ harmonicCenter; exact sum_nonneg (fun p _ => by positivity)
  let x := fun t : TokenType w₀ => tokenMass w₀ vC vZ t * tokenWeight w₀ pC pZ t
  have hx : ∀ t, 0 ≤ x t := by
    intro t
    apply mul_nonneg
    · dsimp only [tokenMass]
      split_ifs <;> assumption
    · exact tokenWeight_nonneg w₀ pC pZ t
  have hm := OrdinaryCorrelations.FactorialAssignments.multiplicity_sum_bound x hx
    (fun _ => Fintype.card S.Index+1)
  have he := total_token_exponent w₀ hh pC pZ hpC hpZ vC vZ hvC hvZ
  calc
    _ ≤ Real.exp (-vC*bandDefect w₀ betaC-vZ*bandDefect w₀ betaZ) * Real.exp (∑ t, x t) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (-vC*bandDefect w₀ betaC-vZ*bandDefect w₀ betaZ+∑ t, x t) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      dsimp only [x]
      nlinarith only [he]

theorem integrated_record_sum (T err K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1)
    (hq : Real.exp (-originCharge S T) ≤ K) (hB : UnorderedTokenBound S K τ)
    (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) :
    (∑ x : RecordPacket D L w₀ hh r hr₀ n N,
      traceIntegrationMajorant x.line hh x.primitives x.record T err) ≤
      Real.exp (err-returnCharge S T*(r:ℝ)) * K^((goodEdges w₀).card-N) *
        (Fintype.card (ListMetadata ℓ L n):ℝ) * exceptionalCost S ℓ L n N C₀ B *
          Real.exp (-theta/2*S.harmonicCenter*(goodEdges w₀).card+
            theta*S.harmonicCenter*(badEdges w₀).card) := by
  let E := Real.exp (err-returnCharge S T*(r:ℝ))
  let bg := Real.exp (-S.harmonicCore*bandDefect w₀ betaC-S.harmonicCenter*bandDefect w₀ betaZ)
  let C := (Fintype.card (ListMetadata ℓ L n):ℝ) * exceptionalCost S ℓ L n N C₀ B
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (exceptionalCost_nonneg ..)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hbg : 0 ≤ bg := (Real.exp_pos _).le
  have hpow : 0 ≤ K^((goodEdges w₀).card-N) := pow_nonneg hK.le _
  have hc := charged_record_sum_le_codes (D := D) (L := L) (w₀ := w₀) (hh := hh) (hr₀ := hr₀)
    (n := n) (N := N) K (originCharge S T) hK hK1 hq pC pZ hpC hpZ
  have hb := charged_code_sum_native (D := D) (w := w₀) (L := L) (n := n) (N := N) K hK hB pC pZ
  have hm := hc.trans (mul_le_mul_of_nonneg_left hb hpow)
  simp_rw [majorant_factorization T err]
  rw [← mul_sum]
  calc
    _ ≤ (E*bg) * (K^((goodEdges w₀).card-N) * (C * factorialTotal S w₀ pC pZ)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg hE hbg)
    _ = (E*K^((goodEdges w₀).card-N)*C) * (bg*factorialTotal S w₀ pC pZ) := by ring
    _ ≤ (E*K^((goodEdges w₀).card-N)*C) *
        Real.exp (-theta/2*S.harmonicCenter*(goodEdges w₀).card+
          theta*S.harmonicCenter*(badEdges w₀).card) :=
      mul_le_mul_of_nonneg_left (factorial_background_bound (hh := hh) pC pZ hpC hpZ)
        (mul_nonneg (mul_nonneg hE hpow) hC)
    _ = _ := by dsimp only [E,C]; ring

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
