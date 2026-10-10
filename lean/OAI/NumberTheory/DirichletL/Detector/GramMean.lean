import OAI.NumberTheory.DirichletL.Detector.GramGlobalExtension

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma actualSextic_power_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2) (e : ℕ) (he : ¬6∣e) :
    actualSextic P hg^e≠1 := by
  intro h
  have hd := (orderOf_dvd_iff_pow_eq_one).mpr h
  rw [actualSextic_order_six P hg hchar] at hd
  exact he hd

theorem primePower_mean_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) [Fintype (O⧸P^c)] (d : O) :
    (∑x : O⧸P^c,(actualSextic P hg^e)
      (Ideal.Quotient.mk P d*primePowerReduction P hc x))=0 := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  simp_rw [map_mul]
  rw [←Finset.mul_sum,sum_reduction _ (primePowerReduction_surjective P hc),
    MulChar.sum_eq_zero_of_ne_one (actualSextic_power_nonprincipal P hg hchar e he),mul_zero,mul_zero]

theorem crt_joint_mean_zero (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : (O⧸Q)→(O⧸Q*P^c)→ℂ) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P d*
        primePowerReduction P hc ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).2))*
      F ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).1) y)=0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have heq := E.toEquiv.sum_comp (fun p : (O⧸Q)×(O⧸P^c)=>
    (actualSextic P hg^e) (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y)
  change (∑x : O⧸Q*P^c,(actualSextic P hg^e)
    (Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2)*F (E x).1 y)=0
  calc
    _ = ∑p : (O⧸Q)×(O⧸P^c),(actualSextic P hg^e)
        (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y := heq
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.sum_mul,primePower_mean_zero P hg hchar c e hc he d,zero_mul]
      simp

end SevenEighths.ProbeGramCommon
end

end OAI
