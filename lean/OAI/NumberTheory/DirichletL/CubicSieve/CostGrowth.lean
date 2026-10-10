import OAI.NumberTheory.DirichletL.CubicSieve.B2Growth
import OAI.NumberTheory.DirichletL.CubicSieve.DescendantBounds
import OAI.NumberTheory.DirichletL.CubicDyadicDecay

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open SecondPassArithmetic EisensteinSchwartzPoisson SevenEighths.CubicDyadicDecay
noncomputable section

theorem HasCubicExponent.frequencyCost_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1/2) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε : ℝ, 0 ≤ C → ∀ hε : 0 < ε,
      ∀ X Y : ℝ, 0 < X → 1 ≤ Y →
        frequencyCost C ε hε X Y ≤
          (X*(2/Y))*‖paperRadialFourier rowMajorant 0‖ +
          (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A) * Y^ε *
            (Y^(3*δ)*X^(-δ) * (decayConstant (1/3+δ)*(X*Y)^(2/3 : ℝ) +
              decayConstant (ξ+δ)*X^(1-ξ)*Y^(2*ξ-1))) := by
  obtain ⟨A,hA,hb⟩ := h.full_element_bound hξ δ hδ
  refine ⟨A,hA,?_⟩
  intro C ε hC hε X Y hX hY
  have hY0 : 0 < Y := by linarith
  have hs := sieve_poisson_bound (fun K => elementSieveNorm K Y) A X Y δ ξ hA.le hX hY0
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun K hK => elementSieveNorm_nonneg K Y)
    (fun K hK => by simpa only [mul_comm Y (K^(1/3 : ℝ))] using hb K Y hK hY)
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*Y^ε := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  have he := add_le_add_left hh ((X*(2/Y))*‖paperRadialFourier rowMajorant 0‖)
  convert he using 1 <;> try dsimp only [frequencyCost, frequencyMajorant]
  all_goals ring

theorem frequencyCost_descendant_of_bound (C ε A δ ξ M N d e : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hα3 : 1/3+δ < 3) (hβ3 : ξ+δ < 3)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d) (hdN : d ≤ N)
    (hb : frequencyCost C ε hε (M/e) (N/d) ≤
      ((M/e)*(2/(N/d)))*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*(N/d)^ε*
        ((N/d)^(3*δ)*(M/e)^(-δ) *
          (decayConstant (1/3+δ)*((M/e)*(N/d))^(2/3 : ℝ) +
            decayConstant (ξ+δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)))) :
    frequencyCost C ε hε (M/e) (N/d) ≤
      2*M*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*N^ε*
        (N^(3*δ)*M^(-δ) *
          (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
            decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1))) := by
  have hd : 1 ≤ d := he.trans hed
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hp := (decayConstant_pos (1/3+δ) (by linarith) hα3).le
  have hq := (decayConstant_pos (ξ+δ) (by linarith) hβ3).le
  have henv := poisson_envelope_descendant_le M N e d δ ξ
    (decayConstant (1/3+δ)) (decayConstant (ξ+δ)) hM hN he hed hδ hξ hp hq
  have hny : (N/d)^ε ≤ N^ε := Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd) hε.le
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (descendant_unit_scale_le M N d e hM.le hN hd he hdN) (norm_nonneg _)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hny hfac
    · exact henv
    · positivity
    · positivity

lemma poisson_envelope_absorb (M N δ ε ξ H Z P Q : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    2*M*Z + H*N^ε*(N^(3*δ)*M^(-δ)*
      (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1))) ≤
        (2*Z+H*(P+Q))*N^(3*δ+ε)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let X := (M*N)^(2/3 : ℝ)
  let Y := M^(1-ξ)*N^(2*ξ-1)
  let S := M+X+Y
  have hX : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hshape : P*X+Q*Y ≤ (P+Q)*S := by
    dsimp only [S]
    nlinarith [mul_nonneg hP hM0.le, mul_nonneg hQ hM0.le, mul_nonneg hP hY, mul_nonneg hQ hX]
  have hsmall : M^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hloss : 1 ≤ N^(3*δ+ε) := Real.one_le_rpow hN (by positivity)
  have hunit : 2*M*Z ≤ 2*Z*N^(3*δ+ε)*S := by
    have hmS : M ≤ S := by dsimp [S]; linarith
    calc
      _ = 2*Z*M := by ring
      _ ≤ 2*Z*S := mul_le_mul_of_nonneg_left hmS (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Z) hS) (sub_nonneg.mpr hloss)]
  have htail : H*N^ε*(N^(3*δ)*M^(-δ)*(P*X+Q*Y)) ≤
      H*(P+Q)*N^(3*δ+ε)*S := by
    have hs : M^(-δ)*(P*X+Q*Y) ≤ (P+Q)*S :=
      (mul_le_of_le_one_left (by positivity) hsmall).trans hshape
    have hpow : N^ε*N^(3*δ) = N^(3*δ+ε) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = H*(N^ε*N^(3*δ))*(M^(-δ)*(P*X+Q*Y)) := by ring
      _ ≤ H*(N^ε*N^(3*δ))*((P+Q)*S) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [hpow]; ring
  have hh := add_le_add hunit htail
  convert hh using 1 <;> dsimp only [S,X,Y] <;> ring

end
end SevenEighths.CubicSieve

end OAI
