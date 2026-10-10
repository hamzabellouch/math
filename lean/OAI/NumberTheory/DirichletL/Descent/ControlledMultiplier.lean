import OAI.NumberTheory.DirichletL.Descent.ActiveReflection

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance controlledField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis ⧸ P) := Ideal.Quotient.field _
noncomputable local instance controlledFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_phase_product (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) (x : Eis) :
    star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) (v i) := by
  have hbad : A4BadPhase c0 hc0 (D.matrix v 1 1) D.U x =
      A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x := by
    apply A4BadPhase_eq_of_residue
    convert dvd_mul_of_dvd_left (D.inverse_fixed hN v) D.U using 1 ; ring
  have hlocal := A3_A4_frequency_product p hp hcop hg (D.matrix v 0 0) (D.matrix v 0 1)
    c0 (D.matrix v 1 1) D.U D.w x hc0 (D.determinant v) D.bezout D.sigma D.epsilon
    (fun i => (v i : Eis ⧸ Ideal.span {p i})) (D.frequency_congruence v) D.epsilon_value
  rw [D.relative_character hN hr hbase v, star_mul]
  calc
    _ = star D.fixedFactor * (star (eisEmbedding (symbol (D.matrix v 0 0) (∏ i, p i))) *
        ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
          (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) := by ring
    _ = _ := by rw [hlocal, hbad]; ring

def fullLocalFourierWeight [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) : ℂ :=
  ∏ i, finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) (v i)

theorem controlled_local_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ, fullLocalFourierWeight hp F v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, ∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
        finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) v *
          frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
            (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_assoc, controlled_phase_product D hN hr hbase hp hc0 hcop hg v x]
  simp only [fullLocalFourierWeight, Finset.prod_mul_distrib]
  ring

def mixedActiveBracket [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) : ℂ :=
  if i ∈ S then
    (rootCard (Eis ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
      tau (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 2 *
        (((actualSextic (Ideal.span {p i}) (hg i)) ^ 2)⁻¹)
          ((D.sigma i : Eis ⧸ Ideal.span {p i}) * (D.epsilon i : Eis ⧸ Ideal.span {p i}) *
            Ideal.Quotient.mk _ x)
  else (((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i) *
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

theorem mixedActiveBracket_eq_units [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (D : ControlledStratumArithmetic p N a0 c0 mode) (i : ι) (x : Eis) :
    (∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
      finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (mixedPrimeFunction p hg j S i) v *
        frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
          (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v) =
      mixedActiveBracket hp hg j S D i x := by
  have hh := actual_mixed_frequency_units (Ideal.span {p i}) (hg i) (hc i)
    (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (decide (i ∈ S)) (j i) (hj i) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x)
  have hfun : mixedPrimeFunction p hg j S i = fun t =>
      if i ∈ S then zeroMark t else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) t := rfl
  rw [hfun]
  by_cases hi : i ∈ S
  · simpa only [hi, decide_true, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      ite_true, markedFrequencyRow] using hh
  · simpa only [hi, decide_false, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      Bool.false_eq_true, ite_false, frequencyRow] using hh

theorem controlled_mixed_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, mixedActiveBracket hp hg j S D i x := by
  rw [controlled_local_multiplier D hN hr hbase hp hc0 hcop hg]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact mixedActiveBracket_eq_units hp hg hc j hj S D i x

end
end SevenEighths.InverseMoment

end OAI
