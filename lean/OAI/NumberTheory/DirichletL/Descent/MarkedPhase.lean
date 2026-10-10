import OAI.NumberTheory.DirichletL.Descent.ReflectedDual

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance markedPhaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def markedActiveExponent (S : Finset ι) (j : ι → ℕ) (i : ι) : ℕ := if i ∈ S then 0 else j i

theorem mixedActiveBracket_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) :
    mixedActiveBracket hp hg j S D i x = (if i ∈ S then (-1 : ℂ) else 1) *
      ((((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i))
          (markedActiveExponent S j i) (D.epsilon i) *
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (markedActiveExponent S j i)
          (Ideal.Quotient.mk _ x)) := by
  by_cases hi : i ∈ S
  · simp only [mixedActiveBracket, markedActiveExponent, hi,
      phase, bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
    ring
  · simp only [mixedActiveBracket, markedActiveExponent, hi, ite_false, one_mul]

theorem mixedActiveBracket_product [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode) (x : Eis) :
    (∏ i, mixedActiveBracket hp hg j S D i x) =
      (-1 : ℂ) ^ S.card * D.bracketProduct hp hg (markedActiveExponent S j) x := by
  simp_rw [mixedActiveBracket_eq_signed]
  rw [Finset.prod_mul_distrib]
  have hsign : (∏ i : ι, if i ∈ S then (-1 : ℂ) else 1) = (-1 : ℂ) ^ S.card := by
    rw [Finset.prod_ite]
    simp
  rw [hsign]
  rfl

theorem mixedReflectedValue_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    mixedReflectedValue D s hp hc0 hg j S W X =
      (-1 : ℂ) ^ S.card * D.reflectedValue s hp hc0 hg (markedActiveExponent S j) W X := by
  unfold mixedReflectedValue ControlledStratumArithmetic.reflectedValue
  simp_rw [mixedActiveBracket_product]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  ring

theorem mixed_model_coefficient [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m I J)) =
    ((-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m) *
      ∑ e : ι → Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0
            (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
            (s.modelDualNumerator u) u) m I J *
        reflectedBranch (fun i => Ideal.span {p i}) hg (markedActiveExponent S j) e
          (primaryGenerator I) (primaryGenerator J) := by
  rw [mixedActiveBracket_product]
  calc
    _ = (-1 : ℂ) ^ S.card * (s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      D.bracketProduct hp hg (markedActiveExponent S j) (s.modelDualNumerator u m I J)) := by ring
    _ = _ :=
      (congrArg ((-1 : ℂ) ^ S.card * ·)
        (D.model_coefficient s hp hc0 hg (markedActiveExponent S j) u m I J)).trans
          (mul_assoc _ _ _).symm

theorem marked_modelRowPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖(-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m‖ = 1 := by
  have hj' : ∀ i, markedActiveExponent S j i < 6 := by
    intro i
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact D.modelRowPhase_norm hN hr hbase s hp hg hchar _ hj' u m

end
end SevenEighths.InverseMoment

end OAI
