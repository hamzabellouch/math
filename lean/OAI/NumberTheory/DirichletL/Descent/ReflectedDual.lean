import OAI.NumberTheory.DirichletL.Descent.ControlledMultiplier

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota CompletedDyadic
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance dualQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def mixedSmoothedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
    fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

def mixedReflectedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) *
    ∑' t : ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1 *
          Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ)) *
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X / (27 * (sourceCuspScale s.index) ^ 2 * (Ideal.absNorm (Ideal.span {c0 * ∏ i, p i}) : ℝ) ^ 2)) *
          (ramifiedScale 1 completedRamifiedStep t.2.1) ^ 3 *
          (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) ^ 3) *
      ((star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))) *
        ∏ i, mixedActiveBracket hp hg j S D i
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem mixed_smoothed_eq_reflected (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X =
      mixedReflectedValue D s hp hc0 hg j S W X := by
  have hden : c0 * (∏ i, p i) ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hmat (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      (D.sourceGamma hN hr hbase v : SL(2, Eis)) *
        ControlledStratumArithmetic.fixedCusp a0 c0 mode = D.matrix v :=
    D.sourceGamma_mul hN hr hbase v
  have hchar (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      levelTwoComplexCharacter (D.sourceGamma hN hr hbase v) =
        complexCharacter (D.relativeGamma hN hr hbase v) :=
    D.sourceGamma_character hN hr hbase v
  have hC : ∀ v, ((D.sourceGamma hN hr hbase v : SL(2, Eis)) *
      ControlledStratumArithmetic.fixedCusp a0 c0 mode) 1 0 = c0 * ∏ i, p i := by
    intro v
    exact (congrArg (fun M : SL(2, Eis) => M 1 0) (hmat v)).trans (D.denominator v)
  have he := s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hden hC
    (fullLocalFourierWeight hp (mixedPrimeFunction p hg j S)) W lo hi hlo hsupp hW X hX
  change mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X = _ at he
  rw [he]
  unfold mixedReflectedValue
  apply congrArg (fun z : ℂ => fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) * z)
  apply tsum_congr
  intro t
  congr 1
  simpa only [hchar, hmat, map_mul] using
    controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end
end SevenEighths.InverseMoment

end OAI
