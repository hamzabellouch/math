import OAI.NumberTheory.DirichletL.Descent.CuspCongruence
import OAI.NumberTheory.DirichletL.Descent.MarkedStratum

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance activeQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

variable {ι : Type*} [Fintype ι]

def localInactiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (A : Finset ι) : ℂ :=
  ∏ i ∈ (Finset.univ : Finset ι) \ A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) 0

def localActiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) : ℂ :=
  ∏ i : A, finiteAdditiveFourierCoeff (quotientTrace (p i.val) (hp i.val)) (F i.val) (v i)

theorem primeFunction_fourier_by_active
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (n : Eis) :
    (∏ i, F i (Ideal.Quotient.mk _ n)) =
      ∑ A : Finset ι, localInactiveWeight p hp F A *
        ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
          localActiveWeight p hp F A v *
            ∏ i : A, quotientTrace (p i.val) (hp i.val)
              ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) := by
  let (i : ι) : Field (Eis ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by
    ext A
    simp
  simpa only [hpow, localInactiveWeight, localActiveWeight] using
    FixedRayActiveSet.fourier_inversion_by_active_set (fun i => Eis ⧸ Ideal.span {p i})
      (fun i => quotientTrace (p i) (hp i))
      (fun i => GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) F
      (fun i => Ideal.Quotient.mk _ n)

theorem activeStratum_function_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    {N a0 c0 : Eis} {mode : Bool}
    (D : ∀ A : Finset ι, ControlledStratumArithmetic (fun i : A => p i.val) N a0 c0 mode)
    (hN : (9 : Eis) * c0 ∣ N) (hc0 : c0 ≠ 0)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n : Eis) :
    (∑ A : Finset ι, localInactiveWeight p hp F A *
      ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
        localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i, F i (Ideal.Quotient.mk _ n) := by
  have hlocal (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n *
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i : A, quotientTrace (p i.val) (hp i.val)
          ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i : A => p i.val) (fun i _ => hprimary i.val))
      hbase s (fun i => hp i.val) hc0 v n
  simp_rw [hlocal]
  rw [primeFunction_fourier_by_active p hp F n]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro v hv
  ring

def fixedActiveFunctionWeight
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (φ : Eis →* ℂ) (t : FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1 * localInactiveWeight p hp F t.2.1 *
    localActiveWeight p hp F t.2.1 t.2.2

theorem fixedActiveFunction_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (Q : Ideal Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (φ : Eis →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ) (n : Eis) :
    (∑ t : FixedActiveCuspIndex c p, fixedActiveFunctionWeight p hp F c hc φ t *
      ShortDraftTrace.breveE (-cuspFrequency n *
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
      fixedThetaTwist φ n * ∏ i, F i (Ideal.Quotient.mk _ n) := by
  simp only [FixedActiveCuspIndex, Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum]
  have hf : (∑ h : Eis ⧸ Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ShortDraftTrace.breveE (-cuspFrequency n * thetaFourierTranslation c h)) = fixedThetaTwist φ n := by
    simp only [fixedThetaRowCoeff]
    rw [thetaFourierTranslation_inversion c hc,
      fixedThetaQuotient_mk φ Q hφ c hcQ]
  rw [← hf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _ = fixedThetaRowCoeff c hc φ h *
        (∑ A : Finset ι, localInactiveWeight p hp F A *
          ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
            localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [activeStratum_function_multiplier p hp hprimary F (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n, (G h).point]
      ring

end
end SevenEighths.InverseMoment

end OAI
