import OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy
import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondMultiplier {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor

omit [DecidableEq ι] in
theorem actualSecondMultiplier_ne_zero {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    actualSecondMultiplier p x ≠ 0 := by
  apply mul_ne_zero
  · exact primeSubsetGenerator_ne_zero _ _
  · exact primeSubsetGenerator_ne_zero _ _

include hp in

theorem actual_second_row_norm_sq
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    ‖eisEmbedding (actualSecondChild p u v x).2.2‖^2 =
      ‖eisEmbedding (actualSecondMultiplier p x*x.second.frequency)‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.firstDivisor)*
      primaryGenerator (sourceIdeal p x.second.divisor)*secondUnitFrequency u v x.second.frequency)‖^2 = _
  rw [sourceIdeal_gen p hp hpr,sourceIdeal_gen p hp hpr]
  simp only [map_mul,norm_mul,mul_pow,secondUnitFrequency_norm,actualSecondMultiplier,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in

theorem actual_second_row_ball
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) (R : ℝ) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R ↔
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x),
    mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,actual_second_row_norm_sq p hp hpr]

omit [DecidableEq ι] in
theorem actual_second_row_radius_one
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (R : ℝ)
    (hsource : source.Nonempty)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) : 1 ≤ R := by
  obtain ⟨x,hx⟩ := hsource
  by_contra hR
  have he := nonzeroChildFrequencyBall_empty _ (actualSecondMultiplier_ne_zero p x) R (lt_of_not_ge hR)
  simpa [he] using hrows x hx

end
end SevenEighths.InverseMoment

end OAI
