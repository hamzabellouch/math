import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleOrdinarySum
import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleExceptionalHigh

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_largePrimeTupleHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

lemma angular_largePrimeTupleHighSum_split (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) :
    angular_largePrimeTupleHighSum ℓ i j ξ Ct H X = angular_largePrimeTupleOrdinaryHighSum ℓ i j ξ δ Ct H X +
      angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct H X := by
  unfold angular_largePrimeTupleHighSum angular_largePrimeTupleOrdinaryHighSum angular_largePrimeTupleExceptionalHighSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
  · by_cases ho : ∃ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
        ¬largePrimeTupleExceptional δ q <;> simp only [hh,ho,true_and,not_true_eq_false,not_false_eq_true,ite_true,ite_false,add_zero,zero_add]
  · simp only [hh,false_and,ite_false,zero_add]

theorem angular_largePrimeTupleHighSum_isLittleO (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_largePrimeTupleHighSum ℓ i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have ho := angular_largePrimeTupleOrdinaryHighSum_isLittleO ℓ i j hSW hℓ hpub hHuxley hperiod
    hMV hC hξ hξz hδ hGI hGQ hVor hGamma Ct H hH
  have he : (fun X => angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    by_cases hij : i+j = 3
    · exact angular_largePrimeTupleExceptionalHighSum_isLittleO ℓ i j hij hpnt hSW hℓ hpub hHuxley
        hperiod hMV hC hξ hξz hδ1 hGI hGQ hVor hGamma Ct H hH
    · have hz : (fun X => angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X) =
          fun _ : ℝ => (0:ℂ) := by
        funext X
        exact angular_largePrimeTupleExceptionalHighSum_zero ℓ i j hij ξ δ Ct (H X) X
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
  have hs : (fun X => angular_largePrimeTupleHighSum ℓ i j ξ Ct (H X) X) =
      fun X => angular_largePrimeTupleOrdinaryHighSum ℓ i j ξ δ Ct (H X) X +
        angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X := by
    funext X
    exact angular_largePrimeTupleHighSum_split ℓ i j ξ δ Ct (H X) X
  rw [hs]
  exact ho.add he

end CubicFirstMoment

end

end OAI
