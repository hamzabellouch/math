import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleExceptionalHigh

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

lemma largePrimeTupleHighSum_split (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) :
    largePrimeTupleHighSum i j ξ Ct H X = largePrimeTupleOrdinaryHighSum i j ξ δ Ct H X +
      largePrimeTupleExceptionalHighSum i j ξ δ Ct H X := by
  unfold largePrimeTupleHighSum largePrimeTupleOrdinaryHighSum largePrimeTupleExceptionalHighSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
  · by_cases ho : ∃ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
        ¬largePrimeTupleExceptional δ q <;> simp only [hh,ho,true_and,not_true_eq_false,not_false_eq_true,ite_true,ite_false,add_zero,zero_add]
  · simp only [hh,false_and,ite_false,zero_add]

theorem largePrimeTupleHighSum_isLittleO (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleHighSum i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have ho := largePrimeTupleOrdinaryHighSum_isLittleO i j hSW hpub hHuxley hperiod
    hMV hC hξ hξz hδ hGI hGQ hVor hGamma Ct H hH
  have he : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    by_cases hij : i+j = 3
    · exact largePrimeTupleExceptionalHighSum_isLittleO i j hij hpnt hSW hpub hHuxley
        hperiod hMV hC hξ hξz hδ1 hGI hGQ hVor hGamma Ct H hH
    · have hz : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =
          fun _ : ℝ => (0:ℂ) := by
        funext X
        exact largePrimeTupleExceptionalHighSum_zero i j hij ξ δ Ct (H X) X
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
  have hs : (fun X => largePrimeTupleHighSum i j ξ Ct (H X) X) =
      fun X => largePrimeTupleOrdinaryHighSum i j ξ δ Ct (H X) X +
        largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X := by
    funext X
    exact largePrimeTupleHighSum_split i j ξ δ Ct (H X) X
  rw [hs]
  exact ho.add he

lemma distinguishedPrimeTupleLow_eq_high_add_boundary (i j : ℕ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    distinguishedPrimeTupleLow i j 0 ξ Ct H X =
      largePrimeTupleHighSum i j ξ Ct H X + largePrimeTupleBoundarySum i j ξ Ct H X := by
  rw [distinguishedPrimeTupleLow_residual_partition i j ξ 0 Ct H hX,
    largePrimeTupleHighSum_split i j ξ 0 Ct H X]

theorem distinguishedPrimeTupleLow_sub_boundary_isLittleO (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => distinguishedPrimeTupleLow i j 0 ξ Ct (H X) X -
      largePrimeTupleBoundarySum i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have hh := largePrimeTupleHighSum_isLittleO i j hpnt hSW hpub hHuxley hperiod hMV hC
    hξ hξz (by norm_num : (0:ℝ) < 1/100) (by norm_num : (1/100:ℝ) ≤ 1/12)
    hGI hGQ hVor hGamma Ct H hH
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  rw [distinguishedPrimeTupleLow_eq_high_add_boundary i j ξ Ct (H X) hX]
  ring

end CubicFirstMoment

end

end OAI
