import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialDefect
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

/-! # The Riccati identity of the actual outgoing columns

No inverse derivative formula is assumed. Differentiate `A Φ = Φ'`,
then use invertibility of the two value columns to obtain the Riccati
equation from their original second-order ODE.
-/

open Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousTwoColumns_hasDerivAt (u v : ℝ → V) (u' v' : V) (r : ℝ)
    (hu : HasDerivAt u u' r) (hv : HasDerivAt v v' r) :
    HasDerivAt (fun t => spectralTwoColumns (u t) (v t))
      (spectralTwoColumns u' v') r := by
  have hp := ((ContinuousLinearMap.smulRightL ℂ V V
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hu
  have hm := ((ContinuousLinearMap.smulRightL ℂ V V
    (ContinuousLinearMap.snd ℂ ℂ ℂ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hv
  exact hp.add hm

theorem homogeneousValueInverse_differentiableAt (u v : ℝ → V) (u' v' : V) (r : ℝ)
    (hu : HasDerivAt u u' r) (hv : HasDerivAt v v' r)
    (hd : spectralValueDet (u r) (v r) ≠ 0) :
    DifferentiableAt ℝ (fun t => spectralValueInverse (u t) (v t)) r := by
  have hdet : HasDerivAt (fun t => spectralValueDet (u t) (v t))
      (u'.1 * (v r).2 + (u r).1 * v'.2 -
        (u'.2 * (v r).1 + (u r).2 * v'.1)) r := by
    exact ((homogeneousPair_fst_hasDerivAt hu).mul (homogeneousPair_snd_hasDerivAt hv)).sub
      ((homogeneousPair_snd_hasDerivAt hu).mul (homogeneousPair_fst_hasDerivAt hv))
  have hadj := homogeneousTwoColumns_hasDerivAt
    (fun t => ((v t).2, -(u t).2)) (fun t => (-(v t).1, (u t).1))
    (v'.2, -u'.2) (-v'.1, u'.1) r
    ((homogeneousPair_snd_hasDerivAt hv).prodMk (homogeneousPair_snd_hasDerivAt hu).neg)
    ((homogeneousPair_fst_hasDerivAt hv).neg.prodMk (homogeneousPair_fst_hasDerivAt hu))
  exact ((hdet.inv hd).smul hadj).differentiableAt

theorem homogeneousTwoColumns_surjective (u v : V)
    (hd : spectralValueDet u v ≠ 0) : Function.Surjective (spectralTwoColumns u v) := by
  apply LinearMap.surjective_of_injective (f := (spectralTwoColumns u v).toLinearMap)
  exact (show Function.LeftInverse (spectralValueInverse u v) (spectralTwoColumns u v) from
    fun z => spectralValueInverse_apply_columns u v z hd).injective

theorem homogeneousRadialRiccati_from_columns
    (B C : End) (u v du dv : ℝ → V) (r : ℝ)
    (hu : HasDerivAt u (du r) r) (hv : HasDerivAt v (dv r) r)
    (hdu : HasDerivAt du (-B (du r) - C (u r)) r)
    (hdv : HasDerivAt dv (-B (dv r) - C (v r)) r)
    (hd : spectralValueDet (u r) (v r) ≠ 0) :
    let A := fun t => spectralRobinOperator (u t) (v t) (du t) (dv t)
    HasDerivAt A (-B * A r - C - A r * A r) r := by
  intro A
  let F := fun t => spectralTwoColumns (u t) (v t)
  let D := fun t => spectralTwoColumns (du t) (dv t)
  have hF : HasDerivAt F (D r) r := homogeneousTwoColumns_hasDerivAt u v _ _ r hu hv
  have hD : HasDerivAt D (-B * D r - C * F r) r := by
    apply (homogeneousTwoColumns_hasDerivAt du dv _ _ r hdu hdv).congr_deriv
    apply ContinuousLinearMap.ext
    intro z
    simp only [D, F, spectralTwoColumns_apply, sub_apply, neg_apply, mul_apply_eq_comp,
      map_add, map_smul, smul_sub, smul_neg]
    abel
  have hA : DifferentiableAt ℝ A r := by
    have hi := homogeneousValueInverse_differentiableAt u v _ _ r hu hv hd
    change DifferentiableAt ℝ (fun t => D t * spectralValueInverse (u t) (v t)) r
    exact hD.differentiableAt.mul hi
  have hdetc : ContinuousAt (fun t => spectralValueDet (u t) (v t)) r :=
    (hu.continuousAt.fst.mul hv.continuousAt.snd).sub
      (hu.continuousAt.snd.mul hv.continuousAt.fst)
  have hAD : (fun t => A t * F t) =ᶠ[𝓝 r] D := by
    filter_upwards [hdetc.eventually (eventually_ne_nhds hd)] with t ht
    apply ContinuousLinearMap.ext
    intro z
    exact spectralRobinOperator_columns (u t) (v t) (du t) (dv t) z ht
  have hder : deriv A r * F r + A r * D r = -B * D r - C * F r :=
    (hA.hasDerivAt.mul hF).unique (hD.congr_of_eventuallyEq hAD)
  have hArF : A r * F r = D r := hAD.self_of_nhds
  have hR : deriv A r = -B * A r - C - A r * A r := by
    apply ContinuousLinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := homogeneousTwoColumns_surjective (u r) (v r) hd x
    have hz := congrArg (fun L : End => L z) hder
    have hzD := congrArg (fun L : End => L z) hArF
    simp only [mul_apply_eq_comp] at hzD
    change A r (F r z) = D r z at hzD
    simp only [add_apply, sub_apply, neg_apply, mul_apply_eq_comp] at hz ⊢
    change deriv A r (F r z) + A r (D r z) = -B (D r z) - C (F r z) at hz
    rw [← hzD] at hz
    exact (eq_sub_iff_add_eq).mpr hz
  exact hA.hasDerivAt.congr_deriv hR

theorem homogeneousRadialDefect_from_columns
    (B C : End) (u v du dv U V' : ℝ → V) (r : ℝ)
    (hu : HasDerivAt u (du r) r) (hv : HasDerivAt v (dv r) r)
    (hdu : HasDerivAt du (-B (du r) - C (u r)) r)
    (hdv : HasDerivAt dv (-B (dv r) - C (v r)) r)
    (hd : spectralValueDet (u r) (v r) ≠ 0)
    (hU : HasDerivAt U (V' r) r) (hV : HasDerivAt V' (-B (V' r) - C (U r)) r) :
    let A := fun t => spectralRobinOperator (u t) (v t) (du t) (dv t)
    HasDerivAt (homogeneousRadialDefect A U V')
      (-(B + A r) (homogeneousRadialDefect A U V' r)) r := by
  intro A
  exact homogeneousRadialDefect_hasDerivAt B C A U V' r hU hV
    (homogeneousRadialRiccati_from_columns B C u v du dv r hu hv hdu hdv hd)

end DefocusingNLS

end OAI
