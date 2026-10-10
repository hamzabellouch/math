import OAI.Geometry.IsometricImmersion.Energy.DirectedCutoffBalance

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedGradientEnergy (chi I u : Coord → ℝ) (edge lambda : ℝ) (p : Coord) : ℝ :=
  chi p * directedWeight edge lambda I p * ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2)

def directedForcingEnergy (chi I f : Coord → ℝ) (edge lambda : ℝ) (p : Coord) : ℝ :=
  chi p * directedWeight edge lambda I p * (f p)^2

def directedCutoffError (A chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) : Coord → ℝ :=
  multiplierCutoffError A chi (directedM edge lambda I) (directedN edge lambda epsilon I) u

def directedCoercivityDefect (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord) : ℝ :=
  chi p * max 0 (c * directedWeight edge lambda I p *
    ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) -
      multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p)

theorem directedCoercivityDefect_zero
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord)
    (hcoercive : c * directedWeight edge lambda I p *
      ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) ≤
        multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p) :
    directedCoercivityDefect A B C chi I u edge lambda epsilon c p = 0 := by
  simp only [directedCoercivityDefect, max_eq_left (sub_nonpos.mpr hcoercive), mul_zero]

theorem directedCoercivityDefect_domination
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord) (hchi : 0 ≤ chi p) :
    c * directedGradientEnergy chi I u edge lambda p ≤
      chi p * multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p +
        directedCoercivityDefect A B C chi I u edge lambda epsilon c p := by
  have hh := mul_le_mul_of_nonneg_left
    (le_max_right (0 : ℝ) (c * directedWeight edge lambda I p *
      ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) -
        multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p)) hchi
  dsimp [directedGradientEnergy, directedCoercivityDefect]
  nlinarith only [hh]

theorem integrated_directed_energy_with_explicit_costs
    {A B C chi I u f : Coord → ℝ} {U : Set Coord} {tl tr sb st : ℝ}
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U)
    (hchi : ContDiffOn ℝ ∞ chi U) (hI : ContDiffOn ℝ ∞ I U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hchiSides : ∀ s ∈ Icc sb st, chi (boxPoint tl s) = 0 ∧ chi (boxPoint tr s) = 0)
    (hchiBottom : ∀ t ∈ Icc tl tr, chi (boxPoint t sb) = 0)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (hchin : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ chi p)
    (lambda epsilon R c : ℝ) (hc : 0 < c) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hR : ∀ p ∈ closedRectangle tl tr sb st, |p 0| ≤ R) :
    (c / 2) * rectangleIntegral tl tr sb st (directedGradientEnergy chi I u st lambda) ≤
      ((1 + R^2) / (2 * c)) * rectangleIntegral tl tr sb st (directedForcingEnergy chi I f st lambda) +
      rectangleIntegral tl tr sb st (fun p => |directedCutoffError A chi I u st lambda epsilon p|) +
      rectangleIntegral tl tr sb st (directedCoercivityDefect A B C chi I u st lambda epsilon c) := by
  let m := directedM st lambda I
  let n := directedN st lambda epsilon I
  let Q := multiplierQuadratic A B C m n u
  let E := directedGradientEnergy chi I u st lambda
  let F := directedForcingEnergy chi I f st lambda
  let Err := directedCutoffError A chi I u st lambda epsilon
  let Def := directedCoercivityDefect A B C chi I u st lambda epsilon c
  let Source := fun p => f p * multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p
  have hW := directedWeight_contDiffOn st lambda hI
  have hm : ContDiffOn ℝ ∞ m U := hW.neg
  have hn : ContDiffOn ℝ ∞ n U :=
    (contDiffOn_const.mul (contDiffOn_apply ℝ ℝ 0 U)).mul hW
  have hcm := hchi.mul hm
  have hcn := hchi.mul hn
  have hut := partial_contDiffOn hu hU 0
  have hus := partial_contDiffOn hu hU 1
  have hgrad := (hut.pow 2).add (hus.pow 2)
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  have hEc : ContinuousOn E (closedRectangle tl tr sb st) :=
    (((hchi.mul hW).mul hgrad).continuousOn.mono hbox)
  have hFc : ContinuousOn F (closedRectangle tl tr sb st) :=
    (((hchi.mul hW).mul (hf.pow 2)).continuousOn.mono hbox)
  have hQ := multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu
  have hchiQ : ContinuousOn (fun p => chi p * Q p) (closedRectangle tl tr sb st) :=
    (hchi.mul hQ).continuousOn.mono hbox
  have hErr := multiplierCutoffError_contDiffOn hU hA hchi hm hn hu
  have hErrc : ContinuousOn Err (closedRectangle tl tr sb st) := hErr.continuousOn.mono hbox
  have hDef : ContinuousOn Def (closedRectangle tl tr sb st) :=
    (hchi.continuousOn.mul ((continuousOn_const (c := (0 : ℝ))).sup
      ((((contDiffOn_const (c := c)).mul hW).mul hgrad).sub hQ).continuousOn)).mono hbox
  have htest : ContDiffOn ℝ ∞ (multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) U :=
    (hcm.mul hus).add (hcn.mul hut)
  have hSource : ContinuousOn Source (closedRectangle tl tr sb st) := (hf.mul htest).continuousOn.mono hbox
  have hsplit : rectangleIntegral tl tr sb st Source =
      rectangleIntegral tl tr sb st (fun p => chi p * Q p) - rectangleIntegral tl tr sb st Err := by
    calc
      _ = rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p *
          multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        change f p * multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p =
          multiplierOperator A B C u p *
            multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p
        rw [hEq p (hbox hp)]
      _ = rectangleIntegral tl tr sb st
          (multiplierQuadratic A B C (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) :=
        integrated_cutoff_directed_identity ht hs hU hA hB hC hchi hI hu hbox hchiSides hchiBottom lambda epsilon
      _ = rectangleIntegral tl tr sb st (fun p => chi p * Q p - Err p) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        exact multiplierQuadratic_cutoff_split hU hA hchi hm hn hu (hbox hp)
      _ = _ := rectangleIntegral_sub ht hs hchiQ hErrc
  have hdom := rectangleIntegral_mono ht hs (continuousOn_const.mul hEc) (hchiQ.add hDef)
    (fun p hp => directedCoercivityDefect_domination A B C chi I u st lambda epsilon c p (hchin p hp))
  change rectangleIntegral tl tr sb st (fun p => c * E p) ≤
    rectangleIntegral tl tr sb st (fun p => chi p * Q p + Def p) at hdom
  rw [rectangleIntegral_const_mul, rectangleIntegral_add ht hs hchiQ hDef] at hdom
  have hsourceBound (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      Source p ≤ (c / 2) * E p + ((1 + R^2) / (2 * c)) * F p := by
    have hWn : 0 ≤ directedWeight st lambda I p :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr hp.2.2) 8) (Real.exp_pos _).le
    have hpoint := directed_source_young_scalar (mul_nonneg (hchin p hp) hWn) hc heps heps1 (hR p hp)
      (f := f p) (ut := coordPartial 0 u p) (us := coordPartial 1 u p)
    have hfac := cutoff_test_factor chi I u st lambda epsilon p
    dsimp [Source]
    rw [hfac]
    exact (le_abs_self _).trans (by
      convert hpoint using 1
      dsimp [E, F, directedGradientEnergy, directedForcingEnergy]
      ring)
  have hsourceIntegral := rectangleIntegral_mono ht hs hSource
    ((continuousOn_const.mul hEc).add (continuousOn_const.mul hFc)) hsourceBound
  change rectangleIntegral tl tr sb st Source ≤ rectangleIntegral tl tr sb st
    (fun p => (c / 2) * E p + ((1 + R^2) / (2 * c)) * F p) at hsourceIntegral
  have hcE : ContinuousOn (fun p => (c / 2) * E p) (closedRectangle tl tr sb st) :=
    continuousOn_const.mul hEc
  have hcF : ContinuousOn (fun p => ((1 + R^2) / (2 * c)) * F p) (closedRectangle tl tr sb st) :=
    continuousOn_const.mul hFc
  rw [rectangleIntegral_add ht hs hcE hcF,
    rectangleIntegral_const_mul, rectangleIntegral_const_mul] at hsourceIntegral
  have herrorIntegral := rectangleIntegral_mono ht hs hErrc hErrc.abs (fun p hp => le_abs_self (Err p))
  change (c / 2) * rectangleIntegral tl tr sb st E ≤
    ((1 + R^2) / (2 * c)) * rectangleIntegral tl tr sb st F +
    rectangleIntegral tl tr sb st (fun p => |Err p|) + rectangleIntegral tl tr sb st Def
  nlinarith only [hdom, hsplit, hsourceIntegral, herrorIntegral]

end SmoothLocal.Weighted

end

end OAI
