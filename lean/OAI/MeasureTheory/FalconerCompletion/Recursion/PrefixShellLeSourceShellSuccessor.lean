import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Recursion.PrefixDescriptors
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixShell
import OAI.MeasureTheory.FalconerCompletion.Shells.WeightedMaskTransform

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma prefixShell_le_sourceShell_successor [IsFiniteMeasure e.weightedDistance] (j : ℕ) :
    e.prefixShell j ≤ (2:ℝ)^(-(e.a:ℝ))*
      (∫ r in Icc ((2:ℝ)^(j+1:ℕ)/2) (2*(2:ℝ)^(j+1:ℕ)),
        ‖Attempt4PrefixShell.weightedMaskTransformND e.prefixDescriptors e.prefixDescriptors
          e.prefixEndpointSmooth e.prefixEndpointSmooth (fun _ => 1) (fun _ => 1)
          e.ρ e.ρ (treeCell e.X) (treeCell e.Y) e.levelMass e.levelMass e.a r‖^2) := by
  simp_rw [e.prefix_shell_transform_exact]
  have hsub : Icc ((2:ℝ)^j) ((2:ℝ)^(j+1))⊆Icc ((2:ℝ)^(j+1)/2) (2*(2:ℝ)^(j+1)) := by
    intro r hr
    constructor
    · simpa only [pow_succ,mul_div_cancel_right₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hr.1
    · have hp : 0 ≤ (2:ℝ)^(j+1) := by positivity
      linarith [hr.2]
  have hi : Integrable (fun r => ‖charFun e.weightedDistance r‖^2)
      (volume.restrict (Icc ((2:ℝ)^(j+1)/2) (2*(2:ℝ)^(j+1)))) := by
    simpa only [one_mul] using charFun_sq_integrable_finite e.weightedDistance
      (volume.restrict (Icc ((2:ℝ)^(j+1)/2) (2*(2:ℝ)^(j+1)))) 1
  exact mul_le_mul_of_nonneg_left
    (integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun e.weightedDistance r‖)) hi) (by positivity)

lemma prefixHigh_shell_regime {sig : ℝ} (hsig : 0 < sig)
    (htN : e.t ≤ e.N) (hwidth : e.a+100*e.q < e.t) (hq : sig*e.N ≤ e.q)
    {v : ℕ} (hv : v+1 ≤ e.t) (hhigh : (e.t:ℝ)-(v+1:ℕ) < sig*e.N) :
    20*sig*e.N ≤ (v+1:ℕ)-(e.a:ℝ) ∧
    (((e.t-e.a)/2:ℕ):ℝ) ≤ ((v+1:ℕ)-(e.a:ℝ))/2+sig*e.N ∧
    (v+1:ℕ)-(e.a:ℝ) ≤ 2*e.N := by
  have hat : e.a ≤ e.t := by omega
  have hw : (e.a:ℝ)+100*e.q < e.t := by exact_mod_cast hwidth
  have hv' : ((v+1:ℕ):ℝ) ≤ e.N := by exact_mod_cast hv.trans htN
  have hfloor : 2*(((e.t-e.a)/2:ℕ):ℝ) ≤ (e.t:ℝ)-e.a := by
    have hh := Nat.mul_div_le (e.t-e.a) 2
    have hhc : (2:ℝ)*(((e.t-e.a)/2:ℕ):ℝ) ≤ ((e.t-e.a:ℕ):ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub hat] using hhc
  have hna : 0 ≤ (e.a:ℝ) := Nat.cast_nonneg _
  have hnN : 0 ≤ (e.N:ℝ) := Nat.cast_nonneg _
  have hsigN : 0 ≤ sig*e.N := mul_nonneg hsig.le hnN
  constructor
  · linarith
  constructor <;> linarith

lemma prefixShell_normalized_mass {B : ℕ} {s sig : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B s sig e.mass)
    (ha : e.a ≤ e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a) :
    |(e.levelMass*e.levelMass)⁻¹| *
      ((e.ρ.restrict (treeCell e.X)).prod (e.ρ.restrict (treeCell e.Y))).real univ ≤
        ((2:ℝ)^e.N)^(2*(n+2:ℝ)*sig) := by
  have h := e.normalized_cellPair_profile_mass hd ha hX hY
  have hm : |(e.levelMass*e.levelMass)⁻¹| = e.levelMass^(-2:ℤ) := by
    rw [abs_of_nonneg (inv_nonneg.mpr (mul_self_nonneg e.levelMass))]
    simp [zpow_neg,pow_two]
  rw [hm]
  convert h using 1 <;> push_cast <;> congr 1
  ring

lemma prefixDescriptors_card_max (hN : 1 ≤ e.N) (hq : 0 < e.q) :
    max 1 ((e.prefixDescriptors.card+e.prefixDescriptors.card:ℕ):ℝ) ≤ 16*(e.N:ℝ)^3 := by
  have hN' : (1:ℝ) ≤ e.N := by exact_mod_cast hN
  exact max_le (by nlinarith [one_le_pow₀ hN' (n:=3)]) (e.prefixDescriptors_card hN hq)

end PositiveDistanceState
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
