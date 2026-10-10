import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitLocal
import PrimeNumberTheoremAnd.Erdos970.Auxiliary
import PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set Filter
open scoped Topology BigOperators

def zerosInRectangle {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (finite_zeros_on_compact χ hχ
    (show IsCompact (Rectangle z w) from IsCompact.reProdIm isCompact_uIcc isCompact_uIcc)).toFinset

@[simp] theorem mem_zerosInRectangle {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z w p : ℂ) :
    p ∈ zerosInRectangle χ hχ z w ↔ p ∈ Rectangle z w ∧ χ.LFunction p = 0 := by
  simp [zerosInRectangle]

theorem rectangle_integral_neg_LFunction_logDeriv_mul {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) {K : ℂ → ℂ}
    (hK : AnalyticOnNhd ℂ K (Rectangle z w))
    (hboundary : ∀ p ∈ Erdos970.RectangleBorder z w, χ.LFunction p ≠ 0) :
    Erdos970.RectangleIntegral' (fun s => -logDeriv χ.LFunction s * K s) z w =
      -∑ p ∈ zerosInRectangle χ hχ z w, (zeroMultiplicity χ p : ℂ)*K p := by
  classical
  let F : ℂ → ℂ := fun s => -logDeriv χ.LFunction s*K s
  let R := Rectangle z w
  have hmero : MeromorphicOn F R := fun p hp =>
    ((analyticAt_LFunction χ hχ p).meromorphicAt.logDeriv.neg).mul (hK p hp).meromorphicAt
  have hanalytic (p : ℂ) (hp : p ∈ R) (hn : χ.LFunction p ≠ 0) : AnalyticAt ℂ F p :=
    (((analyticAt_LFunction χ hχ p).deriv.div (analyticAt_LFunction χ hχ p) hn).neg).mul (hK p hp)
  have hpolezero (p : ℂ) (hp : p ∈ R) (hn : meromorphicOrderAt F p < 0) :
      χ.LFunction p = 0 := by
    by_contra hz
    exact (not_lt_of_ge (hanalytic p hp hz).meromorphicOrderAt_nonneg) hn
  have hpoles : (R ∩ {p | meromorphicOrderAt F p < 0}).Finite := by
    apply (finite_zeros_on_compact χ hχ
      (show IsCompact R from IsCompact.reProdIm isCompact_uIcc isCompact_uIcc)).subset
    intro p hp
    exact ⟨hp.1, hpolezero p hp.1 hp.2⟩
  have hborder : Disjoint (Erdos970.RectangleBorder z w) {p | meromorphicOrderAt F p < 0} := by
    apply Set.disjoint_left.mpr
    intro p hp hn
    exact hboundary p hp (hpolezero p (rectangleBorder_subset_rectangle z w hp) hn)
  have hsimple : HasSimplePolesOn F R := fun p hp =>
    weighted_logDeriv_has_at_most_simple_pole (analyticAt_LFunction χ hχ p)
      (analyticOrderAt_LFunction_ne_top χ hχ p) (hK p hp)
  have hres := RectangleIntegral'_eq_sumResiduesIn hre him hmero hborder hpoles hsimple
  change Erdos970.RectangleIntegral' F z w = _
  rw [hres]
  have hsum : sumResiduesIn F (R ∩ {p | meromorphicOrderAt F p < 0}) =
      ∑ p ∈ hpoles.toFinset, Erdos970.residue F p := by
    conv_lhs => rw [sumResiduesIn, ← hpoles.coe_toFinset]
    rw [tsum_fintype (f := fun p : (hpoles.toFinset : Set ℂ) => Erdos970.residue F p)]
    exact Finset.sum_coe_sort hpoles.toFinset (fun p => Erdos970.residue F p)
  rw [hsum]
  have hsub : hpoles.toFinset ⊆ zerosInRectangle χ hχ z w := by
    intro p hp
    have hp' := hpoles.mem_toFinset.mp hp
    exact (mem_zerosInRectangle χ hχ z w p).mpr ⟨hp'.1, hpolezero p hp'.1 hp'.2⟩
  calc
    _ = ∑ p ∈ zerosInRectangle χ hχ z w, Erdos970.residue F p := by
      apply Finset.sum_subset hsub
      intro p hp hnp
      have hpR := ((mem_zerosInRectangle χ hχ z w p).mp hp).1
      apply residue_eq_zero_of_not_pole_of_meromorphicAt (hmero p hpR)
      exact le_of_not_gt fun hn => hnp (hpoles.mem_toFinset.mpr ⟨hpR, hn⟩)
    _ = -∑ p ∈ zerosInRectangle χ hχ z w, (zeroMultiplicity χ p : ℂ)*K p := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hpR := ((mem_zerosInRectangle χ hχ z w p).mp hp).1
      simpa only [F, logDeriv_apply, neg_mul] using
        residue_neg_LFunction_logDeriv_mul χ hχ (hK p hpR).continuousAt

end Ostmann.Dirichlet

end

end OAI
