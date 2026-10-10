import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllCoreLit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeEdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ActiveReachable
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ForestCuts

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ForestTraversal Finset Classical Filter
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace NumericalLine

lemma component_bound_after_gap (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (hL : 0<L)
    (hc : AllCoreLit w.line a) (hu : repeatedCenterUnlitCount w.line a<t)
    (hpack : ¬Nonempty (GapFamily w a L t))
    (p : S.FixedIndex w.line) (hph : ¬(p.val:ℕ) ∣ h) :
    (activeComponents w.line hh p.val (a p)).card ≤ (2*ℓ)/L+6*t+1 := by
  obtain ⟨H,hH,hcard,huncut,hcut⟩ := w.forest_cuts hh a hc hu hpack
  obtain ⟨bs,hbs,hbl,hcover⟩ := tree_blocks w.line hh H L hL
  have hb := components_le_blocks w hh a H hcut bs hbl hcover p hph
  exact hb.trans (hbs.trans (by omega))

lemma source_component_budget : ∀ᶠ B : ℝ in atTop,0<pathLength B ∧
    ((((2*sourceLength B)/pathLength B+6*listCutoff B+1):ℕ):ℝ) ≤ 32*B^rho := by
  have hp : ∀ᶠ B : ℝ in atTop,2 ≤ B^(1-rho) :=
    (tendsto_rpow_atTop (by norm_num [rho] : (0:ℝ)<1-rho)).eventually (eventually_ge_atTop 2)
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with B hp hB
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hpow : B^rho*B^(1-rho)=B := by
    rw [←Real.rpow_add hB0]; ring_nf; exact Real.rpow_one B
  have hfloor : B^(1-rho)/2 ≤ (pathLength B:ℝ) := by
    have hf := Nat.lt_floor_add_one (B^(1-rho))
    change B^(1-rho)<(pathLength B:ℝ)+1 at hf
    linarith
  have hL0 : (0:ℝ)<(pathLength B:ℝ) := lt_of_lt_of_le (by linarith) hfloor
  have hL : 0<pathLength B := Nat.cast_pos.mp hL0
  have hnum : ((2*sourceLength B:ℕ):ℝ) ≤ 4*B := by
    have hs := sourceLength_le B hB0.le
    push_cast
    linarith
  have hr0 : 0 ≤ B^rho := Real.rpow_nonneg hB0.le _
  have hq : (((2*sourceLength B)/pathLength B:ℕ):ℝ) ≤ 8*B^rho := by
    apply (Nat.cast_div_le (α:=ℝ)).trans
    apply (div_le_iff₀ hL0).mpr
    calc
      ((2*sourceLength B:ℕ):ℝ) ≤ 4*B := hnum
      _ = (8*B^rho)*(B^(1-rho)/2) := by nlinarith [hpow]
      _ ≤ (8*B^rho)*(pathLength B:ℝ) := mul_le_mul_of_nonneg_left hfloor (by positivity)
  have ht : (listCutoff B:ℝ) ≤ 2*B^rho := by
    exact (ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB (by norm_num [rho,epsilon])) (by norm_num))
  have hr1 : 1 ≤ B^rho := Real.one_le_rpow hB (by norm_num [rho])
  refine ⟨hL,?_⟩
  push_cast
  nlinarith

theorem source_components_after_gap (h : ℕ) (hh : 0<h) (τ C₀ : ℝ) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (w : NumericalLine D h (sourceLength B)) (a : (sourceSystem B).FixedResidues w.line),
      AllCoreLit w.line a → repeatedCenterUnlitCount w.line a<listCutoff B →
      ¬Nonempty (GapFamily w a (pathLength B) (listCutoff B)) →
      ∀ p : (sourceSystem B).FixedIndex w.line,
        ((activeComponents w.line hh p.val (a p)).card:ℝ) ≤ 32*B^rho := by
  filter_upwards [source_component_budget,source_eventually_large h] with B hbudget hlarge
  intro D w a hc hu hgap p
  have hph : ¬(p.val:ℕ) ∣ h := Nat.not_dvd_of_pos_of_lt hh (hlarge.2 p.val).2
  exact (Nat.cast_le.mpr (w.component_bound_after_gap hh a hbudget.1 hc hu hgap p hph)).trans hbudget.2

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
