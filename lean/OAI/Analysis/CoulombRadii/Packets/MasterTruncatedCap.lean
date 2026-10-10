import Mathlib
import OAI.Analysis.CoulombRadii.Packets.RawMasterNewton
import OAI.Analysis.CoulombRadii.FormDomain.RetainedPotentialMean

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma rawPacketPotential_ge_far {n : ℕ} (g : 𝓢(Position,ℝ)) (hm : (∫ z,g z^2)=1)
    (hrad : ∀ z,g z=g (EuclideanSpace.single 0 ‖z‖)) (hgs : ∀ z,1 < ‖z‖ → g z=0)
    {c r₀ s R : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hR : 2*packetWidth c r₀ s y ≤ R) (x : Configuration n) :
    Coulomb.restrictedOutPotential (flattenConfiguration n x) {z | R ≤ ‖z-y‖} y ≤
      potentialOf (rawPacketDensity g c r₀ s x) y := by
  rw [rawPacketPotential_sum g hm hc hr₀ hs]
  apply Finset.sum_le_sum
  intro i hi
  change (if R ≤ ‖x i-y‖ then ‖x i-y‖⁻¹ else 0) ≤ _
  split_ifs with h
  · have hl := packetWidth_lipschitz hc.le hr₀ hs (x i) y
    have H := mul_le_mul_of_nonneg_right hscale (norm_nonneg (x i-y))
    have hsep : packetWidth c r₀ s (x i) ≤ ‖y-x i‖ := by
      rw [norm_sub_rev]
      have H' := (le_abs_self (packetWidth c r₀ s (x i)-packetWidth c r₀ s y)).trans hl
      linarith
    rw [packet_potential_newton_eq g hm hrad hgs hc hr₀ hs hsep]
    simp only [coulombKernel,norm_sub_rev]
    exact le_rfl
  · exact integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _)
      (packetKernel_nonneg g hc hr₀ hs (x i) z))

theorem master_field_le_truncated {n : ℕ} (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (g : 𝓢(Position,ℝ)) (hm : (∫ z,g z^2)=1)
    (hrad : ∀ z,g z=g (EuclideanSpace.single 0 ‖z‖)) (hgs : ∀ z,1 < ‖z‖ → g z=0)
    {c r₀ s R : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hR : 0 < R)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hwidth : 2*packetWidth c r₀ s y ≤ R) (V : ℝ) :
    V-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ≤
      V-Coulomb.restrictedCorePotential u {z | R ≤ ‖z-y‖} y := by
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  have := rawLaw_isProbability hu ((fromH1_mass u).trans hum)
  have hgc : HasCompactSupport (g : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hgs z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  let W := Coulomb.rawSignedField (n:=n) V {z | R ≤ ‖z-y‖} y
  have hA : MeasurableSet {z : Position | R ≤ ‖z-y‖} := measurableSet_le measurable_const (by fun_prop)
  have hW : Measurable W := Coulomb.rawSignedField_measurable _ hA y
  have hF := hW.comp (flattenConfiguration n).continuous.measurable
  have hB (x : Configuration n) : ‖W (flattenConfiguration n x)‖ ≤ |V|+(n:ℝ)/R := by
    exact Coulomb.rawSignedField_abs_le V _ y hR (fun _ hz => hz) _
  have hi : Integrable (fun x => W (flattenConfiguration n x)) (rawLaw (fromH1Wave u)) := Integrable.of_bound hF.aestronglyMeasurable (|V|+(n:ℝ)/R)
    (Eventually.of_forall hB)
  have hp := integrable_rawPacketPotential g.continuous hgc hm hc hr₀ hs (rawLaw (fromH1Wave u)) y
  have H := integral_mono (integrable_const V |>.sub hp) hi
    (fun x => sub_le_sub_left (rawPacketPotential_ge_far g hm hrad hgs hc hr₀ hs hscale y hwidth x) V)
  simp only [Pi.sub_apply] at H
  rw [integral_sub (integrable_const V) hp,integral_const,probReal_univ,smul_eq_mul,one_mul,
    ←mixturePacketPotential g.continuous hgc hm hc hr₀ hs] at H
  rw [fromH1_raw_bounded_integral u (F:=fun x => W (flattenConfiguration n x)) hF hB] at H
  simp only [ContinuousLinearEquiv.apply_symm_apply] at H
  rw [Coulomb.potentialForm_rawSignedField u V hA y hR (fun _ hz => hz),hum,mul_one] at H
  exact H

theorem atomic_master_field_cap {J n : ℕ} (S : Coulomb.Nuclei J)
    (hatom : ∀ i,S.position i=0) (u : Coulomb.H1Vector n)
    (hu : Coulomb.Antisymmetric u) (hum : Coulomb.mass u=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ Coulomb.unrestrictedFormBottom S)
    (he : Coulomb.form S u ≤ E+δ) (hδ : 0 ≤ δ)
    (g : 𝓢(Position,ℝ)) (hm : (∫ z,g z^2)=1)
    (hrad : ∀ z,g z=g (EuclideanSpace.single 0 ‖z‖)) (hgs : ∀ z,1 < ‖z‖ → g z=0)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hy : y≠0) (hwidth : 2*packetWidth c r₀ s y ≤ 40*Coulomb.atomicCellScale y) :
    Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ≤
      2*Coulomb.atomicBudgetRecursionC^2*
        Coulomb.screenFieldUnit δ Coulomb.atomicCountConstant (Coulomb.atomicCellScale y) := by
  have ha := Coulomb.atomicCellScale_pos hy
  exact (master_field_le_truncated u hum g hm hrad hgs hc hr₀ hs (by positivity)
    hscale y hwidth (Coulomb.attraction S y)).trans
    ((le_max_left _ _).trans (Coulomb.atomic_expected_raw_field_bound S hatom u hu hum hE he hδ hy))
end NeutralAtom
end

end

end OAI
