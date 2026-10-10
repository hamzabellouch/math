import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketDensity

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
namespace Coulomb

def densityCut (ρ : Space → ℝ) (k : ℕ) (x : Space) : ℝ := min (ρ x) (k:ℝ)
lemma densityCut_nonneg (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (k : ℕ) (x : Space) :
    0 ≤ densityCut ρ k x := le_min (hp x) (Nat.cast_nonneg k)
lemma densityCut_le (ρ : Space → ℝ) (k : ℕ) (x : Space) : densityCut ρ k x ≤ ρ x := min_le_left _ _
lemma densityCut_bound (ρ : Space → ℝ) (k : ℕ) (x : Space) : densityCut ρ k x ≤ (k:ℝ) := min_le_right _ _
lemma densityCut_measurable (ρ : Space → ℝ) (hm : Measurable ρ) (k : ℕ) :
    Measurable (densityCut ρ k) := hm.min measurable_const
lemma densityCut_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (k : ℕ) : Integrable (densityCut ρ k) := by
  apply hi.mono' (densityCut_measurable ρ hm k).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (densityCut_nonneg ρ hp k x)]
  exact densityCut_le ρ k x
lemma densityCut_kinetic_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (k : ℕ) :
    Integrable (fun x => densityCut ρ k x^(5/3:ℝ)) := by
  apply ht.mono' ((densityCut_measurable ρ hm k).pow_const _).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (densityCut_nonneg ρ hp k x) _)]
  exact Real.rpow_le_rpow (densityCut_nonneg ρ hp k x) (densityCut_le ρ k x) (by norm_num)
lemma densityCut_support (ρ : Space → ℝ) (K : Set Space)
    (hs : ∀ x, x ∉ K → ρ x = 0) (k : ℕ) (x : Space) (hx : x ∉ K) : densityCut ρ k x = 0 := by
  simp only [densityCut,hs x hx,min_eq_left (Nat.cast_nonneg k)]
lemma densityCut_tendsto (ρ : Space → ℝ) (x : Space) :
    Tendsto (fun k => densityCut ρ k x) atTop (nhds (ρ x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (ρ x))] with k hk
  exact (min_eq_left hk).symm

lemma packetDensity_mono (g : 𝓢(Space,ℝ)) (ρ σ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsp : ∀ x, 0 ≤ σ x) (hsm : Measurable σ) (hsi : Integrable σ)
    (h : ∀ x, ρ x ≤ σ x) (x : Space) : packetDensity g ρ x ≤ packetDensity g σ x := by
  exact integral_mono (packetDensity_integrand_integrable g ρ hp hm hi x)
    (packetDensity_integrand_integrable g σ hsp hsm hsi x)
    (fun y => mul_le_mul_of_nonneg_left (h y) (sq_nonneg _))

lemma packetDensity_cut_tendsto (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    Tendsto (fun k => packetDensity g (densityCut ρ k) x) atTop (nhds (packetDensity g ρ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => g (x-y)^2*ρ y)
    (fun k => (packetDensity_integrand_integrable g _ (densityCut_nonneg ρ hp k)
      (densityCut_measurable ρ hm k) (densityCut_integrable ρ hp hm hi k) x).1)
    (packetDensity_integrand_integrable g ρ hp hm hi x)
  · intro k
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (densityCut_nonneg ρ hp k y))]
    exact mul_le_mul_of_nonneg_left (densityCut_le ρ k y) (sq_nonneg _)
  · filter_upwards [] with y
    exact tendsto_const_nhds.mul (densityCut_tendsto ρ y)

lemma packetDensity_cut_weighted_tendsto (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ)
    (w : Space → ℝ) (hwp : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hwi : Integrable (fun x => w x*packetDensity g ρ x)) :
    Tendsto (fun k => ∫ x, w x*packetDensity g (densityCut ρ k) x) atTop
      (nhds (∫ x, w x*packetDensity g ρ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => w x*packetDensity g ρ x)
    (fun k => (hwm.mul (packetDensity_measurable g _ (densityCut_measurable ρ hm k))).aestronglyMeasurable) hwi
  · intro k
    filter_upwards [] with x
    change ‖w x*packetDensity g (densityCut ρ k) x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (hwp x) (packetDensity_nonneg g _ (densityCut_nonneg ρ hp k) x))]
    exact mul_le_mul_of_nonneg_left (packetDensity_mono g _ ρ (densityCut_nonneg ρ hp k)
      (densityCut_measurable ρ hm k) (densityCut_integrable ρ hp hm hi k) hp hm hi (densityCut_le ρ k) x) (hwp x)
  · filter_upwards [] with x
    exact tendsto_const_nhds.mul (packetDensity_cut_tendsto g ρ hp hm hi x)
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
