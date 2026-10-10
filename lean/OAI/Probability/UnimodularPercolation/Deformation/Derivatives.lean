import Mathlib
import OAI.Probability.UnimodularPercolation.Deformation.ClusterProducts

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedNeighborhoodEstimate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem twoPoint_neighbor_div_bound [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (v a z : V) (hz : z ∈ neighbors G hloc a) :
    twoPoint G p v z ≤ twoPoint G p v a / (p:ℝ) := by
  obtain ⟨e,he⟩ := (mem_neighbors G hloc a z).mp hz
  have hh := restrictedTwoPoint_adj_lower G Set.univ p a z v e he (Set.mem_univ _)
  simp only [Set.inter_univ] at hh
  change (p:ℝ)*twoPoint G p z v ≤ twoPoint G p a v at hh
  rw [twoPoint_symm G p z v,twoPoint_symm G p a v] at hh
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)

 

theorem neighborhood_twoPoint_bound [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d) (p : unitInterval) (hp : 0 < (p:ℝ))
    (W : Finset V) (v : V) :
    (∑' z : closedBondNeighborhood G (W:Set V), twoPoint G p v z) ≤
      (1+(d:ℝ)/(p:ℝ)) * (∑ a ∈ W, twoPoint G p v a) := by
  apply (neighborhood_mass_le G hloc W (twoPoint G p v) (twoPoint_nonneg G p v)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hsum : (∑ z ∈ neighbors G hloc a, twoPoint G p v z) ≤
      (d:ℝ)*(twoPoint G p v a/(p:ℝ)) := by
    calc
      _ ≤ ∑ _z ∈ neighbors G hloc a, twoPoint G p v a/(p:ℝ) :=
        Finset.sum_le_sum (fun z hz => twoPoint_neighbor_div_bound G hloc p hp v a z hz)
      _ = ((neighbors G hloc a).card:ℝ)*(twoPoint G p v a/(p:ℝ)) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hd a)) (div_nonneg (twoPoint_nonneg G p _ _) hp.le)
  calc
    _ ≤ twoPoint G p v a + (d:ℝ)*(twoPoint G p v a/(p:ℝ)) := add_le_add (le_refl _) hsum
    _ = _ := by ring

end WeightedNeighborhoodEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SizeWeightedPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def sizeMembership (G : BondGraph V E) (x a : V) (ω : Set E) : ℝ :=
  if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0

noncomputable def sizeWeightedConnectionPotential (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ := ∑' a, sizeMembership G x a ω * twoPoint G p y a

theorem sizeMembership_nonneg (G : BondGraph V E) (x a : V) (ω : Set E) :
    0 ≤ sizeMembership G x a ω := by
  unfold sizeMembership
  split_ifs
  · exact Nat.cast_nonneg _
  · rfl

theorem sizeMembership_le (G : BondGraph V E) (x a : V) (ω : Set E) :
    sizeMembership G x a ω ≤ ((cluster G ω x).ncard:ℝ) := by
  unfold sizeMembership
  split_ifs
  · rfl
  · exact Nat.cast_nonneg _

theorem measurable_sizeMembership [Countable V] [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (x a : V) : Measurable (sizeMembership G x a) := by
  apply Measurable.ite (measurableSet_conn G x a)
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)) measurable_const

theorem integrable_sizeMembership [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a : V) : Integrable (sizeMembership G x a) (law p) := by
  apply Integrable.mono' (susceptibility_eq_integral G hloc hqt p hp x).1
    (measurable_sizeMembership G hloc x a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_of_nonneg (sizeMembership_nonneg G x a ω)]
    exact sizeMembership_le G x a ω)

theorem integral_sizeMembership_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a : V) :
    (∫ ω, sizeMembership G x a ω ∂law p) ≤ susceptibility G p x := by
  rw [(susceptibility_eq_integral G hloc hqt p hp x).2]
  exact integral_mono (integrable_sizeMembership G hloc hqt p hp x a)
    (susceptibility_eq_integral G hloc hqt p hp x).1 (sizeMembership_le G x a)

theorem sizeWeightedConnectionPotential_eq_finite (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    sizeWeightedConnectionPotential G p x y ω =
      ((cluster G ω x).ncard:ℝ) * ∑ a ∈ hf.toFinset, twoPoint G p y a := by
  unfold sizeWeightedConnectionPotential
  rw [tsum_eq_sum (s := hf.toFinset)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hc : Conn G ω x a := hf.mem_toFinset.mp ha
    simp only [sizeMembership,ite_eq_left hc]
  · intro a ha
    have hn : ¬Conn G ω x a := fun hc => ha (hf.mem_toFinset.mpr hc)
    simp only [sizeMembership,ite_eq_right hn,zero_mul]

end SizeWeightedPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SizePotentialIntegral
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_sizePotential_integral_norm (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    Summable (fun a => ∫ ω, ‖sizeMembership G x a ω * twoPoint G p y a‖ ∂law p) := by
  apply ((summable_twoPoint_subcritical G hloc hqt p hp y).mul_left (susceptibility G p x)).of_nonneg_of_le
  · exact fun a => integral_nonneg (fun _ => norm_nonneg _)
  · intro a
    simp only [Real.norm_of_nonneg (mul_nonneg (sizeMembership_nonneg G x a _) (twoPoint_nonneg G p y a)),
      integral_mul_const]
    exact mul_le_mul_of_nonneg_right (integral_sizeMembership_le_susceptibility G hloc hqt p hp x a)
      (twoPoint_nonneg G p y a)

theorem integrable_sizeWeightedConnectionPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (sizeWeightedConnectionPotential G p x y) (law p) := by
  apply Integrable.mono' ((susceptibility_eq_integral G hloc hqt p hp x).1.mul_const
    (susceptibility G p y))
    (Measurable.tsum (fun a => (measurable_sizeMembership G hloc x a).mul_const (twoPoint G p y a))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    have hb (a : V) : sizeMembership G x a ω * twoPoint G p y a ≤
        ((cluster G ω x).ncard:ℝ)*twoPoint G p y a :=
      mul_le_mul_of_nonneg_right (sizeMembership_le G x a ω) (twoPoint_nonneg G p y a)
    have hn (a : V) : 0 ≤ sizeMembership G x a ω * twoPoint G p y a :=
      mul_nonneg (sizeMembership_nonneg G x a ω) (twoPoint_nonneg G p y a)
    have hs := (summable_twoPoint_subcritical G hloc hqt p hp y).mul_left ((cluster G ω x).ncard:ℝ)
    change ‖∑' a, sizeMembership G x a ω * twoPoint G p y a‖ ≤ _
    rw [Real.norm_of_nonneg (tsum_nonneg hn)]
    exact ((hs.of_nonneg_of_le hn hb).tsum_le_tsum hb hs).trans_eq (tsum_mul_left))

omit [Countable V] [Countable E] [Nonempty V] in
theorem sizeWeightedConnectionPotential_nonneg (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : 0 ≤ sizeWeightedConnectionPotential G p x y ω :=
  tsum_nonneg (fun a => mul_nonneg (sizeMembership_nonneg G x a ω) (twoPoint_nonneg G p y a))

theorem summable_twoPoint_cube_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    Summable (fun ba : V×V => twoPoint G p x ba.1 * twoPoint G p ba.1 ba.2 * twoPoint G p y ba.2) := by
  exact (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
    (fun ba => mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))
      (twoPoint_nonneg G p _ _))
    (fun ba => mul_le_of_le_one_right
      (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_le_one G p _ _))

 
theorem integral_sizeWeightedConnectionPotential_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    (∫ ω, sizeWeightedConnectionPotential G p x y ω ∂law p) ≤
      maxSusceptibility G p * (∑' a, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) := by
  have hi (a : V) := (integrable_sizeMembership G hloc hqt p hp x a).mul_const (twoPoint G p y a)
  have hs := summable_sizePotential_integral_norm G hloc hqt p hp x y
  have hc : Summable (fun a => ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) :=
    (summable_twoPoint_cube_pair G hloc hqt p hp x y).prod_symm.prod
  change (∫ ω, ∑' a, sizeMembership G x a ω * twoPoint G p y a ∂law p) ≤ _
  rw [←integral_tsum_of_summable_integral_norm hi hs,←tsum_mul_left]
  have hs' : Summable (fun a => ∫ ω, sizeMembership G x a ω * twoPoint G p y a ∂law p) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (sizeMembership_nonneg G x _ _) (twoPoint_nonneg G p y _))] using hs
  apply hs'.tsum_le_tsum (fun a => ?_) (hc.mul_left _)
  rw [integral_mul_const,tsum_mul_right]
  calc
    _ ≤ (maxSusceptibility G p * (∑' b, twoPoint G p x b * twoPoint G p b a)) * twoPoint G p y a :=
      mul_le_mul_of_nonneg_right (integral_size_membership_le G hloc hqt p hp x a) (twoPoint_nonneg G p y a)
    _ = _ := mul_assoc _ _ _

end SizePotentialIntegral
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedCorrelationPointwise
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem deformedFreshExteriorMoment_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : p < pc G) (hp₀ : 0 < (p:ℝ)) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (x y : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    deformedClusterMass G P p k t D ω x * deformedSusceptibility G P p k t D y -
      (1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p * sizeWeightedConnectionPotential G p x y ω ≤
      deformedFreshExteriorMoment G P p k t D x y ω := by
  let A := cluster G (ω ∩ internalEdges G D) x
  have hsub : A ⊆ cluster G ω x := fun _ h => conn_mono G Set.inter_subset_left h
  have hA : A.Finite := hf.subset hsub
  have hn : (∑' z : closedBondNeighborhood G A, twoPoint G p y z) ≤
      (1+(d:ℝ)/(p:ℝ))*(∑ a ∈ hf.toFinset, twoPoint G p y a) := by
    have hh := neighborhood_twoPoint_bound G hloc d hd p hp₀ hA.toFinset y
    rw [hA.coe_toFinset] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => hf.mem_toFinset.mpr (hsub (hA.mem_toFinset.mp ha)))
        (fun a _ _ => twoPoint_nonneg G p y a))
      (add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) hp₀.le)))
  have hm := deformedClusterMass_le_ncard G P hP p k t ht D ω x hf
  have hm₀ := deformedClusterMass_nonneg G P p k t D ω x
  have hχ : 0 ≤ maxSusceptibility G p := zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp)
  have hh := mul_le_mul_of_nonneg_left
    (deformedSusceptibility_deletion G hloc hqt P hP p hp k t ht D A y) hm₀
  have hsum : 0 ≤ ∑ a ∈ hf.toFinset, twoPoint G p y a :=
    Finset.sum_nonneg (fun a _ => twoPoint_nonneg G p y a)
  have hC : 0 ≤ 1+(d:ℝ)/(p:ℝ) := add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) hp₀.le)
  have herr : deformedClusterMass G P p k t D ω x *
      (maxSusceptibility G p * (∑' z : closedBondNeighborhood G A, twoPoint G p y z)) ≤
      (1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p * sizeWeightedConnectionPotential G p x y ω := by
    calc
      _ ≤ deformedClusterMass G P p k t D ω x *
          (maxSusceptibility G p * ((1+(d:ℝ)/(p:ℝ))*(∑ a ∈ hf.toFinset, twoPoint G p y a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hχ) hm₀
      _ ≤ ((cluster G ω x).ncard:ℝ)*
          (maxSusceptibility G p * ((1+(d:ℝ)/(p:ℝ))*(∑ a ∈ hf.toFinset, twoPoint G p y a))) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg hχ (mul_nonneg hC hsum))
      _ = _ := by rw [sizeWeightedConnectionPotential_eq_finite G p x y ω hf]; ring
  dsimp only [deformedFreshExteriorMoment]
  dsimp only [A] at hh
  nlinarith

end WeightedCorrelationPointwise
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedCorrelationIntegral
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem deformed_distinct_correlation (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : p < pc G) (hp₀ : 0 < (p:ℝ)) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (x y : V) :
    deformedSusceptibility G P p k t D x * deformedSusceptibility G P p k t D y -
      (1+(d:ℝ)/(p:ℝ))*(maxSusceptibility G p)^2 *
        (∑' a, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) ≤
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  rw [←integral_deformedFreshExteriorMoment G hloc hqt P hP p hp k t ht D x y]
  have hi := integrable_deformedClusterMass G hloc hqt P hP p hp k t ht D x
  have hj := integrable_sizeWeightedConnectionPotential G hloc hqt p hp x y
  have hb := integral_mono_ae
    ((hi.mul_const (deformedSusceptibility G P p k t D y)).sub
      (hj.const_mul ((1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p)))
    (integrable_deformedFreshExteriorMoment G hloc hqt P hP p hp k t ht D x y)
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      exact deformedFreshExteriorMoment_lower G hloc hqt d hd P hP p hp hp₀ k t ht D x y ω hω)
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hi.mul_const _) (hj.const_mul _),integral_mul_const,integral_const_mul,
    ←deformedSusceptibility_eq_integral G hloc hqt P hP p hp k t ht D x] at hb
  have hC : 0 ≤ (1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p :=
    mul_nonneg (add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) hp₀.le))
      (zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp))
  have herr := mul_le_mul_of_nonneg_left
    (integral_sizeWeightedConnectionPotential_le G hloc hqt p hp x y) hC
  nlinarith

end WeightedCorrelationIntegral
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExactCubeKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem HasKernel.square_real_kernel (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (∑' b, twoPoint G p x b * twoPoint G p b y) = (matrixCoeff (T^2) x y).re := by
  have hh := ((hT.positiveRealMatrix G p T).mul_hasSum T x y).tsum_eq
  simpa only [hT.matrixCoeff_re G p T,pow_two] using hh

theorem HasKernel.cube_real_kernel (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (∑' a, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) =
      (matrixCoeff (T^3) x y).re := by
  have hh := (((hT.positiveRealMatrix G p T).pow 2).mul_hasSum T x y).tsum_eq
  calc
    _ = ∑' a, (matrixCoeff (T^2) x a).re * (matrixCoeff T a y).re := by
      apply tsum_congr
      intro a
      rw [tsum_mul_right,hT.square_real_kernel G p T x a,hT.matrixCoeff_re G p T a y,twoPoint_symm G p y a]
    _ = _ := by simpa only [show T^2*T = T^3 by rw [←pow_succ]] using hh

end ExactCubeKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformWeightedCorrelation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem deformed_distinct_correlation_uniform (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    deformedSusceptibility G P p k t D x * deformedSusceptibility G P p k t D y -
      (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 * (matrixCoeff (T^3) x y).re ≤
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  have hp₀ : 0 < (p:ℝ) := (half_pos hpcrit).trans_le hpnear
  have hb := deformed_distinct_correlation G hloc hqt d hd P hP p hp hp₀ k t ht D x y
  rw [hT.cube_real_kernel G p T x y] at hb
  have hc : (d:ℝ)/(p:ℝ) ≤ 2*(d:ℝ)/(pc G:ℝ) := by
    apply (div_le_div_iff₀ hp₀ hpcrit).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have he := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1:ℝ)) hc)
    (mul_nonneg (sq_nonneg (maxSusceptibility G p)) (((hT.positiveRealMatrix G p T).pow 3) x y).2)
  nlinarith

end UniformWeightedCorrelation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSizeBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incidentSupport_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (incidentSupport G hloc W).card ≤ W.card*d := by
  apply Finset.card_biUnion_le_card_mul
  intro x _
  rw [←Set.ncard_eq_toFinset_card _ (hloc x)]
  exact (incident_ncard_le_degree G hloc x).trans (hd x)

theorem reachBall_ncard_le_pow (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (k : ℕ) :
    (reachBall G x k).ncard ≤ (d+1)^k := by
  induction k with
  | zero => simp only [reachBall,Set.ncard_singleton,pow_zero,le_refl]
  | succ k ih =>
    let W := (finite_reachBall hloc x k).toFinset
    have he : reachBall G x (k+1) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
      ext z
      simp only [reachBall,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,Finset.mem_coe,
        Finset.mem_union,Finset.mem_biUnion,mem_neighbors,Set.Finite.mem_toFinset,W,Adj,exists_prop]
    rw [he,Set.ncard_coe_finset]
    have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => (neighbors_card_le_degree G hloc a).trans (hd a))
    have hi : W.card ≤ (d+1)^k := by simpa only [W,←Set.ncard_eq_toFinset_card] using ih
    calc
      _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
      _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
      _ = W.card*(d+1) := by ring
      _ ≤ (d+1)^k*(d+1) := Nat.mul_le_mul_right _ hi
      _ = _ := (pow_succ _ _).symm

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem interior_card_le (w : RawCorridor G k) : w.interior.card ≤ w.path.length := by
  have hs : w.interior ⊂ w.path.support.toFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset,?_⟩
    intro he
    have hb : w.base ∈ w.path.support.toFinset := List.mem_toFinset.mpr w.path.start_mem_support
    rw [←he] at hb
    have hn : w.base ∉ w.interior := by simp only [interior,Finset.mem_sdiff,Finset.mem_insert,
      true_or,not_true_eq_false,and_false,not_false_eq_true]
    exact hn hb
  have hh := Finset.card_lt_card hs
  rw [List.toFinset_card_of_nodup w.path_isPath.support_nodup,SimpleGraph.Walk.length_support] at hh
  omega

theorem blockers_ncard_le (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (w : RawCorridor G k) : w.blockers.ncard ≤ d*k := by
  have hs : w.blockers ⊆ (incidentSupport G hloc w.interior : Set E) :=
    fun e he => (mem_incidentSupport G hloc w.interior e).mpr he.1
  calc
    _ ≤ (incidentSupport G hloc w.interior : Set E).ncard := Set.ncard_le_ncard hs (Finset.finite_toSet _)
    _ = (incidentSupport G hloc w.interior).card := Set.ncard_coe_finset _
    _ ≤ w.interior.card*d := incidentSupport_card_le G hloc d hd _
    _ ≤ k*d := Nat.mul_le_mul_right _ (w.interior_card_le.trans w.path_length)
    _ = _ := Nat.mul_comm _ _

end RawCorridor
end CorridorSizeBounds
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkTotalMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
  apply (Finset.finite_toSet (insert x (neighbors G hloc x))).subset
  intro y hy
  by_contra hn
  have hn' : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_coe,Finset.mem_insert,mem_neighbors,not_or] using hn
  exact hy (by simp only [walkKernel,ite_eq_right hn'.1.symm,ite_eq_right hn'.2,add_zero])

theorem walkKernel_tsum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    (∑' y, walkKernel G hloc a x y) = 1 := by
  rw [tsum_eq_sum (s := insert x (neighbors G hloc x))]
  · exact walkKernel_row_sum G hloc a x
  · intro y hy
    have hn : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_insert,mem_neighbors,not_or] using hy
    simp only [walkKernel,ite_eq_right hn.1.symm,ite_eq_right hn.2,add_zero]

theorem raw_integral_one (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (k : ℕ) (x : V) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x (fun _ => 1) = 1 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction k generalizing x with
  | zero => exact RawFrom.integral_zero _ _ _
  | succ k ih =>
    rw [RawFrom.integral_succ]
    simp only [ih,mul_one]
    have he := sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a)
      (walkKernel_finite_support G hloc a) (fun x y hxy hn => by
        apply walkKernel_zero_of_not_step G hloc a x y hxy
        intro h
        obtain ⟨e,he⟩ := h
        exact hn ⟨hxy,e,Set.mem_univ e,he⟩) x (fun _ => 1)
    simpa only [mul_one,walkKernel_tsum G hloc a] using he.symm

 
theorem rawFrom_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (x : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) k x, w.2.mass (walkKernel G hloc a)) = 1 := by
  simpa only [RawFrom.integral,mul_one] using raw_integral_one G hloc a k x

end RawWalkTotalMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkFiniteBases
attribute [local instance] Classical.propDecidable Classical.decEq

theorem raw_probability_on_bases_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (S : Set V) (hS : S.Finite) :
    (∑' w : RawCorridor G k, if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) = (S.ncard:ℝ) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  have hs : Summable (fun w : RawCorridor G k => if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (finite_corridors_on_bases G hloc k S hS).subset
    intro w hw
    by_contra hn
    exact hw (ite_eq_right hn)
  rw [hs.tsum_sigma]
  have he (x : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k x,
      if (RawCorridor.base ⟨x,w⟩) ∈ S then (RawCorridor.probability (walkKernel G hloc a) ⟨x,w⟩) else 0) =
      if x ∈ S then 1 else 0 := by
    by_cases hx : x ∈ S
    · simp only [RawCorridor.base,RawCorridor.probability,hx,ite_true,rawFrom_probability_sum G hloc a k x]
    · simp only [RawCorridor.base,hx,ite_false,tsum_zero]
  simp only [he]
  rw [tsum_eq_sum (s := hS.toFinset)]
  · rw [Finset.sum_congr rfl (fun x hx => ite_eq_left (hS.mem_toFinset.mp hx))]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [←Set.ncard_eq_toFinset_card _ hS]
  · intro x hx
    exact ite_eq_right (fun h => hx (hS.mem_toFinset.mpr h))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem base_mem_reachBall_of_retained (w : RawCorridor G k) (e : E)
    (he : e ∈ w.retained) (z : V) (hz : z ∈ G e) : w.base ∈ reachBall G z k := by
  have hs : z ∈ w.path.support := SimpleGraph.Walk.mem_support_of_mem_edges he hz
  let q := (w.path.takeUntil z hs).reverse
  have hq : q.length ≤ k := by
    change (w.path.takeUntil z hs).reverse.length ≤ k
    rw [SimpleGraph.Walk.length_reverse]
    exact (w.path.length_takeUntil_le_length hs).trans w.path_length
  have hh := walk_mem_reachBall G Set.univ (x := z) q 0 (by simp only [reachBall,Set.mem_singleton_iff])
  simp only [Nat.zero_add] at hh
  exact reachBall_mono_local G z hq hh

theorem counted_base_mem_cluster (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : w.counted D ω x y) : w.base ∈ cluster G ω x := by
  obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
  have hm := w.counted_base_mem_walk D ω x y hc q
  exact conn_mono G Set.inter_subset_left ((conn_iff_reachable G _ x w.base).mpr ⟨q.takeUntil w.base hm⟩)

end RawCorridor
end RawWalkFiniteBases
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def rawWeightBase (r q : ℝ) (d : ℕ) : ℝ := r⁻¹ * (q⁻¹)^d

theorem rawWeightBase_one_le {r q : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hq : 0 < q) (hq₁ : q ≤ 1) (d : ℕ) : 1 ≤ rawWeightBase r q d := by
  exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hr).mpr hr₁)
    (one_le_pow₀ ((one_le_inv₀ hq).mpr hq₁))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem weight_le_uniform (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (w : RawCorridor G k) : w.weight P p ≤ w.probability P * (rawWeightBase r q d)^k := by
  have hp₀ : 0 < (p:ℝ) := hr.trans_le hrp
  have hp₁ : 0 < 1-(p:ℝ) := hq.trans_le hqp
  have hr₁ : r ≤ 1 := hrp.trans p.2.2
  have hq₁ : q ≤ 1 := hqp.trans (sub_le_self _ p.2.1)
  have hi : (p:ℝ)⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrp
  have hj : (1-(p:ℝ))⁻¹ ≤ q⁻¹ := inv_anti₀ hq hqp
  have hL : ((p:ℝ)^w.path.length)⁻¹ ≤ (r⁻¹)^k := by
    simp only [←inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr p.2.1) hi _).trans
      (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hr₁) w.path_length)
  have hB : ((1-(p:ℝ))^w.blockers.ncard)⁻¹ ≤ ((q⁻¹)^d)^k := by
    simp only [←inv_pow,←pow_mul]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hp₁.le) hj _).trans
      (pow_le_pow_right₀ ((one_le_inv₀ hq).mpr hq₁) (w.blockers_ncard_le hloc d hd))
  unfold weight
  calc
    _ = w.probability P * (((p:ℝ)^w.path.length)⁻¹ * ((1-(p:ℝ))^w.blockers.ncard)⁻¹) := mul_assoc _ _ _
    _ ≤ w.probability P * ((r⁻¹)^k * ((q⁻¹)^d)^k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hL hB
        (inv_nonneg.mpr (pow_nonneg hp₁.le _)) (pow_nonneg (inv_nonneg.mpr hr.le) _))
        (w.2.2.mass_nonneg P hP)
    _ = _ := by rw [rawWeightBase,mul_pow]

end RawCorridor
end UniformRawWeight
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformPenaltyDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_raw_selection (G : BondGraph V E) (hloc : LocallyFinite G)
    (k : ℕ) (S : Set V) (hS : S.Finite) (Q : RawCorridor G k → Prop)
    (hQ : ∀ w, Q w → w.base ∈ S) (f : RawCorridor G k → ℝ) :
    Summable (fun w => if Q w then f w else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_corridors_on_bases G hloc k S hS).subset
  intro w hw
  by_contra hn
  exact hw (ite_eq_right (fun h => hn (hQ w h)))

theorem mask_le_mask_mul {U W : Prop} [Decidable U] [Decidable W] (hUW : U → W)
    {f g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hfg : f ≤ g*B) :
    (if U then f else 0) ≤ (if W then g else 0)*B := by
  by_cases hU : U
  · simp only [hU,hUW hU,ite_true]; exact hfg
  · rw [ite_eq_right hU]
    by_cases hW : W
    · rw [ite_eq_left hW]; exact mul_nonneg hg hB
    · rw [ite_eq_right hW,zero_mul]

theorem raw_weight_sum_le_on_bases (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (S : Set V) (hS : S.Finite) (Q : RawCorridor G k → Prop)
    (hQ : ∀ w, Q w → w.base ∈ S) :
    (∑' w : RawCorridor G k, if Q w then w.weight (walkKernel G hloc a) p else 0) ≤
      (S.ncard:ℝ)*(rawWeightBase r q d)^k := by
  have hf := summable_raw_selection G hloc k S hS Q hQ
    (fun w => w.weight (walkKernel G hloc a) p)
  have hg := summable_raw_selection G hloc k S hS (fun w => w.base ∈ S)
    (fun _ h => h) (fun w => w.probability (walkKernel G hloc a))
  have hB : 0 ≤ (rawWeightBase r q d)^k := pow_nonneg
    (zero_le_one.trans (rawWeightBase_one_le hr (hrp.trans p.2.2) hq (hqp.trans (sub_le_self _ p.2.1)) d)) _
  have hpoint (w : RawCorridor G k) :
      (if Q w then w.weight (walkKernel G hloc a) p else 0) ≤
        (if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) * (rawWeightBase r q d)^k :=
    mask_le_mask_mul (hQ w) (w.2.2.mass_nonneg _ hP) hB
      (w.weight_le_uniform hloc d hd (walkKernel G hloc a) hP p hr hq hrp hqp)
  have hb := hf.tsum_le_tsum hpoint (hg.mul_right ((rawWeightBase r q d)^k))
  rw [tsum_mul_right,raw_probability_on_bases_sum G hloc a k S hS] at hb
  exact hb

 

theorem corridorPenalty_le_cluster (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) (hf : (cluster G ω x).Finite) :
    corridorPenalty G (walkKernel G hloc a) p k D ω x y ≤
      ((cluster G ω x).ncard:ℝ)*(rawWeightBase r q d)^k := by
  exact raw_weight_sum_le_on_bases G hloc d hd a hP p hr hq hrp hqp k _ hf
    (fun w => w.counted D ω x y) (fun w hw => w.counted_base_mem_cluster D ω x y hw)

 

theorem raw_edge_weight_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (e : E) (z : V) (hz : z ∈ G e) :
    (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤
      (((d:ℝ)+1)*rawWeightBase r q d)^k := by
  have hb := raw_weight_sum_le_on_bases G hloc d hd a hP p hr hq hrp hqp k
    (reachBall G z k) (finite_reachBall hloc z k) (fun w => e ∈ w.retained)
    (fun w hw => w.base_mem_reachBall_of_retained e hw z hz)
  have hcard : ((reachBall G z k).ncard:ℝ) ≤ ((d:ℝ)+1)^k := by
    exact_mod_cast reachBall_ncard_le_pow G hloc d hd z k
  have hB : 0 ≤ (rawWeightBase r q d)^k := pow_nonneg
    (zero_le_one.trans (rawWeightBase_one_le hr (hrp.trans p.2.2) hq (hqp.trans (sub_le_self _ p.2.1)) d)) _
  exact hb.trans ((mul_le_mul_of_nonneg_right hcard hB).trans_eq (mul_pow _ _ _).symm)

end UniformPenaltyDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExponentialCorridorCost
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pow_le_exp_div_self {B : ℝ} (hB : 1 ≤ B) {k : ℕ} (hk : 0 < k) :
    B^k ≤ Real.exp ((Real.log B + 1)*(k:ℝ))/(k:ℝ) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  apply (le_div_iff₀ (Nat.cast_pos.mpr hk)).mpr
  have hh : (k:ℝ) ≤ Real.exp (k:ℝ) := by linarith [Real.add_one_le_exp (k:ℝ)]
  calc
    _ ≤ B^k * Real.exp (k:ℝ) := mul_le_mul_of_nonneg_left hh (pow_nonneg hB₀.le _)
    _ = Real.exp ((k:ℝ)*Real.log B) * Real.exp (k:ℝ) := by rw [Real.exp_nat_mul,Real.exp_log hB₀]
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

 

theorem exists_uniform_corridor_edge_cost (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ e : E,
      (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤
        Real.exp (C*(k:ℝ))/(k:ℝ) := by
  let B := ((d:ℝ)+1)*rawWeightBase ((pc G:ℝ)/2) (1-(pc G:ℝ)) d
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    (rawWeightBase_one_le (half_pos hpcrit) (by have := (pc G).2.2; linarith)
      (sub_pos.mpr hpcrit₁) (sub_le_self _ (pc G).2.1) d)
  refine ⟨Real.log B + 1,by linarith [Real.log_nonneg hB],?_⟩
  intro p hpnear hp k hk e
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have he : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  have hq : 1-(pc G:ℝ) ≤ 1-(p:ℝ) := sub_le_sub_left (show (p:ℝ) ≤ (pc G:ℝ) from hp.le) (1:ℝ)
  exact (raw_edge_weight_bound G hloc d hd a hP p (half_pos hpcrit)
    (sub_pos.mpr hpcrit₁) hpnear hq k e z he).trans (pow_le_exp_div_self hB (by omega))

end ExponentialCorridorCost
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LiteralDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedDerivativeMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) : ℝ :=
  ∑' y, corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y

theorem deformedConnection_eq_zero_of_not_conn (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) (hn : ¬Conn G ω x y) :
    deformedConnection G P p k t D ω x y = 0 := by
  have hnc : ¬Conn G (ω ∩ internalEdges G D) x y := fun h => hn (conn_mono G Set.inter_subset_left h)
  simp only [deformedConnection,hnc,and_false,ite_false]

theorem deformedClusterMass_eq_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : deformedClusterMass G P p k t D ω x =
      ∑ y ∈ hf.toFinset, deformedConnection G P p k t D ω x y := by
  apply tsum_eq_sum
  intro y hy
  exact deformedConnection_eq_zero_of_not_conn G P p k t D ω x y (fun h => hy (hf.mem_toFinset.mpr h))

theorem deformedDerivativeMass_eq_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : deformedDerivativeMass G P p k t D ω x =
      ∑ y ∈ hf.toFinset, corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y := by
  apply tsum_eq_sum
  intro y hy
  rw [deformedConnection_eq_zero_of_not_conn G P p k t D ω x y (fun h => hy (hf.mem_toFinset.mpr h)),mul_zero]

theorem measurable_deformedDerivativeMass [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    Measurable (fun ω => deformedDerivativeMass G P p k t D ω x) :=
  Measurable.tsum (fun y => (measurable_corridorPenalty G P p k D x y).mul
    (measurable_deformedConnection G P p k t D x y))

theorem deformedDerivativeMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ)
    (D : Set V) (ω : Set E) (x : V) : 0 ≤ deformedDerivativeMass G P p k t D ω x :=
  tsum_nonneg (fun y => mul_nonneg (corridorPenalty_nonneg G P hP p k D ω x y)
    (deformedConnection_nonneg G P p k t D ω x y))

theorem hasDerivAt_deformedConnection (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    HasDerivAt (fun s => deformedConnection G P p k s D ω x y)
      (-(corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y)) t := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · simp only [deformedConnection,hc,and_self,ite_true]
    simpa only [Pi.neg_apply,id_eq,neg_mul,one_mul,mul_neg,mul_comm] using
      (((hasDerivAt_id t).neg.mul_const (corridorPenalty G P p k D ω x y)).exp)
  · simpa only [deformedConnection,hc,ite_false,mul_zero,neg_zero] using hasDerivAt_const t (0:ℝ)

 

theorem hasDerivAt_deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) :
    HasDerivAt (fun s => deformedClusterMass G P p k s D ω x)
      (-deformedDerivativeMass G P p k t D ω x) t := by
  have hh := HasDerivAt.fun_sum (u := hf.toFinset) (fun y _ => hasDerivAt_deformedConnection G P p k t D ω x y)
  simpa only [deformedClusterMass_eq_sum G P p k _ D ω x hf,
    deformedDerivativeMass_eq_sum G P p k t D ω x hf,Finset.sum_neg_distrib] using hh

end LiteralDeformationDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationDerivativeDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedDerivativeMass_le_square (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ≤
      ((cluster G ω x).ncard:ℝ)^2 * (rawWeightBase p (1-(p:ℝ)) d)^k := by
  rw [deformedDerivativeMass_eq_sum G (walkKernel G hloc a) p k t D ω x hf]
  calc
    _ ≤ ∑ _y ∈ hf.toFinset, ((cluster G ω x).ncard:ℝ)*(rawWeightBase p (1-(p:ℝ)) d)^k := by
      apply Finset.sum_le_sum
      intro y _
      have hn := corridorPenalty_nonneg G (walkKernel G hloc a) hP p k D ω x y
      exact (mul_le_of_le_one_right hn (deformedConnection_le_one G (walkKernel G hloc a) hP p k t ht D ω x y)).trans
        (corridorPenalty_le_cluster G hloc d hd a hP p hp0 (sub_pos.mpr hp1) le_rfl le_rfl k D ω x y hf)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
      ring

theorem integrable_deformedDerivativeMass [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (x : V) :
    Integrable (fun ω => deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x) (law p) := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  apply Integrable.mono' ((hs x).1.mul_const ((rawWeightBase p (1-(p:ℝ)) d)^k))
    (measurable_deformedDerivativeMass G (walkKernel G hloc a) p k t D x).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
  rw [Real.norm_of_nonneg (deformedDerivativeMass_nonneg G (walkKernel G hloc a) hP p k t D ω x)]
  exact deformedDerivativeMass_le_square G hloc d hd a hP p hp0
    ((show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2) k t ht D ω x hω

end DeformationDerivativeDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section DeformationDifferentiation
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem hasDerivAt_deformedSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 < t)
    (D : Set V) (x : V) :
    HasDerivAt (fun s => deformedSusceptibility G (walkKernel G hloc a) p k s D x)
      (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ∂law p)) t := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have hp1 : (p:ℝ) < 1 := (show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := law p) (s := Set.Ioi 0) (x₀ := t)
    (F := fun s ω => deformedClusterMass G (walkKernel G hloc a) p k s D ω x)
    (F' := fun s ω => -deformedDerivativeMass G (walkKernel G hloc a) p k s D ω x)
    (bound := fun ω => ((cluster G ω x).ncard:ℝ)^2*(rawWeightBase p (1-(p:ℝ)) d)^k)
    (Ioi_mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (measurable_deformedClusterMass G (walkKernel G hloc a) p k s D x).aestronglyMeasurable))
    (integrable_deformedClusterMass G hloc hqt (walkKernel G hloc a) hP p hp k t ht.le D x)
    (measurable_deformedDerivativeMass G (walkKernel G hloc a) p k t D x).neg.aestronglyMeasurable
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      intro s hs
      rw [norm_neg,Real.norm_of_nonneg (deformedDerivativeMass_nonneg G (walkKernel G hloc a) hP p k s D ω x)]
      exact deformedDerivativeMass_le_square G hloc d hd a hP p hp0 hp1 k s hs.le D ω x hω)
    ((hs x).1.mul_const _)
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      intro s _
      exact hasDerivAt_deformedClusterMass G (walkKernel G hloc a) p k s D ω x hω)
  rw [integral_neg] at hder
  apply hder.2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact deformedSusceptibility_eq_integral G hloc hqt (walkKernel G hloc a) hP p hp k s hs.le D x

end DeformationDifferentiation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section ContinuousDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem continuous_deformedConnection (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    Continuous (fun s => deformedConnection G P p k s D ω x y) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_deformedConnection G P p k t D ω x y).continuousAt)

theorem continuous_deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    Continuous (fun s => deformedClusterMass G P p k s D ω x) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_deformedClusterMass G P p k t D ω x hf).continuousAt)

theorem continuous_deformedDerivativeMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    Continuous (fun s => deformedDerivativeMass G P p k s D ω x) := by
  simp_rw [deformedDerivativeMass_eq_sum G P p k _ D ω x hf]
  exact continuous_finsetSum _ (fun y _ => continuous_const.mul (continuous_deformedConnection G P p k D ω x y))

 

theorem continuousOn_integral_deformedDerivativeMass [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (D : Set V) (x : V) :
    ContinuousOn (fun t => ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ∂law p) (Set.Ici 0) := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  apply continuousOn_of_dominated
    (bound := fun ω => ((cluster G ω x).ncard:ℝ)^2*(rawWeightBase p (1-(p:ℝ)) d)^k)
  · intro t _
    exact (measurable_deformedDerivativeMass G (walkKernel G hloc a) p k t D x).aestronglyMeasurable
  · intro t ht
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    rw [Real.norm_of_nonneg (deformedDerivativeMass_nonneg G (walkKernel G hloc a) hP p k t D ω x)]
    exact deformedDerivativeMass_le_square G hloc d hd a hP p hp0
      ((show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2) k t ht D ω x hω
  · exact (hs x).1.mul_const _
  · filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    exact (continuous_deformedDerivativeMass G (walkKernel G hloc a) p k D ω x hω).continuousOn

end ContinuousDeformationDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RightDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem continuousOn_deformedSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (D : Set V) (x : V) :
    ContinuousOn (fun t => deformedSusceptibility G P p k t D x) (Set.Ici 0) := by
  have hc : ContinuousOn (fun t => ∫ ω, deformedClusterMass G P p k t D ω x ∂law p) (Set.Ici 0) := by
    apply continuousOn_of_dominated (bound := fun ω => ((cluster G ω x).ncard:ℝ))
    · intro t _
      exact (measurable_deformedClusterMass G P p k t D x).aestronglyMeasurable
    · intro t ht
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      rw [Real.norm_of_nonneg (deformedClusterMass_nonneg G P p k t D ω x)]
      exact deformedClusterMass_le_ncard G P hP p k t ht D ω x hω
    · exact (susceptibility_eq_integral G hloc hqt p hp x).1
    · filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      exact (continuous_deformedClusterMass G P p k D ω x hω).continuousOn
  exact hc.congr (fun t ht => deformedSusceptibility_eq_integral G hloc hqt P hP p hp k t ht D x)

 

theorem hasDerivWithinAt_deformedSusceptibility_zero [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (D : Set V) (x : V) :
    HasDerivWithinAt (fun t => deformedSusceptibility G (walkKernel G hloc a) p k t D x)
      (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k 0 D ω x ∂law p)) (Set.Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
  · intro t ht
    exact (hasDerivAt_deformedSusceptibility G hloc hqt d hd a hP p hp0 hp k t ht D x).differentiableAt.differentiableWithinAt
  · exact (continuousOn_deformedSusceptibility G hloc hqt (walkKernel G hloc a) hP p hp k D x 0 (by simp)).mono Set.Ioi_subset_Ici_self
  · exact self_mem_nhdsWithin
  · have hc := (continuousOn_integral_deformedDerivativeMass G hloc hqt d hd a hP p hp0 hp k D x 0 (by simp)).neg
    apply (hc.mono Set.Ioi_subset_Ici_self).congr'
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := 0)] with t ht
    exact (hasDerivAt_deformedSusceptibility G hloc hqt d hd a hP p hp0 hp k t ht D x).deriv.symm

end RightDeformationDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalMoveGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_move_terminal (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (F : Set E) (hF : F ⊆ ω ∩ internalEdges G D) (b z y : V)
    (hbz : Conn G F b z) (hc : w.counted D ω b y) (hdis : Disjoint F w.retained) :
    w.counted D ω z y := by
  apply (w.counted_iff D ω z y).mpr
  refine ⟨hc.1,conn_trans G _ (conn_symm G _ (conn_mono G hF hbz)) hc.2.2.1,?_,hc.2.2.2.2⟩
  intro e he
  refine ⟨(hc.2.2.2.1 e he).1,?_⟩
  intro hzy
  apply (hc.2.2.2.1 e he).2
  apply conn_trans G _ (conn_mono G ?_ hbz) hzy
  intro f hf
  refine ⟨hF hf,?_⟩
  intro hfe
  have hh : f = e := Set.mem_singleton_iff.mp hfe
  exact Set.disjoint_left.mp hdis hf (hh.symm ▸ he)

end RawCorridor

 

theorem corridorPenaltyTerm_move_bound (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (D : Set V) (ω : Set E)
    (F : Finset E) (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V)
    (hbz : Conn G (F:Set E) b z) (w : RawCorridor G k) :
    corridorPenaltyTerm G P p D ω b y w ≤
      (∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0) + corridorPenaltyTerm G P p D ω z y w := by
  have hn := w.weight_nonneg P hP p
  have hs : 0 ≤ ∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0 :=
    Finset.sum_nonneg (fun e _ => by split_ifs; exact hn; exact le_rfl)
  by_cases hc : w.counted D ω b y
  · rw [corridorPenaltyTerm,ite_eq_left hc]
    by_cases hd : Disjoint (F:Set E) w.retained
    · have hc' := w.counted_move_terminal D ω F hF b z y hbz hc hd
      simpa only [corridorPenaltyTerm,hc',ite_true] using le_add_of_nonneg_left hs
    · obtain ⟨e,he,hew⟩ := Set.not_disjoint_iff.mp hd
      have he' : (if e ∈ w.retained then w.weight P p else 0) ≤
          ∑ f ∈ F, if f ∈ w.retained then w.weight P p else 0 :=
        Finset.single_le_sum (f := fun f => if f ∈ w.retained then w.weight P p else 0) (fun f _ => by split_ifs; exact hn; exact le_rfl) he
      rw [ite_eq_left hew] at he'
      exact he'.trans (le_add_of_nonneg_right (corridorPenaltyTerm_nonneg G P hP p D ω z y w))
  · rw [corridorPenaltyTerm,ite_eq_right hc]
    exact add_nonneg hs (corridorPenaltyTerm_nonneg G P hP p D ω z y w)

end TerminalMoveGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalMovePenalty
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_raw_edge_weights (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (e : E) :
    Summable (fun w : RawCorridor G k => if e ∈ w.retained then w.weight P p else 0) := by
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have he : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  exact summable_raw_selection G hloc k (reachBall G z k) (finite_reachBall hloc z k)
    (fun w => e ∈ w.retained) (fun w hw => w.base_mem_reachBall_of_retained e hw z he)
    (fun w => w.weight P p)

 

theorem corridorPenalty_move_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V) (hbz : Conn G (F:Set E) b z) :
    corridorPenalty G P p k D ω b y ≤
      (∑ e ∈ F, ∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) +
        corridorPenalty G P p k D ω z y := by
  have hs : Summable (fun w : RawCorridor G k => ∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0) :=
    (hasSum_sum (fun e (_ : e ∈ F) => (summable_raw_edge_weights G hloc P p k e).hasSum)).summable
  have hr := corridorPenalty_summable G hloc P p k D ω z y
  have hl := (corridorPenalty_summable G hloc P p k D ω b y).tsum_le_tsum
    (corridorPenaltyTerm_move_bound G P hP p k D ω F hF b z y hbz) (hs.add hr)
  rw [hs.tsum_add hr,Summable.tsum_finsetSum (fun e _ => summable_raw_edge_weights G hloc P p k e)] at hl
  exact hl

end TerminalMovePenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteOpeningAssociation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_union_const (S : Set E) : Measurable (fun ω : Set E => ω ∪ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).or measurable_const

theorem measurableSet_finite_open (F : Finset E) : MeasurableSet {ω : Set E | (F:Set E) ⊆ ω} := by
  have he : {ω : Set E | (F:Set E) ⊆ ω} = ⋂ e ∈ F, {ω : Set E | e ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.mem_coe,Set.subset_def]
  rw [he]
  exact F.measurableSet_biInter (fun e _ => measurableSet_setOfPred.mpr ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable))

 

theorem finite_open_integral_lower (p : unitInterval) (F : Finset E) (f : Set E → ℝ)
    (hf : Measurable f) (hn : ∀ ω, 0 ≤ f ω) (hb : ∀ ω, f ω ≤ 1)
    (hm : Monotone f) :
    (p:ℝ)^F.card*(∫ ω, f ω ∂law p) ≤ ∫ ω, if (F:Set E) ⊆ ω then f ω else 0 ∂law p := by
  let J : Set E → ℝ := fun ω => if (F:Set E) ⊆ ω then 1 else 0
  let g : Set E → ℝ := fun ω => f (ω ∪ (F:Set E))
  have hJ : Measurable J := Measurable.ite (measurableSet_finite_open F) measurable_const measurable_const
  have hg : Measurable g := hf.comp (measurable_union_const (F:Set E))
  have hi (f : Set E → ℝ) (hfm : Measurable f) (hfn : ∀ ω, 0 ≤ f ω) (hfb : ∀ ω, f ω ≤ 1) : Integrable f (law p) := by
    exact Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (hfn ω)]; exact hfb ω))
  have hfi := hi f hf hn hb
  have hgi := hi g hg (fun ω => hn _) (fun ω => hb _)
  have hJint : (∫ ω, J ω ∂law p) = (p:ℝ)^F.card := by
    have hh := integral_indicator_const (μ := law p) (1:ℝ) (measurableSet_finite_open F)
    simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one,finite_open_probability,J] using hh
  have he := integral_mul_disjoint_coordinates p (F:Set E) (F:Set E)ᶜ disjoint_compl_right J g hJ hg
    (fun ω => by simp only [J,Set.subset_inter_iff,Set.Subset.refl,and_true])
    (fun ω => by
      dsimp only [g]
      congr 1
      ext e
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
      tauto)
  calc
    _ ≤ (p:ℝ)^F.card*(∫ ω, g ω ∂law p) := mul_le_mul_of_nonneg_left
      (integral_mono hfi hgi (fun ω => hm Set.subset_union_left)) (pow_nonneg p.2.1 _)
    _ = (∫ ω, J ω ∂law p)*(∫ ω, g ω ∂law p) := by rw [hJint]
    _ = ∫ ω, J ω*g ω ∂law p := he.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hF : (F:Set E) ⊆ ω
        · simp only [J,g,hF,ite_true,one_mul,Set.union_eq_left.mpr hF]
        · simp only [J,hF,ite_false,zero_mul])

end FiniteOpeningAssociation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalConnectionComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_move_edge_cost (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V) (hbz : Conn G (F:Set E) b z)
    (c : ℝ) (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    corridorPenalty G P p k D ω b y ≤ (F.card:ℝ)*c+corridorPenalty G P p k D ω z y := by
  apply (corridorPenalty_move_bound G hloc P hP p k D ω F hF b z y hbz).trans
  apply add_le_add _ le_rfl
  exact (Finset.sum_le_sum (fun e _ => hc e)).trans_eq (by simp only [Finset.sum_const,nsmul_eq_mul])

 

theorem deformedConnection_move_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z y : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (if (F:Set E) ⊆ ω then deformedConnection G P p k t D ω z y else 0) ≤
      deformedConnection G P p k t D ω b y := by
  by_cases ho : (F:Set E) ⊆ ω
  · rw [ite_eq_left ho]
    by_cases hz : z ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) z y
    · have hFa : (F:Set E) ⊆ ω ∩ internalEdges G D := fun e he => ⟨ho he,hF he⟩
      have hb' : b ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) b y :=
        ⟨hb,hz.2.1,conn_trans G _ (conn_mono G hFa hbz) hz.2.2⟩
      simp only [deformedConnection,hz,hb',and_self,ite_true]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonpos_left
        (corridorPenalty_move_edge_cost G hloc P hP p k D ω F hFa b z y hbz c hc) (neg_nonpos.mpr ht)
      simpa only [mul_add] using hh
    · rw [deformedConnection,ite_eq_right hz,mul_zero]
      exact deformedConnection_nonneg G P p k t D ω b y
  · rw [ite_eq_right ho,mul_zero]
    exact deformedConnection_nonneg G P p k t D ω b y

end TerminalConnectionComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EndpointSusceptibilityComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedKernel_move_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z y : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card * deformedKernel G P p k t D z y ≤
      deformedKernel G P p k t D b y := by
  have hi := integrable_deformedConnection G P hP p k t ht D z y
  have hIi := hi.indicator (measurableSet_finite_open F)
  have has := finite_open_integral_lower p F (fun ω => deformedConnection G P p k t D ω z y)
    (measurable_deformedConnection G P p k t D z y)
    (fun ω => deformedConnection_nonneg G P p k t D ω z y)
    (fun ω => deformedConnection_le_one G P hP p k t ht D ω z y)
    (fun _ _ hω => deformedConnection_mono G hloc P hP p k t ht (Set.Subset.refl _) hω z y)
  have hb' := integral_mono (hIi.const_mul (Real.exp (-t*((F.card:ℝ)*c))))
    (integrable_deformedConnection G P hP p k t ht D b y)
    (fun ω => deformedConnection_move_lower G hloc P hP p k t ht D ω F hF b z y hb hbz c hc)
  simp only [Set.indicator,Set.mem_ofPred_eq,integral_const_mul] at hb'
  have hh := mul_le_mul_of_nonneg_left has (Real.exp_pos (-t*((F.card:ℝ)*c))).le
  simp only [mul_assoc] at hh ⊢
  exact hh.trans hb'

 
theorem deformedSusceptibility_move_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card * deformedSusceptibility G P p k t D z ≤
      deformedSusceptibility G P p k t D b := by
  simpa only [deformedSusceptibility,tsum_mul_left] using
    ((summable_deformedKernel G hloc hqt P hP p hp k t ht D z).mul_left
      (Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card)).tsum_le_tsum
      (fun y => deformedKernel_move_lower G hloc P hP p k t ht D F hF b z y hb hbz c hc)
      (summable_deformedKernel G hloc hqt P hP p hp k t ht D b)

end EndpointSusceptibilityComparison
end Percolation

end OAI
