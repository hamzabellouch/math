import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.ExteriorMoments

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedBoundaryPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exposedVertexPotential (G : BondGraph V E) (p : unitInterval)
    (x a b : V) (ω : Set E) : ℝ :=
  if Conn G ω x a then freshExteriorMoment G p a b ω else 0

theorem integrable_exposedVertexPotential [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    Integrable (exposedVertexPotential G p x a b) (law p) := by
  have he : exposedVertexPotential G p x a b = {ω | Conn G ω x a}.indicator (freshExteriorMoment G p a b) := by
    funext ω
    simp only [exposedVertexPotential,Set.indicator,Set.mem_ofPred_eq]
  rw [he]
  exact (integrable_freshExteriorMoment G hloc hqt p hp a b).indicator (measurableSet_conn G x a)

theorem integral_exposedVertexPotential_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    (∫ ω, exposedVertexPotential G p x a b ω ∂law p) ≤ distinctClusterMoment G p a b := by
  rw [←show (∫ ω, freshExteriorMoment G p a b ω ∂law p) = distinctClusterMoment G p a b from
    integral_freshExteriorMoment G hloc hqt p hp a b]
  apply integral_mono (integrable_exposedVertexPotential G hloc hqt p hp x a b)
    (integrable_freshExteriorMoment G hloc hqt p hp a b)
  intro ω
  unfold exposedVertexPotential
  split_ifs
  · rfl
  · exact freshExteriorMoment_nonneg G p a b ω

theorem exposedBoundaryPotential_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x v : V) (M : ℕ) (ω : Set E) :
    ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M =
      ∑ a ∈ (finite_reachBall hloc v M).toFinset,
        ∑ b ∈ neighbors G hloc a, exposedVertexPotential G p x a b ω := by
  unfold deletedBoundaryPotential
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Conn G ω x a
  · have hc := cluster_eq_of_conn G ω ha
    have hn : a ∉ (cluster G ω x)ᶜ := by exact not_not.mpr ha
    simp only [ite_eq_left hn,Finset.mul_sum]
    simp only [exposedVertexPotential,ite_eq_left ha,freshExteriorMoment,hc]
  · have hn : ¬a ∉ (cluster G ω x)ᶜ := by exact not_not.mpr ha
    simp only [ite_eq_right hn,mul_zero,exposedVertexPotential,ite_eq_right ha,Finset.sum_const_zero]

 

theorem integral_exposedBoundaryPotential_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x v : V) (M : ℕ) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M) (law p) ∧
    (∫ ω, ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M ∂law p) ≤
      ∑ a ∈ (finite_reachBall hloc v M).toFinset, neighborClusterMoment G hloc p a := by
  simp_rw [exposedBoundaryPotential_eq G hloc p x v M]
  have hi (a : V) := integrable_finsetSum (neighbors G hloc a)
    (fun b _ => integrable_exposedVertexPotential G hloc hqt p hp x a b)
  refine ⟨integrable_finsetSum _ (fun a _ => hi a),?_⟩
  rw [integral_finsetSum _ (fun a _ => hi a)]
  apply Finset.sum_le_sum
  intro a _
  rw [integral_finsetSum _ (fun b _ => integrable_exposedVertexPotential G hloc hqt p hp x a b)]
  exact Finset.sum_le_sum (fun b _ => integral_exposedVertexPotential_le G hloc hqt p hp x a b)

end ExposedBoundaryPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformExposedBoundary
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (M : ℕ) :
    (reachBall G (a x) M).ncard = (reachBall G x M).ncard := by
  have he : reachBall G (a x) M = a '' reachBall G x M := by
    ext y
    constructor
    · intro h
      exact ⟨a.symm y,by simpa only [Equiv.symm_apply_apply] using mem_reachBall_aut G (isAut_symm G hab) h,by simp⟩
    · rintro ⟨z,hz,rfl⟩
      exact mem_reachBall_aut G hab hz
  rw [he,Set.ncard_image_of_injective _ a.injective]

theorem reachBall_card_le_root_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (M : ℕ) (x : V) : (finite_reachBall hloc x M).toFinset.card ≤
      ∑ i, (reachBall G (root i) M).ncard := by
  obtain ⟨i,a,b,hab,hax⟩ := hcover x
  rw [←Set.ncard_eq_toFinset_card (reachBall G x M) (finite_reachBall hloc x M),←hax,reachBall_ncard_covariant G hab]
  exact Finset.single_le_sum (f := fun i => (reachBall G (root i) M).ncard) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem rootNeighborMoment_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) : 0 ≤ rootNeighborMoment G hloc root weight p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (neighborClusterMoment_nonneg G hloc p _))

 

theorem integral_exposedBoundaryPotential_uniform [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x v : V) (M : ℕ) :
    (∫ ω, ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M ∂law p) ≤
      (∑ i, ((reachBall G (root i) M).ncard:ℝ))*c*rootNeighborMoment G hloc root weight p := by
  let B := (finite_reachBall hloc v M).toFinset
  calc
    _ ≤ ∑ a ∈ B, neighborClusterMoment G hloc p a :=
      (integral_exposedBoundaryPotential_le G hloc hqt p hp x v M).2
    _ ≤ ∑ _a ∈ B, c*rootNeighborMoment G hloc root weight p :=
      Finset.sum_le_sum (fun a _ => neighborMoment_le_rootMoment G hloc root weight hw hcover c hc hmin p a)
    _ = (B.card:ℝ)*(c*rootNeighborMoment G hloc root weight p) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hb : (B.card:ℝ) ≤ ∑ i, ((reachBall G (root i) M).ncard:ℝ) := by
        exact_mod_cast reachBall_card_le_root_sum G hloc root hcover M v
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb
        (mul_nonneg hc (rootNeighborMoment_nonneg G hloc root weight hw p))

end UniformExposedBoundary
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctMomentPotential
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem kernel_distinctMoment_integral [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x v : V) :
    (∑' y, q.kernel p v y * distinctClusterMoment G p x y) =
      ∫ ω, (∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) ∂law p := by
  rw [integral_tsum_of_finite_support (law p) (finite_reachBall hloc v M).toFinset _
    (fun y => (integrable_freshExteriorMoment G hloc hqt p hp x y).const_mul (q.kernel p v y))
    (fun ω y hy => by rw [q.kernel_outside_ball_zero p v y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul])]
  apply tsum_congr
  intro y
  rw [integral_const_mul,integral_freshExteriorMoment G hloc hqt p hp]
  rfl

theorem integrable_kernel_freshMoment [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x v : V) :
    Integrable (fun ω => ∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) (law p) := by
  have he (ω) : (∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) =
      ∑ y ∈ (finite_reachBall hloc v M).toFinset, q.kernel p v y * freshExteriorMoment G p x y ω :=
    tsum_eq_sum (fun y hy => by rw [q.kernel_outside_ball_zero p v y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul])
  simp_rw [he]
  exact integrable_finsetSum _ (fun y _ => (integrable_freshExteriorMoment G hloc hqt p hp x y).const_mul _)

 
theorem kernel_distinctMoment_bound [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) (x v : V) :
    (∑' y, q.kernel p v y * distinctClusterMoment G p x y) ≤
      (1+(1-(p:ℝ))/p*M)*distinctClusterMoment G p x v +
        (p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c*rootNeighborMoment G hloc root weight p := by
  let C := 1+(1-(p:ℝ))/p*M
  let R := (p:ℝ)^(-(M:ℤ))
  let b := fun ω : Set E => ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M
  have hi := (integral_exposedBoundaryPotential_le G hloc hqt p hpc x v M).1
  have hpoint (ω : Set E) : (∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) ≤
      C*freshExteriorMoment G p x v ω + R*b ω := by
    have h := mul_le_mul_of_nonneg_left (q.kernel_deleted_potential_bound hqt (cluster G ω x)ᶜ p hp hpc v)
      (Nat.cast_nonneg (cluster G ω x).ncard : (0:ℝ) ≤ _)
    rw [←tsum_mul_left] at h
    calc
      _ = ∑' y, ((cluster G ω x).ncard:ℝ)*(q.kernel p v y * inducedSusceptibility G (cluster G ω x)ᶜ p y) := by
        apply tsum_congr
        intro y
        simp only [freshExteriorMoment]
        ring
      _ ≤ _ := h
      _ = _ := by dsimp [C,R,b,freshExteriorMoment]; ring
  rw [q.kernel_distinctMoment_integral hqt p hpc x v]
  calc
    _ ≤ ∫ ω, C*freshExteriorMoment G p x v ω + R*b ω ∂law p :=
      integral_mono (q.integrable_kernel_freshMoment hqt p hpc x v)
        (((integrable_freshExteriorMoment G hloc hqt p hpc x v).const_mul C).add (hi.const_mul R)) hpoint
    _ = C*distinctClusterMoment G p x v + R*(∫ ω, b ω ∂law p) := by
      rw [integral_add ((integrable_freshExteriorMoment G hloc hqt p hpc x v).const_mul C) (hi.const_mul R),
        integral_const_mul,integral_const_mul,integral_freshExteriorMoment G hloc hqt p hpc]
      rfl
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (integral_exposedBoundaryPotential_uniform G hloc hqt root weight hw hcover c hc hmin p hpc x v M)
        (zpow_nonneg p.2.1 (-(M:ℤ)))
      dsimp [C,R,b] at *
      nlinarith

end LocalEndpointRule
end DistinctMomentPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePositiveOperatorPowers
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_positive_product_support (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hb : ∀ x, (Function.support (fun y => (matrixCoeff B x y).re)).Finite) (x : V) :
    (Function.support (fun y => (matrixCoeff (A*B) x y).re)).Finite := by
  let S := (ha x).toFinset
  let T := S.biUnion (fun z => (hb z).toFinset)
  apply T.finite_toSet.subset
  intro y hy
  by_contra hn
  apply hy
  change (matrixCoeff (A*B) x y).re = 0
  rw [←(hA.mul_hasSum B x y).tsum_eq]
  rw [←tsum_zero]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ S
  · have hzy : (matrixCoeff B z y).re = 0 := by
      by_contra hh
      apply hn
      exact Finset.mem_biUnion.mpr ⟨z,hz,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hh⟩
    rw [hzy,mul_zero]
  · have hzx : (matrixCoeff A x z).re = 0 := by
      simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
    rw [hzx,zero_mul]

theorem finite_positive_product_action (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hb : ∀ x, (Function.support (fun y => (matrixCoeff B x y).re)).Finite)
    (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (A*B) x y).re*f y) =
      ∑' z, (matrixCoeff A x z).re*∑' y, (matrixCoeff B z y).re*f y := by
  let K := fun x y => (matrixCoeff A x y).re
  let J := fun x y => (matrixCoeff B x y).re
  let S := (ha x).toFinset
  have hz (z : V) (hz : z ∉ S) : K x z = 0 := by
    simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  have he (y : V) : (matrixCoeff (A*B) x y).re*f y = ∑ z ∈ S, K x z*(J z y*f y) := by
    rw [←(hA.mul_hasSum B x y).tsum_eq,tsum_eq_sum (s := S)
      (fun z h => by change K x z*J z y = 0; rw [hz z h,zero_mul]),Finset.sum_mul]
    exact Finset.sum_congr rfl (fun z _ => mul_assoc _ _ _)
  have hs := hasSum_sum (s := S) (fun z _ =>
    (finiteKernel_summable_mul J hb z f).hasSum.mul_left (K x z))
  have hr : (∑' z, K x z*∑' y, J z y*f y) = ∑ z ∈ S, K x z*∑' y, J z y*f y :=
    tsum_eq_sum (fun z h => by rw [hz z h,zero_mul])
  simpa only [←he,←hr] using hs.tsum_eq

theorem finite_positive_pow_support (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (j : ℕ) (x : V) : (Function.support (fun y => (matrixCoeff (A^j) x y).re)).Finite := by
  induction j generalizing x with
  | zero =>
      apply (Set.finite_singleton x).subset
      intro y hy
      by_contra hn
      apply hy
      have he : x ≠ y := fun h => hn (by simp only [Set.mem_singleton_iff]; exact h.symm)
      simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right he,Complex.zero_re]
  | succ j ih =>
      rw [pow_succ']
      exact finite_positive_product_support A (A^j) hA ha ih x

theorem positive_identity_action (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (1 : Hilbert V →L[ℂ] Hilbert V) x y).re*f y) = f x := by
  rw [tsum_eq_single x (fun y hy => by
    simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right (Ne.symm hy),Complex.zero_re,zero_mul])]
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_true,Complex.one_re,one_mul]

end FinitePositiveOperatorPowers
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePotentialIteration
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realAction (A : Hilbert V →L[ℂ] Hilbert V) (f : V → ℝ) (x : V) : ℝ :=
  ∑' y, (matrixCoeff A x y).re*f y

theorem realAction_mono (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f g : V → ℝ) (hfg : ∀ x, f x ≤ g x) (x : V) : realAction A f x ≤ realAction A g x := by
  exact (finiteKernel_summable_mul _ ha x f).tsum_le_tsum
    (fun y => mul_le_mul_of_nonneg_left (hfg y) (hA x y).2) (finiteKernel_summable_mul _ ha x g)

theorem realAction_affine (A : Hilbert V →L[ℂ] Hilbert V)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f : V → ℝ) (a b : ℝ) (x : V) :
    realAction A (fun y => a*f y+b) x = a*realAction A f x + b*realAction A (fun _ => 1) x := by
  unfold realAction
  simp_rw [mul_add]
  rw [Summable.tsum_add]
  · have he (y : V) : (matrixCoeff A x y).re*(a*f y) = a*((matrixCoeff A x y).re*f y) := by ring
    simp_rw [he]
    simp only [tsum_mul_left,tsum_mul_right,mul_one]
    ring
  · exact finiteKernel_summable_mul _ ha x (fun y => a*f y)
  · exact finiteKernel_summable_mul _ ha x (fun _ => b)

theorem realAction_pow_succ (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (j : ℕ) (f : V → ℝ) (x : V) :
    realAction (A^(j+1)) f x = realAction A (realAction (A^j) f) x := by
  rw [pow_succ']
  exact finite_positive_product_action A (A^j) hA ha (finite_positive_pow_support A hA ha j) f x

 

theorem realAction_pow_potential_bound (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (f : V → ℝ) (Z B : ℝ) (hZ : 2 ≤ Z) (hB : 0 ≤ B)
    (hf : ∀ x, realAction A f x ≤ Z*f x+B) (j : ℕ) (x : V) :
    realAction (A^j) f x ≤ Z^j*f x + B*(Z^j-1) := by
  have hz : 0 ≤ Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  induction j generalizing x with
  | zero =>
      simp only [pow_zero,realAction,positive_identity_action,one_mul,sub_self,mul_zero,add_zero,le_refl]
  | succ j ih =>
      rw [realAction_pow_succ A hA ha]
      calc
        _ ≤ realAction A (fun y => Z^j*f y+B*(Z^j-1)) x := realAction_mono A hA ha _ _ ih x
        _ = Z^j*realAction A f x + (B*(Z^j-1))*realAction A (fun _ => 1) x := realAction_affine A ha f _ _ x
        _ ≤ Z^j*(Z*f x+B) + B*(Z^j-1) := add_le_add
          (mul_le_mul_of_nonneg_left (hf x) (pow_nonneg hz _))
          (by
            simpa only [mul_one] using (mul_le_mul_of_nonneg_left (hrow x)
              (mul_nonneg hB (sub_nonneg.mpr (one_le_pow₀ hz1)))))
        _ ≤ Z^(j+1)*f x+B*(Z^(j+1)-1) := by
          have hh := mul_nonneg (mul_nonneg hB (pow_nonneg hz j)) (show 0 ≤ Z-2 by linarith)
          rw [pow_succ]
          nlinarith only [hh]

theorem realAction_pow_potential_at_zero (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (f : V → ℝ) (Z B : ℝ) (hZ : 2 ≤ Z) (hB : 0 ≤ B)
    (hf : ∀ x, realAction A f x ≤ Z*f x+B) (j : ℕ) (x : V) (hx : f x = 0) :
    realAction (A^j) f x ≤ B*Z^j := by
  have h := realAction_pow_potential_bound A hA ha hrow f Z B hZ hB hf j x
  rw [hx,mul_zero,zero_add] at h
  nlinarith

end PositivePotentialIteration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedPositiveOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem normalized_operator_positive (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) : PositiveRealMatrix A := by
  intro x y
  rw [hA]
  exact ⟨rfl,mul_nonneg (inv_nonneg.mpr (q.successProbability_nonneg p o)) (q.kernel_nonneg p x y)⟩

theorem normalized_operator_finite (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (x : V) :
    (Function.support (fun y => (matrixCoeff A x y).re)).Finite := by
  apply (finite_reachBall hloc x M).subset
  intro y hy
  by_contra hn
  apply hy
  change (matrixCoeff A x y).re = 0
  simp only [hA,normalizedKernel,q.kernel_outside_ball_zero p x y hn,mul_zero,Complex.ofReal_zero,Complex.zero_re]

theorem normalized_operator_action (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (f : V → ℝ) (x : V) :
    realAction A f x = (q.successProbability p o)⁻¹ * (∑' y, q.kernel p x y*f y) := by
  simp only [realAction,hA,Complex.ofReal_re,normalizedKernel,mul_assoc,tsum_mul_left]

theorem normalized_operator_row_le (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (hu : 0 < q.successProbability p o) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (x : V) :
    realAction A (fun _ => 1) x ≤ 1 := by
  rw [q.normalized_operator_action o p A hA]
  simp only [mul_one]
  calc
    _ ≤ (q.successProbability p o)⁻¹ * q.successProbability p o :=
      mul_le_mul_of_nonneg_left (q.kernel_row_le_success o p x) (inv_nonneg.mpr hu.le)
    _ = 1 := inv_mul_cancel₀ hu.ne'

theorem normalized_operator_row_eq (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (hu : 0 < q.successProbability p o) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (x : V)
    (hx : x ∈ vertexOrbit G o) : realAction A (fun _ => 1) x = 1 := by
  rw [q.normalized_operator_action o p A hA]
  simp only [mul_one]
  change (q.successProbability p o)⁻¹ * q.successProbability p x = 1
  rw [q.successProbability_orbit p o x hx,inv_mul_cancel₀ hu.ne']

theorem normalized_operator_invariant (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) :
    KernelInvariant (vertexAut G) A := by
  rintro a ⟨b,hab⟩ x y
  simp only [hA,normalizedKernel,q.kernel_covariant p a b hab]

theorem normalized_operator_end_support (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ))
    (x y : V) (hy : y ∉ vertexOrbit G o) : (matrixCoeff A x y).re = 0 := by
  simp only [hA,normalizedKernel,q.kernel_zero_of_end_not_mem p x y hy,mul_zero,Complex.ofReal_zero,Complex.zero_re]

end LocalEndpointRule
end NormalizedPositiveOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UpperDistinctMomentIteration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinctClusterMoment_self (G : BondGraph V E) (p : unitInterval) (x : V) :
    distinctClusterMoment G p x x = 0 := by
  have hs (ω : Set E) : Conn G ω x x := .refl
  simp only [distinctClusterMoment,hs,not_true_eq_false,ite_false,integral_zero]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem normalized_power_distinctMoment_upper [Countable V] [Countable E] [Nonempty V]
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G)
    (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ))
    (Z : ℝ) (hZ : 2 ≤ Z)
    (hscale : (q.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*M) ≤ Z)
    (j : ℕ) (x : V) :
    realAction (A^j) (distinctClusterMoment G p x) x ≤
      ((q.successProbability p o)⁻¹*(p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c)*
        rootNeighborMoment G hloc root weight p * Z^j := by
  let B := ((q.successProbability p o)⁻¹*(p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c)*
    rootNeighborMoment G hloc root weight p
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hu.le) (zpow_nonneg p.2.1 _))
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))) hc)
      (rootNeighborMoment_nonneg G hloc root weight hw p)
  have hf (v : V) : realAction A (distinctClusterMoment G p x) v ≤ Z*distinctClusterMoment G p x v+B := by
    rw [q.normalized_operator_action o p A hA]
    calc
      _ ≤ (q.successProbability p o)⁻¹ *
          ((1+(1-(p:ℝ))/p*M)*distinctClusterMoment G p x v+
            (p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c*rootNeighborMoment G hloc root weight p) :=
        mul_le_mul_of_nonneg_left
          (q.kernel_distinctMoment_bound hqt root weight hw hcover c hc hmin p hp hpc x v) (inv_nonneg.mpr hu.le)
      _ = ((q.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*M))*distinctClusterMoment G p x v+B := by dsimp [B]; ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hscale (distinctClusterMoment_nonneg G p x v)
        linarith
  exact realAction_pow_potential_at_zero A (q.normalized_operator_positive o p A hA)
    (q.normalized_operator_finite o p A hA) (q.normalized_operator_row_le o p hu A hA)
    (distinctClusterMoment G p x) Z B hZ hB hf j x (distinctClusterMoment_self G p x)

end LocalEndpointRule
end UpperDistinctMomentIteration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePowerStochasticity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem realAction_pow_row_le (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1) (j : ℕ) (x : V) :
    realAction (A^j) (fun _ => 1) x ≤ 1 := by
  induction j generalizing x with
  | zero => rw [pow_zero]; exact (positive_identity_action (fun _ => 1) x).le
  | succ j ih =>
      rw [realAction_pow_succ A hA ha]
      exact (realAction_mono A hA ha _ (fun _ => 1) ih x).trans (hrow x)

theorem positive_pow_end_support (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (O : Set V) (hO : ∀ x y, y ∉ O → (matrixCoeff A x y).re = 0)
    (j : ℕ) (x y : V) (hx : x ∈ O) (hy : y ∉ O) : (matrixCoeff (A^j) x y).re = 0 := by
  cases j with
  | zero =>
      have hxy : x ≠ y := fun h => hy (h ▸ hx)
      simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right hxy,Complex.zero_re]
  | succ j =>
      rw [pow_succ,←((hA.pow j).mul_hasSum A x y).tsum_eq]
      simp only [hO _ y hy,mul_zero,tsum_zero]

theorem realAction_pow_row_eq_on (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (O : Set V) (hO : ∀ x y, y ∉ O → (matrixCoeff A x y).re = 0)
    (hrow : ∀ x ∈ O, realAction A (fun _ => 1) x = 1)
    (j : ℕ) (x : V) (hx : x ∈ O) : realAction (A^j) (fun _ => 1) x = 1 := by
  induction j generalizing x with
  | zero => rw [pow_zero]; exact positive_identity_action (fun _ => 1) x
  | succ j ih =>
      rw [realAction_pow_succ A hA ha]
      calc
        _ = realAction A (fun _ => 1) x := by
          apply tsum_congr
          intro y
          by_cases hy : y ∈ O
          · rw [ih y hy]
          · rw [hO x y hy,zero_mul,zero_mul]
        _ = 1 := hrow x hx

end PositivePowerStochasticity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectedMomentLoss
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def connectedClusterMoment (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, (if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) ∂law p

theorem integrable_connected_cluster_square [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) (law p) := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have he : (fun ω : Set E => if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) =
      {ω | Conn G ω x y}.indicator (fun ω => ((cluster G ω x).ncard:ℝ)^2) := by
    funext ω
    simp only [Set.indicator,Set.mem_ofPred_eq]
  rw [he]
  exact (hs x).1.indicator (measurableSet_conn G x y)

theorem distinct_add_connected_cluster_moment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    distinctClusterMoment G p x y + connectedClusterMoment G p x y =
      ∫ ω, ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) ∂law p := by
  rw [distinctClusterMoment,connectedClusterMoment,
    ←integral_add (integrable_distinct_cluster_product G hloc hqt p hp x y)
      (integrable_connected_cluster_square G hloc hqt p hp x y)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases h : Conn G ω x y
    · simp only [h,not_true_eq_false,ite_false,ite_true,zero_add,cluster_eq_of_conn G ω h,pow_two]
    · simp only [h,not_false_eq_true,ite_true,ite_false,add_zero])

theorem distinctClusterMoment_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    susceptibility G p x * susceptibility G p y - connectedClusterMoment G p x y ≤
      distinctClusterMoment G p x y := by
  have h := (subcritical_cluster_association G hloc hqt p hp x y).2
  rw [←distinct_add_connected_cluster_moment G hloc hqt p hp] at h
  linarith

 
theorem realAction_connectedMoment_eq_diagonalLoss [Countable V] [Countable E]
    (G : BondGraph V E) (o : V) (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (x : V) (hend : ∀ y, y ∉ vertexOrbit G o → (matrixCoeff A x y).re = 0)
    (p : unitInterval) (hs : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p)) :
    realAction A (connectedClusterMoment G p x) x =
      ∫ ω, diagonalLossMass G o (fun a b => (matrixCoeff A a b).re) ω x ∂law p := by
  have hr (z : V) (S : Finset V) : (∑ y ∈ S, (matrixCoeff A z y).re) ≤ 1 := by
    have hsrow : Summable (fun y => (matrixCoeff A z y).re) := by
      simpa only [mul_one] using finiteKernel_summable_mul (fun a b => (matrixCoeff A a b).re) ha z (fun _ => 1)
    exact (hsrow.sum_le_tsum S (fun y _ => (hA z y).2)).trans (by simpa only [realAction,mul_one] using hrow z)
  rw [integral_diagonalLoss_eq_series G o _ (fun a b => (hA a b).2) 1 hr x p hs]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ vertexOrbit G o
  · rw [ite_eq_left hy]
    rfl
  · simp only [ite_eq_right hy,hend y hy,zero_mul]

end ConnectedMomentLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LowerDistinctMomentOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem realAction_distinctMoment_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b : ℝ) (hb : 0 ≤ b)
    (hχ : ∀ x, b ≤ susceptibility G p x)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hinv : KernelInvariant (vertexAut G) A)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (heq : realAction A (fun _ => 1) (root i₀) = 1)
    (hend : ∀ y, y ∉ vertexOrbit G (root i₀) → (matrixCoeff A (root i₀) y).re = 0) :
    b^2-‖A‖*(c*rootSusceptibility G root weight p)^3 ≤
      realAction A (distinctClusterMoment G p (root i₀)) (root i₀) := by
  let x := root i₀
  let f := connectedClusterMoment G p x
  have hr (z : V) (S : Finset V) : (∑ y ∈ S, (matrixCoeff A z y).re) ≤ 1 := by
    have hsrow : Summable (fun y => (matrixCoeff A z y).re) := by
      simpa only [mul_one] using finiteKernel_summable_mul (fun a b => (matrixCoeff A a b).re) ha z (fun _ => 1)
    exact (hsrow.sum_le_tsum S (fun y _ => (hA z y).2)).trans (by simpa only [realAction,mul_one] using hrow z)
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have hf : realAction A f x ≤ ‖A‖*(c*rootSusceptibility G root weight p)^3 := by
    rw [realAction_connectedMoment_eq_diagonalLoss G (root i₀) A hA ha hrow x hend p (hs x).1]
    exact diagonalLoss_le_rootSusceptibility_cube G hloc hqt root weight Γ htr hΓ hw i₀ hw₀ hcover c hc hmin p hp
      (fun a b => (matrixCoeff A a b).re) (fun a b => (hA a b).2)
      (fun a b hab z y => congrArg Complex.re (hinv a ⟨b,hab⟩ z y)) 1 hr A (hA.real)
  have hpnt (y : V) : (-1)*f y+b^2 ≤ distinctClusterMoment G p x y := by
    have h := distinctClusterMoment_lower G hloc hqt p hp x y
    have hprod : b*b ≤ susceptibility G p x * susceptibility G p y :=
      mul_le_mul (hχ x) (hχ y) hb (susceptibility_nonneg G p x)
    dsimp [f]
    nlinarith only [h,hprod]
  have hi := realAction_mono A hA ha (fun y => (-1)*f y+b^2)
    (distinctClusterMoment G p x) hpnt x
  rw [realAction_affine A ha f (-1) (b^2) x,heq] at hi
  nlinarith only [hi,hf]

end LowerDistinctMomentOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctMomentSandwich
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem normalized_power_moment_sandwich [Countable V] [Countable E] [Nonempty V]
    (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G)
    (hu : 0 < q.successProbability p (root i₀))
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ))
    (a : ℝ) (ha : 0 ≤ a) (hχ : ∀ x, a*rootSusceptibility G root weight p ≤ susceptibility G p x)
    (Z : ℝ) (hZ : 2 ≤ Z)
    (hscale : (q.successProbability p (root i₀))⁻¹*(1+(1-(p:ℝ))/p*M) ≤ Z) (j : ℕ) :
    (a*rootSusceptibility G root weight p)^2 - ‖A‖^j*(c*rootSusceptibility G root weight p)^3 ≤
      ((q.successProbability p (root i₀))⁻¹*(p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c)*
        rootNeighborMoment G hloc root weight p * Z^j := by
  have hpos := q.normalized_operator_positive (root i₀) p A hA
  have hfin := q.normalized_operator_finite (root i₀) p A hA
  have hrow := q.normalized_operator_row_le (root i₀) p hu A hA
  have hend := q.normalized_operator_end_support (root i₀) p A hA
  have hx : root i₀ ∈ vertexOrbit G (root i₀) := ⟨Equiv.refl V,Equiv.refl E,(fun _ => by simp),rfl⟩
  have hlo := realAction_distinctMoment_lower G hloc hqt root weight Γ htr hΓ hw i₀ hw₀ hcover c hc hmin p hpc
    (a*rootSusceptibility G root weight p) (mul_nonneg ha (rootSusceptibility_nonneg G root weight hw p)) hχ
    (A^j) (hpos.pow j) (finite_positive_pow_support A hpos hfin j)
    ((q.normalized_operator_invariant (root i₀) p A hA).pow j)
    (realAction_pow_row_le A hpos hfin hrow j)
    (realAction_pow_row_eq_on A hpos hfin _ hend
      (q.normalized_operator_row_eq (root i₀) p hu A hA) j (root i₀) hx)
    (positive_pow_end_support A hpos _ hend j (root i₀) · hx)
  have hhi := q.normalized_power_distinctMoment_upper (root i₀) hqt root weight hw hcover c hc hmin p hp hpc hu A hA Z hZ hscale j (root i₀)
  have hpow : ‖A^j‖ ≤ ‖A‖^j := by
    cases j with
    | zero =>
      simp only [pow_zero]
      have he : (1 : Hilbert V →L[ℂ] Hilbert V) = ContinuousLinearMap.id ℂ (Hilbert V) := by ext x; rfl
      rw [he]
      exact ContinuousLinearMap.norm_id_le
    | succ j => exact norm_pow_le' A (Nat.succ_pos j)
  have hn := mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (mul_nonneg hc (rootSusceptibility_nonneg G root weight hw p)) 3)
  linarith

end LocalEndpointRule
end DistinctMomentSandwich
end Percolation

 
namespace Percolation
section LogarithmicPowerChoice

 

theorem exists_logarithmic_power (r h Z T : ℝ) (hr : 0 ≤ r) (hh : 0 < h)
    (hrh : r ≤ Real.exp (-h)) (hZ : 1 ≤ Z) (hT : 1 ≤ T) :
    ∃ j : ℕ, r^j ≤ T⁻¹ ∧ Z^j ≤ Z*T^(Real.log Z/h) := by
  let t := Real.log T/h
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hT) hh.le
  let j := Nat.ceil t
  have hlo : t ≤ (j:ℝ) := Nat.le_ceil t
  have hhi : (j:ℝ) ≤ t+1 := (Nat.ceil_lt_add_one ht).le
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  refine ⟨j,?_,?_⟩
  · calc
      r^j ≤ (Real.exp (-h))^j := pow_le_pow_left₀ hr hrh j
      _ = Real.exp ((j:ℝ)*(-h)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-Real.log T) := by
        apply Real.exp_le_exp.mpr
        have hl : Real.log T ≤ (j:ℝ)*h := (div_le_iff₀ hh).mp hlo
        nlinarith
      _ = T⁻¹ := by rw [Real.exp_neg,Real.exp_log hTp]
  · calc
      Z^j = Real.exp ((j:ℝ)*Real.log Z) := by rw [Real.exp_nat_mul,Real.exp_log hZp]
      _ ≤ Real.exp ((t+1)*Real.log Z) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hlogZ)
      _ = Z*T^(Real.log Z/h) := by
        rw [Real.rpow_def_of_pos hTp,←Real.exp_log hZp,←Real.exp_add]
        simp only [Real.log_exp]
        congr 1
        dsimp [t]
        ring

 

theorem moment_sandwich_power_law (a c C Z h r χ N : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) (hZ : 1 ≤ Z) (hh : 0 < h)
    (hr : 0 ≤ r) (hrh : r ≤ Real.exp (-h)) (hχ : 1 ≤ χ) (hN : 0 ≤ N)
    (hs : ∀ j : ℕ, (a*χ)^2-r^j*(c*χ)^3 ≤ C*N*Z^j) :
    let T := 1+2*c^3/a^2
    a^2/(2*C*Z*T^(Real.log Z/h))*χ^(2-Real.log Z/h) ≤ N := by
  let T := 1+2*c^3/a^2
  have hap : 0 < a^2 := sq_pos_of_pos ha
  have hT : 1 ≤ T := by
    have hn : 0 ≤ 2*c^3/a^2 := by positivity
    dsimp [T]
    linarith
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hχp : 0 < χ := zero_lt_one.trans_le hχ
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hTx : 1 ≤ T*χ := by nlinarith
  obtain ⟨j,hrj,hZj⟩ := exists_logarithmic_power r h Z (T*χ) hr hh hrh hZ hTx
  have hbudget : 2*c^3 ≤ a^2*T := by dsimp [T]; field_simp; nlinarith
  have hsmall : r^j*(c*χ)^3 ≤ a^2/2*χ^2 := by
    calc
      _ ≤ (T*χ)⁻¹*(c*χ)^3 := mul_le_mul_of_nonneg_right hrj (pow_nonneg (mul_nonneg hc hχp.le) _)
      _ = c^3/T*χ^2 := by field_simp
      _ ≤ a^2/2*χ^2 := mul_le_mul_of_nonneg_right ((div_le_iff₀ hTp).mpr (by nlinarith [hbudget])) (sq_nonneg χ)
  have hlarge : a^2/2*χ^2 ≤ C*N*(Z*(T*χ)^(Real.log Z/h)) := by
    have hs' := hs j
    have hprod := mul_le_mul_of_nonneg_left hZj (mul_nonneg hC.le hN)
    nlinarith only [hsmall,hs',hprod]
  have hpow : 0 < χ^(Real.log Z/h) := Real.rpow_pos_of_pos hχp _
  have hTpow : 0 < T^(Real.log Z/h) := Real.rpow_pos_of_pos hTp _
  have he : C*N*(Z*(T*χ)^(Real.log Z/h)) =
      (C*Z*T^(Real.log Z/h))*N*χ^(Real.log Z/h) := by
    rw [Real.mul_rpow hTp.le hχp.le]
    ring
  rw [he] at hlarge
  have hden : 0 < 2*C*Z*T^(Real.log Z/h) := by positivity
  change a^2/(2*C*Z*T^(Real.log Z/h))*χ^(2-Real.log Z/h) ≤ N
  rw [Real.rpow_sub hχp,Real.rpow_two]
  calc
    _ = (a^2*χ^2)/(2*C*Z*T^(Real.log Z/h)*χ^(Real.log Z/h)) := by
      rw [div_mul_div_comm]
    _ ≤ N := (div_le_iff₀ (mul_pos hden hpow)).mpr (by nlinarith only [hlarge])

end LogarithmicPowerChoice
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section ProfileContinuity
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

theorem exp_neg_H (q : EndpointProfile G hloc p₀ o s) : Real.exp (-q.H) = ‖q.op‖ := by
  rw [H,one_div,Real.log_inv,neg_neg,Real.exp_log q.norm_pos]

 

theorem exists_nearby_operators {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : EndpointProfile G hloc p₀ (root i₀) s) (hp₀ : 0 < (p₀:ℝ)) :
    ∃ A : unitInterval → (Hilbert V →L[ℂ] Hilbert V),
      (∀ p x y, matrixCoeff (A p) x y = (q.rule.normalizedKernel (root i₀) p x y : ℂ)) ∧
      ∀ᶠ p in nhds p₀, q.rule.successProbability p₀ (root i₀)/2 ≤ q.rule.successProbability p (root i₀) ∧
        ‖A p‖ ≤ Real.exp (-(q.H-1)) ∧ (p₀:ℝ)/2 ≤ (p:ℝ) := by
  obtain ⟨A,_,hA,hcont⟩ := q.rule.exists_continuous_normalized_operators root weight Γ htr hΓ hw i₀ hw₀
  have he : A p₀ = q.op := kernel_extension_unique (hA p₀) q.coeff
  have hnorm : ContinuousAt (fun p => ‖A p‖) p₀ := (hcont p₀ q.success_pos.ne').norm
  have hb : ‖A p₀‖ < Real.exp (-(q.H-1)) := by
    rw [he,←q.exp_neg_H]
    exact Real.exp_lt_exp.mpr (by linarith)
  have ha := hnorm.eventually_lt continuousAt_const hb
  have hu : ∀ᶠ p in nhds p₀, q.rule.successProbability p₀ (root i₀)/2 < q.rule.successProbability p (root i₀) :=
    continuousAt_const.eventually_lt (q.rule.continuous_successProbability (root i₀)).continuousAt (by linarith [q.success_pos])
  have hp : ∀ᶠ p : unitInterval in nhds p₀, (p₀:ℝ)/2 < (p:ℝ) :=
    continuousAt_const.eventually_lt continuous_subtype_val.continuousAt (by linarith)
  refine ⟨A,hA,?_⟩
  filter_upwards [ha,hu,hp] with p ha hu hp
  exact ⟨hu.le,ha.le,hp.le⟩

end EndpointProfile
end ProfileContinuity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section MapScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

noncomputable def potentialScale (q : EndpointProfile G hloc p₀ o s) (p : unitInterval) : ℝ :=
  (q.rule.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*q.cap)

noncomputable def geometricScale (q : EndpointProfile G hloc p₀ o s) : ℝ := 2*q.potentialScale p₀

theorem potentialScale_pos (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    0 < q.potentialScale p₀ := by
  exact mul_pos (inv_pos.mpr q.success_pos) (by
    have hn : 0 ≤ (1-(p₀:ℝ))/p₀*q.cap := mul_nonneg (div_nonneg (sub_nonneg.mpr p₀.2.2) hp₀.le) (Nat.cast_nonneg _)
    linarith)

theorem geometricScale_two_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    2 ≤ q.geometricScale := by
  have hu : 1 ≤ (q.rule.successProbability p₀ o)⁻¹ :=
    (one_le_inv₀ q.success_pos).mpr (q.rule.successProbability_le_one p₀ o)
  have hb : 0 ≤ (1-(p₀:ℝ))/p₀*q.cap :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr p₀.2.2) hp₀.le) (Nat.cast_nonneg _)
  dsimp [geometricScale,potentialScale]
  nlinarith

theorem log_geometricScale_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ))
    (hM : 1 ≤ q.cap) :
    Real.log q.geometricScale ≤ q.U+q.m+Real.log (2*(1+1/(p₀:ℝ))) := by
  have hM' : (1:ℝ) ≤ q.cap := by exact_mod_cast hM
  have hMp : (0:ℝ) < q.cap := zero_lt_one.trans_le hM'
  have hb : 1+(1-(p₀:ℝ))/p₀*q.cap ≤ (1+1/(p₀:ℝ))*q.cap := by
    apply (mul_le_mul_iff_of_pos_right hp₀).mp
    field_simp
    nlinarith
  have Hz : q.geometricScale ≤ (1/q.rule.successProbability p₀ o)*(q.cap:ℝ)*(2*(1+1/(p₀:ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (inv_nonneg.mpr q.success_pos.le))
    simpa only [geometricScale,potentialScale,one_div,mul_assoc,mul_comm,mul_left_comm] using h
  have hc : 0 < 2*(1+1/(p₀:ℝ)) := by positivity
  have h := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (q.geometricScale_two_le hp₀)) Hz
  rw [Real.log_mul (mul_ne_zero (one_div_ne_zero q.success_pos.ne') hMp.ne') hc.ne',
    Real.log_mul (one_div_ne_zero q.success_pos.ne') hMp.ne'] at h
  exact h

theorem eventually_potentialScale_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    ∀ᶠ p in nhds p₀, q.potentialScale p ≤ q.geometricScale := by
  have hu := (q.rule.continuous_successProbability o).continuousAt.inv₀ q.success_pos.ne'
  have hv : ContinuousAt (fun p : unitInterval => ((1-(p:ℝ))/p)) p₀ :=
    (continuousAt_const.sub continuous_subtype_val.continuousAt).div continuous_subtype_val.continuousAt hp₀.ne'
  have he : ContinuousAt q.potentialScale p₀ := hu.mul (continuousAt_const.add (hv.mul continuousAt_const))
  have hlt : q.potentialScale p₀ < q.geometricScale := by
    dsimp only [geometricScale]
    linarith [q.potentialScale_pos hp₀]
  filter_upwards [he.eventually_lt continuousAt_const hlt] with p hp
  exact hp.le

end EndpointProfile
end MapScaleBudget
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section ProfileNeighborMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

 

theorem eventually_neighborMoment_lower [Countable V] [Countable E] [Nonempty V]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (q : EndpointProfile G hloc p₀ (root i₀) s) (hp₀ : 0 < (p₀:ℝ)) (hH : 1 < q.H) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
      b*(rootSusceptibility G root weight p)^(2-Real.log q.geometricScale/(q.H-1)) ≤
        rootNeighborMoment G hloc root weight p := by
  obtain ⟨a,ha,hχ⟩ := exists_rootSusceptibility_lower G hconn hloc hqt root weight hw hw1 hcover
    ((p₀:ℝ)/2) (by linarith)
  obtain ⟨A,hA,hnear⟩ := q.exists_nearby_operators root weight Γ htr hΓ hw i₀ hw₀ hp₀
  let B : unitInterval → ℝ := fun p =>
    (q.rule.successProbability p (root i₀))⁻¹*(p:ℝ)^(-(q.cap:ℤ))*(∑ i, ((reachBall G (root i) q.cap).ncard:ℝ))*c
  have hB (p : unitInterval) : 0 ≤ B p := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (q.rule.successProbability_nonneg p _))
      (zpow_nonneg p.2.1 _)) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))) hc
  have hBc : ContinuousAt B p₀ := by
    exact ((((q.rule.continuous_successProbability (root i₀)).continuousAt.inv₀ q.success_pos.ne').mul
      (continuous_subtype_val.continuousAt.zpow₀ (-(q.cap:ℤ)) (Or.inl hp₀.ne'))).mul continuousAt_const).mul continuousAt_const
  let C := B p₀+1
  have hC : 0 < C := by dsimp [C]; linarith [hB p₀]
  have hCB : ∀ᶠ p in nhds p₀, B p ≤ C := by
    filter_upwards [hBc.eventually_lt continuousAt_const (show B p₀ < C by dsimp [C]; linarith)] with p hp
    exact hp.le
  let Z := q.geometricScale
  let h := q.H-1
  let T := 1+2*c^3/a^2
  let b := a^2/(2*C*Z*T^(Real.log Z/h))
  have hz : 2 ≤ Z := q.geometricScale_two_le hp₀
  have ht : 0 < T := by
    have hh : 0 ≤ 2*c^3/a^2 := by positivity
    dsimp [T]
    linarith
  have hb : 0 < b := div_pos (sq_pos_of_pos ha) (by
    have hp := Real.rpow_pos_of_pos ht (Real.log Z/h)
    have hZp : 0 < Z := by linarith
    positivity)
  refine ⟨b,hb,?_⟩
  filter_upwards [hnear,hCB,q.eventually_potentialScale_le hp₀] with p hnear hCB hscale
  intro hpc
  obtain ⟨hu,hAn,hpp⟩ := hnear
  have hp : 0 < (p:ℝ) := lt_of_lt_of_le (by linarith : 0 < (p₀:ℝ)/2) hpp
  have hup : 0 < q.rule.successProbability p (root i₀) :=
    lt_of_lt_of_le (by linarith [q.success_pos]) hu
  have hχ1 : 1 ≤ rootSusceptibility G root weight p := by
    calc
      1 = ∑ i, weight i*1 := by simp only [mul_one,hw1]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (susceptibility_one_le G hloc hqt p hpc (root i)) (hw i))
  apply moment_sandwich_power_law a c C Z h ‖A p‖ (rootSusceptibility G root weight p)
    (rootNeighborMoment G hloc root weight p) ha hc hC (by linarith) (by dsimp [h]; linarith)
    (norm_nonneg _) hAn hχ1 (rootNeighborMoment_nonneg G hloc root weight hw p)
  intro j
  have hs := q.rule.normalized_power_moment_sandwich hqt root weight Γ htr hΓ hw i₀ hw₀ hcover c hc hmin p hp hpc hup
    (A p) (hA p) a ha.le (hχ p hpp hpc) Z hz hscale j
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCB (rootNeighborMoment_nonneg G hloc root weight hw p)) (pow_nonneg (by linarith) j))

end EndpointProfile
end ProfileNeighborMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EfficientProfileMomentConsequence
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem neighborMoment_growth_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (p₀ : unitInterval) (hp₀ : 0 < (p₀:ℝ)) (hp₁ : (p₀:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law p₀, (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p₀)) :
    ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
      b*(rootSusceptibility G root weight p)^(2-γ) ≤ rootNeighborMoment G hloc root weight p := by
  obtain ⟨i,heff⟩ := efficient_endpoint_profiles_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 p₀ hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  intro γ hγ
  let C := Real.log (2*(1+1/(p₀:ℝ)))
  have hC : 0 ≤ C := Real.log_nonneg (by
    have hinv : 0 ≤ 1/(p₀:ℝ) := (one_div_pos.mpr hp₀).le
    nlinarith)
  obtain ⟨q,hM,hH,hR,hcost⟩ := heff (γ/4) (by linarith) (2+4*C/γ)
  have hH2 : 2 < q.H := by
    have hn : 0 ≤ 4*C/γ := div_nonneg (mul_nonneg (by norm_num) hC) hγ.le
    linarith
  have hCsmall : C < γ*q.H/4 := by
    have hx : 4*C < (q.H-2)*γ := (div_lt_iff₀ hγ).mp (by linarith : 4*C/γ < q.H-2)
    nlinarith
  have hexp : Real.log q.geometricScale/(q.H-1) ≤ γ := by
    apply (div_le_iff₀ (by linarith : 0 < q.H-1)).mpr
    have hz := q.log_geometricScale_le hp₀ (by omega)
    have hm : γ*q.H/2 ≤ γ*(q.H-1) := by nlinarith
    dsimp [C] at hCsmall
    nlinarith only [hz,hcost,hCsmall,hm]
  obtain ⟨b,hb,hnear⟩ := q.eventually_neighborMoment_lower hconn hqt root weight Γ htr
    (fun a ha => hΓ ha) (fun i => (hw i).le) hw1 i (hw i) hcover c hc hmin hp₀ hH
  refine ⟨b,hb,?_⟩
  filter_upwards [hnear] with p hp
  intro hpc
  have hχ : 1 ≤ rootSusceptibility G root weight p := by
    calc
      1 = ∑ i, weight i*1 := by simp only [mul_one,hw1]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (susceptibility_one_le G hloc hqt p hpc (root i)) (hw i).le)
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hχ (by linarith :
    2-γ ≤ 2-Real.log q.geometricScale/(q.H-1))) hb.le).trans (hp hpc)

end EfficientProfileMomentConsequence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory Function
section PivotalSprinklingGain
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_set_union_pair : Measurable (fun f : Set E × Set E => f.1 ∪ f.2) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  change MeasurableSet ({f : Set E × Set E | e ∈ f.1} ∪ {f | e ∈ f.2})
  apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
  · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_fst
  · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_snd

theorem measurable_set_insert (e : E) : Measurable (fun ω : Set E => insert e ω) := by
  have h : Measurable (fun ω : Set E => ({e}:Set E) ∪ ω) :=
    measurable_set_union_pair.comp (measurable_const.prodMk measurable_id)
  simpa only [Set.singleton_union] using (h : Measurable (fun ω : Set E => {e} ∪ ω))

theorem measurableSet_closedPivotal (A : Set (Set E)) (hA : MeasurableSet A) (e : E) :
    MeasurableSet (closedPivotal A e) := by
  exact (measurableSet_mem e).compl.inter (hA.compl.inter (hA.preimage (measurable_set_insert e)))

def singleSprinkle (Q : Finset E) (e : (Q : Set E)) : Set (Set E) :=
  {η | Subtype.val ⁻¹' η = {e}}

theorem measurableSet_singleSprinkle (Q : Finset E) (e : (Q : Set E)) :
    MeasurableSet (singleSprinkle Q e) :=
  (measurableSet_singleton _).preimage (measurable_set_restrict (Q:Set E))

theorem singleSprinkle_disjoint (Q : Finset E) :
    Pairwise (Disjoint on singleSprinkle Q) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro η ha hb
  apply hab
  have h : ({a} : Set (Q:Set E)) = {b} := ha.symm.trans hb
  simpa only [Set.singleton_eq_singleton_iff] using h

theorem singleSprinkle_mem (Q : Finset E) (e : (Q:Set E)) {η : Set E}
    (hη : η ∈ singleSprinkle Q e) : e.val ∈ η := by
  have h : e ∈ Subtype.val ⁻¹' η := by rw [hη]; exact Set.mem_singleton e
  exact h

theorem singleSprinkle_probability (Q : Finset E) (e : (Q:Set E)) (a : unitInterval) :
    (law a).real (singleSprinkle Q e) = (a:ℝ)*(1-(a:ℝ))^(Q.card-1) := by
  have h := congrArg (fun μ : Measure (Set (Q:Set E)) => μ.real {({e}:Set (Q:Set E))})
    (law_map_restrict a (Q:Set E))
  rw [Measure.real,Measure.map_apply (measurable_set_restrict _) (measurableSet_singleton _)] at h
  change (law a).real (singleSprinkle Q e) = _ at h
  rw [h,law,setBernoulli_real_singleton a (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,Set.ncard_singleton]
  simp only [Set.ncard_univ,Nat.card_eq_fintype_card,pow_one]
  rw [show Fintype.card (Q:Set E) = Q.card from Fintype.card_coe Q]

 

theorem event_sprinkling_gain (p a : unitInterval) (Q : Finset E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) * (∑ e ∈ Q, (law p).real (closedPivotal A e)) ≤
      (law (sprinkleParameter p a)).real A - (law p).real A := by
  let μ : Measure (Set E × Set E) := (law p).prod (law a)
  let B : Set (Set E × Set E) := {f | f.1 ∉ A ∧ f.1 ∪ f.2 ∈ A}
  let C (e : (Q:Set E)) := (closedPivotal A e.val) ×ˢ singleSprinkle Q e
  have hB : MeasurableSet B := (hA.compl.preimage measurable_fst).inter (hA.preimage measurable_set_union_pair)
  have hC (e : (Q:Set E)) : MeasurableSet (C e) :=
    (measurableSet_closedPivotal A hA e.val).prod (measurableSet_singleSprinkle Q e)
  have hd : Pairwise (Disjoint on C) := by
    intro e f hef
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp (singleSprinkle_disjoint Q hef) hz.2 hz'.2
  have hsub : (⋃ e, C e) ⊆ B := by
    intro z hz
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hz
    refine ⟨he.1.2.1,?_⟩
    apply hup _ he.1.2.2
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact Or.inr (singleSprinkle_mem Q e he.2)
    · exact Or.inl hf
  have hgain : μ.real B = (law (sprinkleParameter p a)).real A - (law p).real A := by
    have he : (fun f : Set E × Set E => f.1 ∪ f.2) ⁻¹' A = (A ×ˢ Set.univ) ∪ B := by
      ext f
      simp only [Set.mem_preimage,Set.mem_union,Set.mem_prod,Set.mem_univ,and_true,B,Set.mem_ofPred_eq]
      exact ⟨fun h => by by_cases ha : f.1 ∈ A; exact Or.inl ha; exact Or.inr ⟨ha,h⟩,
        fun h => h.elim (fun ha => hup Set.subset_union_left ha) And.right⟩
    have hd : Disjoint (A ×ˢ (Set.univ : Set (Set E))) B := by
      apply Set.disjoint_left.mpr
      intro f hf hf'
      exact hf'.1 hf.1
    have hm := congrArg (fun ν : Measure (Set E) => ν.real A) (law_map_union p a)
    rw [Measure.real,Measure.map_apply measurable_set_union_pair hA] at hm
    change μ.real ((fun f : Set E × Set E => f.1 ∪ f.2) ⁻¹' A) = _ at hm
    rw [he,measureReal_union hd hB] at hm
    have hp : μ.real (A ×ˢ Set.univ) = (law p).real A := by
      rw [measureReal_prod_prod,probReal_univ,mul_one]
    rw [hp] at hm
    linarith
  have hs : μ.real (⋃ e, C e) =
      (a:ℝ)*(1-(a:ℝ))^(Q.card-1) * (∑ e ∈ Q, (law p).real (closedPivotal A e)) := by
    rw [measureReal_iUnion_fintype hd hC]
    simp only [C,μ,measureReal_prod_prod,singleSprinkle_probability]
    rw [←Finset.sum_mul,mul_comm]
    congr 1
    apply Finset.sum_bij (fun e _ => e.val)
    · intro e _; exact e.property
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he; exact ⟨⟨e,he⟩,Finset.mem_univ _,rfl⟩
    · intro _ _; rfl
  rw [←hs,←hgain]
  exact measureReal_mono hsub

end PivotalSprinklingGain
end Percolation

end OAI
