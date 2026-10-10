import OAI.Probability.GaussianPropeller.FourCells

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

structure Configuration (d k:ℕ) where
  z : Fin k→Space d
  P : Fin k→ℝ
  zero : ∑ j,z j=0
  norm : ∑ j,‖z j‖^2=1
  pos : ∀ j,z j≠0
  order : Antitone (fun j=>‖z j‖)
  obtuse : Pairwise (fun j l=>⟪z j,z l⟫<0)
  cap : ∀ j,‖z j‖≤2/3
  probability : ∑ j,P j=1
  half : ∀ j,P j≤1/2
  quadratic : ∀ j,(if k=5 then (0.929:ℝ) else 0.884)*‖z j‖^2≤P j
  linear : ∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j
  pair : ∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2
  cap3 : k=4 → ∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j)
  loss4 : k=4 → ∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x

variable {d k:ℕ} [NeZero k]

lemma exists_configuration (hk:2≤k) {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) :
    Nonempty (Configuration d k) := by
  classical
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hs:0<(Real.sqrt (value A))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hCp)
  let v:Fin k→Space d := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
  let σ:=_root_.Tuple.sort (fun j=> -‖v j‖)
  let z:Fin k→Space d := fun j=>v (σ j)
  let P:Fin k→ℝ := fun j=>(gaussian d).real (A (σ j))
  have hr:∀ j,‖v j‖=‖centroid (A j)‖/Real.sqrt (value A) := by
    intro j
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    ring
  have hz:∀ j,‖z j‖=‖centroid (A (σ j))‖/Real.sqrt (value A) := fun j=>hr (σ j)
  refine ⟨{z:=z,P:=P,zero:=?_,norm:=?_,pos:=?_,order:=?_,obtuse:=?_,cap:=?_,
            probability:=?_,half:=?_,quadratic:=?_,linear:=?_,pair:=?_,cap3:=?_,loss4:=?_}⟩
  · dsimp [z]
    rw [Equiv.sum_comp σ]
    simp only [v,←Finset.smul_sum,sum_centroid_eq_zero hA.1.1,smul_zero]
  · dsimp [z]
    rw [Equiv.sum_comp σ (fun j => ‖v j‖^2)]
    simp_rw [hr,div_pow,Real.sq_sqrt hCp.le]
    rw [←Finset.sum_div]
    change value A/value A=1
    exact div_self hCp.ne'
  · intro j
    exact smul_ne_zero hs.ne' (active_centroid_ne_zero hA hCp (hall (σ j)))
  · intro i j hij
    have hh:=_root_.Tuple.monotone_sort (fun j=> -‖v j‖) hij
    exact neg_le_neg_iff.mp hh
  · intro i j hij
    change ⟪(Real.sqrt (value A))⁻¹•centroid (A (σ i)),(Real.sqrt (value A))⁻¹•centroid (A (σ j))⟫<0
    rw [real_inner_smul_left,real_inner_smul_right]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg hs
      (negative_inner_of_minimal hA (σ.injective.ne hij) (hall _) (hall _)))
  · intro j
    rw [hz]
    exact (normalized_centroid_lt_two_thirds (hA.1.1.1 _) hC).le
  · dsimp [P]
    rw [Equiv.sum_comp σ (fun j => (gaussian d).real (A j))]
    exact sum_cell_probability hA.1.1
  · intro j
    exact (active_probability_mem hk hA hCp (hall (σ j))).2
  · intro j
    rw [hz]
    by_cases hk5:k=5
    · subst k
      convert minimal_cap_four hA hC hall (σ j) using 1
      norm_num [P]
    · simp only [ite_eq_right hk5]
      convert normalized_cell_probability (hA.1.1.1 (σ j)) hC using 1 <;>
        norm_num [P,centroid,gaussian]
  · intro j
    rw [hz]
    exact (minimal_linear_quadratic hk hA hC hall (σ j)).le
  · intro i j l hij hil
    exact normalized_tuple_pair hA hC hall (σ.injective.ne hij) (σ.injective.ne hil)
  · intro hk4 j
    subst k
    rw [hz]
    exact minimal_cap_three hA hC hall (σ j)
  · intro hk4 j
    subst k
    rw [hz]
    obtain ⟨x,hx,hpx,hl⟩:=minimal_loss_constraint (by norm_num) hA hC hall (σ j)
    refine ⟨x,hx,hpx,le_trans ?_ hl⟩
    norm_num only [Nat.cast_ofNat] at hl ⊢
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)) (by positivity)

end GaussianPropeller.Reduction

end OAI
