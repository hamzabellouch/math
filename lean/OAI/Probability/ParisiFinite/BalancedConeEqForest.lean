import Mathlib
import OAI.Probability.ParisiFinite.NegativeFlip
import OAI.Probability.ParisiFinite.TermNormSub

namespace OAI

/-! Balanced Cone Eq Forest. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories
open Locality BoundedBranch
attribute [local instance] Classical.propDecidable

 

theorem balanced_cone_eq_forest {m : ℕ} (p : ℕ) (γ β : Fin p → ℝ)
    (r : Edge m) (H : Finset (Edge m))
    (hc : H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r))
    (hb : (usedVertices r H).card=H.card+2) :
    H=forestEdges r (forestCode r H p) := by
  apply (Finset.eq_of_subset_of_card_le (forestCode_edges_subset r H p) ?_).symm
  rw [forestCode_edges_card]
  have hu := used_card_eq_forestSize_add_two p γ β r H hc
  omega

 

theorem nonzero_shape_is_forest (m p : ℕ) (γ β : Fin p → ℝ) (g : FullGraph m)
    (hn : shapeTermLimit m p γ β g≠0) :
    m=g.1.2.card+2 ∧ g.1.2=forestEdges g.1.1 (forestCode g.1.1 g.1.2 p) ∧
      reached g.1.1 g.1.2 p=Finset.univ := by
  have hb : m=g.1.2.card+2 := by
    by_contra h
    exact hn (by simp [shapeTermLimit,h])
  have hg : graphCoefficientLimit m p γ β g.1.1 g.1.2≠0 := by
    intro hz
    exact hn (by simp [shapeTermLimit,hb,hz])
  have hc : g.1.2⊆relevantEdges (g.1.2∪{g.1.1}) (qaoaWord p γ β) (roots g.1.1) := by
    by_contra h
    exact hg (graphCoefficientLimit_zero_of_not_cone m p γ β g.1.1 g.1.2 h)
  have hcount : (usedVertices g.1.1 g.1.2).card=g.1.2.card+2 := by
    rw [g.2,Finset.card_univ,Fintype.card_fin]
    exact hb
  refine ⟨hb,balanced_cone_eq_forest p γ β g.1.1 g.1.2 hc hcount,?_⟩
  exact (used_eq_ball p γ β g.1.1 g.1.2 hc).symm.trans g.2

 

theorem energySliceLimit_eq_forests (m p : ℕ) (γ β : Fin p → ℝ) :
    energySliceLimit m p γ β=
      ∑g : FullGraph m with m=g.1.2.card+2 ∧
        g.1.2=forestEdges g.1.1 (forestCode g.1.1 g.1.2 p) ∧
        reached g.1.1 g.1.2 p=Finset.univ,
          (m.factorial:ℂ)⁻¹*graphCoefficientLimit m p γ β g.1.1 g.1.2 := by
  unfold energySliceLimit
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hc : m=g.1.2.card+2 ∧
      g.1.2=forestEdges g.1.1 (forestCode g.1.1 g.1.2 p) ∧
      reached g.1.1 g.1.2 p=Finset.univ
  · simp only [ite_eq_left hc,shapeTermLimit,ite_eq_left hc.1]
  · rw [ite_eq_right hc]
    by_contra hn
    exact hc (nonzero_shape_is_forest m p γ β g hn)

end SKQAOA.SiteHistories

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories

@[fun_prop] theorem continuous_step (σ τ : Bool) : Continuous (fun t : ℝ => step t σ τ) := by
  unfold step
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_mix (p : ℕ) (σ : Bool) (h : Bits p) :
    Continuous (fun β : Fin p → ℝ => mix p β σ h) := by
  induction p generalizing σ with
  | zero => simp only [mix]; fun_prop
  | succ p ih =>
    simp only [mix]
    apply Continuous.mul
    · fun_prop
    · exact (ih _ _).comp (continuous_pi fun i => continuous_apply i.castSucc)

@[fun_prop] theorem continuous_weight (p : ℕ) (s : Site p) :
    Continuous (fun β : Fin p → ℝ => weight p β s) := by
  unfold weight
  fun_prop

@[fun_prop] theorem continuous_interaction (p : ℕ) (a b : Bits p) :
    Continuous (fun γ : Fin p → ℝ => interaction p γ a b) := by
  induction p with
  | zero => simp only [interaction]; fun_prop
  | succ p ih =>
    simp only [interaction]
    apply Continuous.add
    · fun_prop
    · exact (ih _ _).comp (continuous_pi fun i => continuous_apply i.castSucc)

@[fun_prop] theorem continuous_delta (p : ℕ) (a b : Site p) :
    Continuous (fun γ : Fin p → ℝ => delta p γ a b) := by
  unfold delta
  fun_prop

@[fun_prop] theorem continuous_angleMass (p : ℕ) :
    Continuous (fun γ : Fin p → ℝ => angleMass p γ) := by
  induction p with
  | zero => simp only [angleMass]; fun_prop
  | succ p ih =>
    simp only [angleMass]
    apply Continuous.add
    · fun_prop
    · exact ih.comp (continuous_pi fun i => continuous_apply i.castSucc)

@[fun_prop] theorem continuous_variation (p : ℕ) :
    Continuous (fun β : Fin p → ℝ => variation p β) := by
  unfold variation
  fun_prop

@[fun_prop] theorem continuous_activity (p : ℕ) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => activity p θ.1 θ.2) := by
  unfold activity
  fun_prop

@[fun_prop] theorem continuous_markedBound (p : ℕ) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => markedBound p θ.1 θ.2) := by
  unfold markedBound
  fun_prop

@[fun_prop] theorem continuous_tower (h : ℕ) :
    Continuous (fun x : ℝ => BoundedBranch.tower x h) := by
  induction h with
  | zero => simp only [BoundedBranch.tower]; fun_prop
  | succ h ih =>
    simp only [BoundedBranch.tower]
    exact Real.continuous_exp.comp (continuous_id.mul ih)

@[fun_prop] theorem continuous_tailConstant (p : ℕ) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => tailConstant p θ.1 θ.2) := by
  unfold tailConstant
  fun_prop

@[fun_prop] theorem continuous_graphCoefficientLimit (m p : ℕ) (r : Edge m)
    (H : Finset (Edge m)) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => graphCoefficientLimit m p θ.1 θ.2 r H) := by
  unfold graphCoefficientLimit FiniteHistory.expectation
  apply continuous_finsetSum
  intro a ha
  apply Continuous.mul
  · fun_prop
  · apply Continuous.mul
    · fun_prop
    · apply continuous_finsetProd
      intro e he
      split_ifs <;> fun_prop

@[fun_prop] theorem continuous_shapeTermLimit (m p : ℕ) (g : FullGraph m) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => shapeTermLimit m p θ.1 θ.2 g) := by
  unfold shapeTermLimit
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_energySliceLimit (m p : ℕ) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => energySliceLimit m p θ.1 θ.2) := by
  unfold energySliceLimit
  fun_prop

end SKQAOA.SiteHistories

 

open scoped Topology
open Filter

namespace UniformApproximation

 

theorem continuous_of_geometric_approximants {X E : Type*} [TopologicalSpace X]
    [PseudoMetricSpace E] (f : X → E) (a : ℕ → X → E) (C : X → ℝ)
    (ha : ∀ L,Continuous (a L)) (hC : Continuous C)
    (_ : ∀ x,0≤C x) (hd : ∀ L x,dist (f x) (a L x)≤C x/(2:ℝ)^L) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto f (𝓝 x) (𝓝 (f x))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht : Tendsto (fun L : ℕ => (C x+1)/(2:ℝ)^L) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹<1)).const_mul (C x+1)
    simpa only [div_eq_mul_inv,inv_pow,mul_zero] using hh
  obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds (by positivity : 0<ε/4))).exists
  have hnearC : ∀ᶠ y in 𝓝 x,C y<C x+1 :=
    hC.continuousAt.eventually (gt_mem_nhds (by linarith : C x<C x+1))
  have hneara : ∀ᶠ y in 𝓝 x,dist (a L y) (a L x)<ε/2 :=
    (Metric.tendsto_nhds.mp (ha L).continuousAt) _ (by positivity)
  filter_upwards [hnearC,hneara] with y hyC hya
  have hy := (hd L y).trans (div_le_div_of_nonneg_right hyC.le (by positivity))
  have hx := (hd L x).trans
    (div_le_div_of_nonneg_right (by linarith : C x≤C x+1) (by positivity))
  have htri := dist_triangle4 (f y) (a L y) (a L x) (f x)
  rw [dist_comm (a L x)] at htri
  linarith

end UniformApproximation

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories

 
def valueApprox (p L : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  (∑m∈Finset.range (L+2),energySliceLimit m p γ β).re

@[fun_prop] theorem continuous_valueApprox (p L : ℕ) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => valueApprox p L θ.1 θ.2) := by
  unfold valueApprox
  fun_prop

 

theorem value_approx_error (p L : ℕ) (γ β : Fin p → ℝ) :
    |value p γ β-valueApprox p L γ β|≤tailConstant p γ β/(2:ℝ)^L := by
  have ht := (tendsto_expectedEnergy_value p γ β).sub
    (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_truncatedEnergy p L γ β))
  apply le_of_tendsto ht.abs
  apply Eventually.of_forall
  intro n
  calc
    |expectedEnergy n p γ β-(truncatedEnergy n p L γ β).re|
        = |(complexEnergy n p γ β-truncatedEnergy n p L γ β).re| := by
      rw [expectedEnergy_eq_complexEnergy,Complex.sub_re]
    _ ≤ ‖complexEnergy n p γ β-truncatedEnergy n p L γ β‖ := Complex.abs_re_le_norm _
    _ ≤ _ := norm_complexEnergy_sub_truncated n p L γ β

end SKQAOA.SiteHistories

namespace SKQAOA

 

@[fun_prop] theorem continuous_value (p : ℕ) :
    Continuous (fun θ : (Fin p → ℝ)×(Fin p → ℝ) => value p θ.1 θ.2) := by
  apply UniformApproximation.continuous_of_geometric_approximants
    (a:=fun L θ => SiteHistories.valueApprox p L θ.1 θ.2)
    (C:=fun θ => SiteHistories.tailConstant p θ.1 θ.2)
  · exact SiteHistories.continuous_valueApprox p
  · exact SiteHistories.continuous_tailConstant p
  · exact fun θ => SiteHistories.tailConstant_nonneg p θ.1 θ.2
  · intro L θ
    simpa only [Real.dist_eq] using SiteHistories.value_approx_error p L θ.1 θ.2

end SKQAOA

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories
attribute [local instance] Classical.propDecidable

 

theorem norm_energySlice_bound (n p L : ℕ) (γ β : Fin p → ℝ) :
    ‖energySlice n (L+2) p γ β‖≤tailConstant p γ β/(2:ℝ)^L := by
  calc
    _ ≤ ∑g : MarkedGraph n with (usedVertices g.1 g.2).card=L+2,
        ‖clusterEnergy p γ β g.1 g.2‖ := norm_sum_le _ _
    _ ≤ ∑g : MarkedGraph n with L+2≤(usedVertices g.1 g.2).card,
        ‖clusterEnergy p γ β g.1 g.2‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro g hg
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_eq (Finset.mem_filter.mp hg).2.symm⟩
      · intro g hg hgn
        exact norm_nonneg _
    _ = ∑r : Edge n,∑H : Finset (Edge n) with L+2≤(usedVertices r H).card,
        ‖clusterEnergy p γ β r H‖ := by
      simp only [Finset.sum_filter,Fintype.sum_prod_type]
    _ ≤ _ := sum_norm_clusterEnergy_tail n p L γ β

theorem norm_energySliceLimit_bound (p L : ℕ) (γ β : Fin p → ℝ) :
    ‖energySliceLimit (L+2) p γ β‖≤tailConstant p γ β/(2:ℝ)^L := by
  apply le_of_tendsto (tendsto_energySlice (L+2) p γ β).norm
  exact Eventually.of_forall (fun n => norm_energySlice_bound n p L γ β)

 

theorem summable_energySliceLimit (p : ℕ) (γ β : Fin p → ℝ) :
    Summable (fun m => energySliceLimit m p γ β) := by
  have hg : Summable (fun L : ℕ => tailConstant p γ β/(2:ℝ)^L) := by
    have := (summable_geometric_of_norm_lt_one (by norm_num : ‖(2:ℝ)⁻¹‖<1)).mul_left
      (tailConstant p γ β)
    simpa only [div_eq_mul_inv,inv_pow] using this
  have hs : Summable (fun L => energySliceLimit (L+2) p γ β) :=
    Summable.of_norm_bounded hg (fun L => norm_energySliceLimit_bound p L γ β)
  exact (summable_nat_add_iff 2).mp hs

 

theorem value_eq_support_series (p : ℕ) (γ β : Fin p → ℝ) :
    value p γ β=(∑'m : ℕ,energySliceLimit m p γ β).re := by
  have hs := (summable_energySliceLimit p γ β).hasSum.tendsto_sum_nat
  have ht : Tendsto (fun L : ℕ => valueApprox p L γ β) atTop
      (𝓝 (∑'m : ℕ,energySliceLimit m p γ β).re) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp (hs.comp (tendsto_add_atTop_nat 2))
  have hz : Tendsto (fun L : ℕ => tailConstant p γ β/(2:ℝ)^L) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹<1)).const_mul (tailConstant p γ β)
    simpa only [div_eq_mul_inv,inv_pow,mul_zero] using this
  have hv : Tendsto (fun L : ℕ => valueApprox p L γ β) atTop (𝓝 (value p γ β)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun L => dist_nonneg) _ hz
    intro L
    simpa only [Real.dist_eq,abs_sub_comm] using value_approx_error p L γ β
  exact tendsto_nhds_unique hv ht

 

theorem value_eq_forest_series (p : ℕ) (γ β : Fin p → ℝ) :
    value p γ β=(∑'m : ℕ,
      ∑g : FullGraph m with m=g.1.2.card+2 ∧
        g.1.2=forestEdges g.1.1 (forestCode g.1.1 g.1.2 p) ∧
        reached g.1.1 g.1.2 p=Finset.univ,
          (m.factorial:ℂ)⁻¹*graphCoefficientLimit m p γ β g.1.1 g.1.2).re := by
  rw [value_eq_support_series]
  congr 1
  apply tsum_congr
  intro m
  exact energySliceLimit_eq_forests m p γ β

end SKQAOA.SiteHistories

 

open scoped Topology
open Filter

namespace RawPulseControl
open PulseControl
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A]

 
def words (G : κ → A) : Submonoid A where
  carrier := Set.range (pulseValue G)
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro U V ⟨w,rfl⟩ ⟨v,rfl⟩
    exact ⟨w++v,pulseValue_append G w v⟩

variable [NormedAlgebra ℚ A] [CompleteSpace A] [StarRing A] [CStarRing A] [StarModule ℝ A]

theorem words_unitary (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) :
    words G≤unitary A := by
  rintro U ⟨w,rfl⟩
  apply (unitary A).list_prod_mem
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem p.2 (hG p.1))

theorem closure_unitary (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) :
    (words G).topologicalClosure≤unitary A :=
  (words G).topologicalClosure_minimal (words_unitary G hG) isClosed_unitary

variable [NormOneClass A] [Nontrivial A]

def directions (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) : Submodule ℝ A :=
  tangents _ (words G).isClosed_topologicalClosure (closure_unitary G hG)

theorem generator_mem (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) (a : κ) :
    G a∈directions G hG := by
  refine ⟨hG a,fun t => (words G).le_topologicalClosure ?_⟩
  exact ⟨[(a,t)],by simp only [pulseValue,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]⟩

theorem bracket_mem (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) {X Y : A}
    (hX : X∈directions G hG) (hY : Y∈directions G hG) :
    X*Y-Y*X∈directions G hG := by
  apply commutator_loop_tangent_mem _ (words G).isClosed_topologicalClosure (closure_unitary G hG) hX.1 hY.1
  intro u v
  exact (words G).topologicalClosure.mul_mem
    ((words G).topologicalClosure.mul_mem
      ((words G).topologicalClosure.mul_mem (hX.2 u) (hY.2 v)) (hX.2 (-u))) (hY.2 (-v))

theorem closed_directions (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) :
    IsClosed (directions G hG : Set A) :=
  isClosed_tangents _ (words G).isClosed_topologicalClosure (closure_unitary G hG)

 

theorem approximate (G : κ → A) (hG : ∀a,G a∈skewAdjoint A) {X : A}
    (hX : X∈directions G hG) (t : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃w : List (κ×ℝ),‖pulseValue G w-NormedSpace.exp (t•X)‖<ε := by
  obtain ⟨U,⟨w,rfl⟩,hd⟩ := Metric.mem_closure_iff.mp (hX.2 t) ε hε
  exact ⟨w,by simpa only [dist_eq_norm,norm_sub_rev] using hd⟩

end RawPulseControl

 

open scoped Topology
open Filter

namespace CompactSeedControl
open QuaternionControl RawPulseControl
variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]

abbrev SpinField (S : Type*) [TopologicalSpace S] := C(S,Quaternion ℝ)
local instance balancedConeEqForestSpinFieldNormedAlgebra : NormedAlgebra ℚ (SpinField S) :=
  NormedAlgebra.restrictScalars ℚ ℝ (SpinField S)

def X (f : C(S,ℝ)) : SpinField S :=
  ⟨fun s => f s • (⟨0,0,0,1⟩ : Quaternion ℝ),f.continuous.smul continuous_const⟩
def Y (f : C(S,ℝ)) : SpinField S :=
  ⟨fun s => f s • (⟨0,0,1,0⟩ : Quaternion ℝ),f.continuous.smul continuous_const⟩
def Z (f : C(S,ℝ)) : SpinField S :=
  ⟨fun s => f s • (⟨0,1,0,0⟩ : Quaternion ℝ),f.continuous.smul continuous_const⟩

omit [CompactSpace S] [Nonempty S] in
@[simp] theorem X_apply (f : C(S,ℝ)) (s : S) : X f s=⟨0,0,0,f s⟩ := by
  change f s • (⟨0,0,0,1⟩ : Quaternion ℝ) = _
  apply Quaternion.ext <;> simp
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Y_apply (f : C(S,ℝ)) (s : S) : Y f s=⟨0,0,f s,0⟩ := by
  change f s • (⟨0,0,1,0⟩ : Quaternion ℝ) = _
  apply Quaternion.ext <;> simp
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Z_apply (f : C(S,ℝ)) (s : S) : Z f s=⟨0,f s,0,0⟩ := by
  change f s • (⟨0,1,0,0⟩ : Quaternion ℝ) = _
  apply Quaternion.ext <;> simp

omit [CompactSpace S] [Nonempty S] in
@[simp] theorem X_add (f g : C(S,ℝ)) : X (f+g)=X f+X g := by
  apply ContinuousMap.ext
  intro s
  simpa only [ContinuousMap.add_apply,X_apply,qX,Pi.add_apply] using
    congrFun (qX_add (fun t => f t) (fun t => g t)) s
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem X_smul (r : ℝ) (f : C(S,ℝ)) : X (r•f)=r•X f := by
  apply ContinuousMap.ext
  intro s
  simpa only [ContinuousMap.smul_apply,X_apply,qX,Pi.smul_apply,smul_eq_mul] using
    congrFun (qX_smul r (fun t => f t)) s
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Y_smul (r : ℝ) (f : C(S,ℝ)) : Y (r•f)=r•Y f := by
  apply ContinuousMap.ext
  intro s
  change (r * f s) • (⟨0,0,1,0⟩ : Quaternion ℝ) = r • (f s • (⟨0,0,1,0⟩ : Quaternion ℝ))
  exact mul_smul r (f s) _
omit [CompactSpace S] [Nonempty S] in
@[simp] theorem Z_smul (r : ℝ) (f : C(S,ℝ)) : Z (r•f)=r•Z f := by
  apply ContinuousMap.ext
  intro s
  change (r * f s) • (⟨0,1,0,0⟩ : Quaternion ℝ) = r • (f s • (⟨0,1,0,0⟩ : Quaternion ℝ))
  exact mul_smul r (f s) _

omit [CompactSpace S] [Nonempty S] in
theorem bracket_ZX (f g : C(S,ℝ)) : Z f*X g-X g*Z f=Y ((-2:ℝ)•(f*g)) := by
  apply ContinuousMap.ext
  intro s
  simpa only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    X_apply,Y_apply,Z_apply,qX,qY,qZ,Pi.mul_apply,Pi.sub_apply,smul_eq_mul,mul_assoc] using
    congrFun (bracket_zx (fun t => f t) (fun t => g t)) s

omit [CompactSpace S] [Nonempty S] in
theorem bracket_ZY (f g : C(S,ℝ)) : Z f*Y g-Y g*Z f=X ((2:ℝ)•(f*g)) := by
  rw [X_smul]
  apply ContinuousMap.ext
  intro s
  simpa only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    X_apply,Y_apply,Z_apply,qX,qY,qZ,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using
    congrFun (bracket_zy (fun t => f t) (fun t => g t)) s

omit [CompactSpace S] [Nonempty S] in
theorem bracket_YX (f g : C(S,ℝ)) : Y f*X g-X g*Y f=Z ((2:ℝ)•(f*g)) := by
  apply ContinuousMap.ext
  intro s
  simpa only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    X_apply,Y_apply,Z_apply,qX,qY,qZ,Pi.mul_apply,Pi.sub_apply,smul_eq_mul,mul_assoc] using
    congrFun (bracket_yx (fun t => f t) (fun t => g t)) s

 

def generator (s : C(S,ℝ)) (a : Bool) : SpinField S := if a then Z s else X 1

omit [CompactSpace S] [Nonempty S] in
theorem generator_skew (s : C(S,ℝ)) (a : Bool) : generator s a∈skewAdjoint (SpinField S) := by
  rw [skewAdjoint.mem_iff]
  apply ContinuousMap.ext
  intro t
  have hx (r : ℝ) : star (r • (⟨0,0,0,1⟩ : Quaternion ℝ)) = -(r • (⟨0,0,0,1⟩ : Quaternion ℝ)) := by
    apply QuaternionAlgebra.star_eq_neg.mpr
    change r * 0 = 0
    ring
  have hz (r : ℝ) : star (r • (⟨0,1,0,0⟩ : Quaternion ℝ)) = -(r • (⟨0,1,0,0⟩ : Quaternion ℝ)) := by
    apply QuaternionAlgebra.star_eq_neg.mpr
    change r * 0 = 0
    ring
  cases a
  · exact hx 1
  · exact hz (s t)

def available (s : C(S,ℝ)) : Submodule ℝ (SpinField S) :=
  directions (generator s) (generator_skew s)

theorem X_one_mem (s : C(S,ℝ)) : X 1∈available s :=
  generator_mem (generator s) (generator_skew s) false

theorem Z_seed_mem (s : C(S,ℝ)) : Z s∈available s :=
  generator_mem (generator s) (generator_skew s) true

theorem Y_seed_mul_mem (s f : C(S,ℝ)) (hf : X f∈available s) :
    Y (s*f)∈available s := by
  have h := bracket_mem (generator s) (generator_skew s) (Z_seed_mem s) hf
  rw [bracket_ZX,Y_smul] at h
  have hh := (available s).smul_mem (-1/2:ℝ) h
  simpa only [smul_smul,show (-1/2:ℝ)*(-2)=1 by norm_num,one_smul] using hh

theorem X_sq_mul_mem (s f : C(S,ℝ)) (hf : X f∈available s) :
    X (s^2*f)∈available s := by
  have h := bracket_mem (generator s) (generator_skew s) (Z_seed_mem s) (Y_seed_mul_mem s f hf)
  rw [bracket_ZY,X_smul] at h
  have hh := (available s).smul_mem (1/2:ℝ) h
  simp only [smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul] at hh
  simpa only [pow_two,mul_assoc] using hh

theorem X_even_power_mem (s : C(S,ℝ)) (k : ℕ) : X ((s^2)^k)∈available s := by
  induction k with
  | zero => simpa only [pow_zero] using X_one_mem s
  | succ k ih => simpa only [pow_succ'] using X_sq_mul_mem s ((s^2)^k) ih

 

theorem X_even_polynomial_mem (s : C(S,ℝ)) (P : Polynomial ℝ) :
    X (P.aeval (s^2))∈available s := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add,X_add] using (available s).add_mem hP hQ
  | monomial k a =>
    have h := (available s).smul_mem a (X_even_power_mem s k)
    rw [Polynomial.aeval_monomial,← Algebra.smul_def,X_smul]
    exact h

theorem Z_seed_mul_mem (s f : C(S,ℝ)) (hf : X f∈available s) :
    Z (s*f)∈available s := by
  have h := bracket_mem (generator s) (generator_skew s) (Y_seed_mul_mem s f hf) (X_one_mem s)
  rw [bracket_YX,mul_one,Z_smul] at h
  have hh := (available s).smul_mem (1/2:ℝ) h
  simpa only [smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul] using hh

 

theorem polynomial_pulse_approximation (s : C(S,ℝ)) (P : Polynomial ℝ) (t : ℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∃w : List (Bool×ℝ),‖PulseControl.pulseValue (generator s) w-
      NormedSpace.exp (t•X (P.aeval (s^2)))‖<ε :=
  approximate (generator s) (generator_skew s) (X_even_polynomial_mem s P) t hε

end CompactSeedControl

 

open scoped Topology
open Filter

namespace CompactSeedControl
variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
local instance balancedConeEqForestContinuousSpinFieldNormedAlgebra : NormedAlgebra ℚ (SpinField S) :=
  NormedAlgebra.restrictScalars ℚ ℝ (SpinField S)

 
omit [CompactSpace S] [Nonempty S] in
theorem continuous_X : Continuous (X : C(S,ℝ) → SpinField S) := by
  let k : Quaternion ℝ := ⟨0,0,0,1⟩
  exact (((ContinuousLinearMap.id ℝ ℝ).smulRight k).compLeftContinuous ℝ S).continuous

omit [CompactSpace S] [Nonempty S] in
theorem continuous_Y : Continuous (Y : C(S,ℝ) → SpinField S) := by
  let k : Quaternion ℝ := ⟨0,0,1,0⟩
  exact (((ContinuousLinearMap.id ℝ ℝ).smulRight k).compLeftContinuous ℝ S).continuous

omit [CompactSpace S] [Nonempty S] in
theorem continuous_Z : Continuous (Z : C(S,ℝ) → SpinField S) := by
  let k : Quaternion ℝ := ⟨0,1,0,0⟩
  exact (((ContinuousLinearMap.id ℝ ℝ).smulRight k).compLeftContinuous ℝ S).continuous

 

theorem X_function_square_mem (s : C(S,ℝ)) (h : C(ℝ,ℝ)) :
    X (h.comp (s^2))∈available s := by
  let I := Set.Icc (0:ℝ) ‖s^2‖
  let η : C(S,I) := ⟨fun t => ⟨(s^2) t, by
    constructor
    · simpa only [ContinuousMap.pow_apply] using sq_nonneg (s t)
    · exact (s^2).apply_le_norm t⟩, by fun_prop⟩
  have hc : Continuous (fun f : C(I,ℝ) => X (f.comp η)) :=
    continuous_X.comp (ContinuousMap.compRightAlgHom_continuous ℝ ℝ η)
  have hz : IsClosed {f : C(I,ℝ) | X (f.comp η)∈available s} :=
    (RawPulseControl.closed_directions (generator s) (generator_skew s)).preimage hc
  have hp : (polynomialFunctions I : Set C(I,ℝ)) ⊆
      {f : C(I,ℝ) | X (f.comp η)∈available s} := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨P,rfl⟩ := hf
    change X ((P.toContinuousMapOn I).comp η)∈available s
    have he : (P.toContinuousMapOn I).comp η = P.aeval (s^2) := by
      ext t
      simp [η,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap]
    rw [he]
    exact X_even_polynomial_mem s P
  have ht : h.restrict I ∈ closure (polynomialFunctions I : Set C(I,ℝ)) :=
    continuousMap_mem_polynomialFunctions_closure 0 ‖s^2‖ _
  have hh := closure_minimal hp hz ht
  exact hh

 

theorem X_even_continuous_mem (s : C(S,ℝ)) (f : C(ℝ,ℝ)) (hf : Function.Even f) :
    X (f.comp s)∈available s := by
  let h : C(ℝ,ℝ) := f.comp ⟨Real.sqrt,Real.continuous_sqrt⟩
  have hh := X_function_square_mem s h
  have he : h.comp (s^2) = f.comp s := by
    ext t
    change f (Real.sqrt ((s t)^2))=f (s t)
    rw [Real.sqrt_sq_eq_abs]
    rcases le_total 0 (s t) with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht,hf]
  rwa [he] at hh

theorem even_continuous_pulse_approximation (s : C(S,ℝ)) (f : C(ℝ,ℝ))
    (hf : Function.Even f) (t : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃w : List (Bool×ℝ),‖PulseControl.pulseValue (generator s) w-
      NormedSpace.exp (t•X (f.comp s))‖<ε :=
  RawPulseControl.approximate (generator s) (generator_skew s) (X_even_continuous_mem s f hf) t hε

end CompactSeedControl

end

end OAI
