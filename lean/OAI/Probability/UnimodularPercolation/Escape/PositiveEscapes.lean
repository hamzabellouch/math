import Mathlib
import OAI.Probability.UnimodularPercolation.Escape.CollisionTails

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
section DependentFiniteUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_dependent_event_union {β δ : Type*} [Fintype β] [Fintype δ]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    (μ : (b : β) → γ b → ℝ) (hμ : ∀ b c, 0 ≤ μ b c)
    (B : (b : β) → γ b → δ → Prop) :
    (∑ b, ∑ c, if ∃ d, B b c d then μ b c else 0) ≤
      ∑ d, ∑ b, ∑ c, if B b c d then μ b c else 0 := by
  have hh := finite_nonnegative_event_union
    (fun ξ : Sigma γ => μ ξ.1 ξ.2)
    (fun ξ => hμ ξ.1 ξ.2)
    (fun ξ : Sigma γ => B ξ.1 ξ.2)
  simpa only [Fintype.sum_sigma] using hh

end DependentFiniteUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualFinitePositionHits
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι S T : Type*} [Fintype I] [Fintype ι] [Fintype S] [Fintype T]

 

theorem raw_anchor_finite_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (j : S → I) (z : T → V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (L : ℕ) (y : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if ∃ st : S × T, h.val (j st.1) = z st.2 then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (Fintype.card S : ℝ)*(Fintype.card T : ℝ)*Real.sqrt c*‖P‖^L := by
  let (v : V) : Finite ((openSimpleGraph G Set.univ).neighborSet v) := finite_openSimpleGraph_neighbors G hloc v
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) L y) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  simp only [tsum_fintype]
  have hu := finite_dependent_event_union
    (β := RawFrom (openSimpleGraph G Set.univ) L y)
    (γ := fun mid => segmentAnchors G hloc γ n hdiam ep mid.1)
    (δ := S × T)
    (fun mid _ => mid.2.mass (walkKernel G hloc a)/(segmentAnchors G hloc γ n hdiam ep (γ ep)).card)
    (fun mid _ => div_nonneg (mid.2.mass_nonneg _ hK) (Nat.cast_nonneg _))
    (fun _ h st => h.val (j st.1) = z st.2)
  apply hu.trans
  calc
    _ ≤ ∑ _st : S × T, Real.sqrt c*‖P‖^L := by
      apply Finset.sum_le_sum
      intro st _
      obtain ⟨H,hH,hHn⟩ := exists_anchoredPositionOperator_uniform G hloc root weight Γ hΓ htr hw hw1 hcov
        c hc hmin γ n hdiam ep (j st.1)
      simpa only [tsum_fintype] using raw_anchor_point_collision_bound G hloc a γ n hdiam ep (j st.1)
        P H hpos hP hH (Real.sqrt c) hHn L y (z st.2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul]; ring

end ActualFinitePositionHits
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EarlyFiniteCollisions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {S : Type*} [Fintype S]

 

theorem raw_hits_distant_set_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m J : ℕ) (x : V) (z : S → V) (hD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (z s)) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if ∃ s, z s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      (Fintype.card S : ℝ)*‖P‖^J/(1-‖P‖) := by
  let (v : V) : Finite ((openSimpleGraph G Set.univ).neighborSet v) := finite_openSimpleGraph_neighbors G hloc v
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) m x) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have he (w : RawFrom (openSimpleGraph G Set.univ) m x) :
      (∃ s, z s ∈ w.2.vertices) ↔ ∃ si : S × Fin (m+1), w.2.position si.2.val = z si.1 := by
    constructor
    · rintro ⟨s,hs⟩
      obtain ⟨i,hi,he⟩ := w.2.mem_vertices_iff_position.mp hs
      exact ⟨(s,⟨i,by omega⟩),he⟩
    · rintro ⟨⟨s,i⟩,he⟩
      exact ⟨s,he ▸ w.2.position_mem_vertices i.val⟩
  simp only [he,tsum_fintype]
  have hu := finite_nonnegative_event_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK)
    (fun w (si : S × Fin (m+1)) => w.2.position si.2.val = z si.1)
  apply hu.trans
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _s : S, ∑ i : Fin (m+1), if J ≤ i.val then ‖P‖^i.val else 0 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro i _
      have hh := raw_position_probability G hloc a P hpos hP i.val m (by omega) x (z s)
      simp only [tsum_fintype] at hh
      rw [hh]
      split_ifs with hi
      · exact matrixCoeff_power_le P i.val x (z s)
      · exact (walkPower_zero_of_lt_dist G hloc a P hpos hP i.val x (z s) (by have hd := hD s; omega)).le
    _ ≤ ∑ _s : S, ‖P‖^J/(1-‖P‖) := Finset.sum_le_sum (fun _ _ =>
      finite_geometric_cutoff_bound ‖P‖ (norm_nonneg _) hρ J (m+1))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end EarlyFiniteCollisions
end Percolation

 
namespace Percolation
section QuantitativeEarlyCutoff

 

noncomputable def earlyCollisionCost (ρ : ℝ) (J : ℕ) : ℝ :=
  2*((J:ℝ)+1)*ρ^J/(1-ρ) + 2*ρ^J/(1-ρ)^2

theorem earlyCollisionCost_tendsto (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Filter.Tendsto (earlyCollisionCost ρ) Filter.atTop (nhds 0) := by
  have hn : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hρ] using hρ1
  have ht : Filter.Tendsto (fun J : ℕ => (J:ℝ)*ρ^J) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1 hn).tendsto_atTop_zero
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have hh := (((ht.add hp).const_mul 2).div_const (1-ρ)).add ((hp.const_mul 2).div_const ((1-ρ)^2))
  have he : earlyCollisionCost ρ = (fun J : ℕ => 2*((J:ℝ)*ρ^J+ρ^J)/(1-ρ)+2*ρ^J/(1-ρ)^2) := by
    funext J
    unfold earlyCollisionCost
    ring
  rw [he]
  simpa only [zero_add,mul_zero,zero_div] using hh

theorem exists_earlyCollisionCutoff (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → earlyCollisionCost ρ J < ε := by
  exact Filter.eventually_atTop.mp ((earlyCollisionCost_tendsto ρ hρ hρ1).eventually (gt_mem_nhds hε))

end QuantitativeEarlyCutoff
end Percolation

 
namespace Percolation
section WeightedBinaryUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_weighted_event_or {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (B C : α → Prop) [DecidablePred B] [DecidablePred C] :
    (∑ a, if B a ∨ C a then μ a else 0) ≤
      (∑ a, if B a then μ a else 0) + ∑ a, if C a then μ a else 0 := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hb : B a <;> by_cases hc : C a <;> simp only [hb,hc,or_self,or_false,false_or,ite_true,ite_false,add_zero,zero_add,le_refl]
  exact le_add_of_nonneg_right (hμ a)

end WeightedBinaryUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualEarlyExperiment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_early_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if ((∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices)) ∨
          (∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices) then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      earlyCollisionCost ‖P‖ J := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) m x) := Fintype.ofFinite _
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) L y) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hu := finite_weighted_event_or
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y =>
      w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a))
    (fun w => mul_nonneg (w.1.2.mass_nonneg _ hK) (w.2.2.mass_nonneg _ hK))
    (fun w => (∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices))
    (fun w => ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices)
  have hp := finite_product_failure_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w : RawFrom (openSimpleGraph G Set.univ) L y => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK) (fun w => w.2.mass_nonneg _ hK)
    (by simpa only [tsum_fintype] using rawFrom_probability_sum G hloc a m x)
    (by simpa only [tsum_fintype] using rawFrom_probability_sum G hloc a L y)
    (fun w => ∃ s, pos s ∈ w.2.vertices) (fun w => ∃ s, neg s ∈ w.2.vertices)
  have hx := raw_hits_distant_set_bound G hloc a P hpos hP hρ m J x pos hposD
  have hy := raw_hits_distant_set_bound G hloc a P hpos hP hρ L J y neg hnegD
  have hi := raw_intersection_uniform_bound G hloc a P hpos hsym hP hρ m L J x y hxy
  simp only [tsum_fintype,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hx hy hi ⊢
  have hx' : (∑ w : RawFrom (openSimpleGraph G Set.univ) m x,
      if ∃ s, pos s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((J:ℝ)+1)*‖P‖^J/(1-‖P‖) := by
    convert hx using 1
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  have hy' : (∑ w : RawFrom (openSimpleGraph G Set.univ) L y,
      if ∃ s, neg s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((J:ℝ)+1)*‖P‖^J/(1-‖P‖) := by
    convert hy using 1
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  have hp' : (∑ w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if (∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices) then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      (∑ w : RawFrom (openSimpleGraph G Set.univ) m x,
        if ∃ s, pos s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) +
      (∑ w : RawFrom (openSimpleGraph G Set.univ) L y,
        if ∃ s, neg s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) := by
    convert hp using 1
    · apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> rfl
    · congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;> split_ifs <;> rfl
  have hr : (((J:ℝ)+1)*‖P‖^J/(1-‖P‖) + ((J:ℝ)+1)*‖P‖^J/(1-‖P‖)) +
      2*‖P‖^J/(1-‖P‖)^2 = earlyCollisionCost ‖P‖ J := by
    unfold earlyCollisionCost
    ring
  have hh := hu.trans ((add_le_add (hp'.trans (add_le_add hx' hy')) hi).trans_eq hr)
  exact hh

end ActualEarlyExperiment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ConditioningCost
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchor_event_le_unconditioned (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V)
    (B : RawFrom (openSimpleGraph G Set.univ) m x → RawFrom (openSimpleGraph G Set.univ) L y → Prop) [∀ tail mid, Decidable (B tail mid)] :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B tail mid then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if B w.1 w.2 then w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep (γ ep)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  simp only [tsum_fintype,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro tail _
  apply Finset.sum_le_sum
  intro mid _
  by_cases hb : B tail mid
  · simp only [ite_eq_left hb,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    have hc : ((segmentAnchors G hloc γ n hdiam ep mid.1).card : ℝ) ≤
        (segmentAnchors G hloc γ n hdiam ep (γ ep)).card := by
      rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
      split_ifs
      · exact le_rfl
      · exact_mod_cast Nat.zero_le _
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK))
    nlinarith
  · simp only [ite_eq_right hb,Finset.sum_const_zero]
    exact le_rfl

end ConditioningCost
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EarlyAnchoredCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchor_early_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
              (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices) then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      earlyCollisionCost ‖P‖ J := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  exact (raw_anchor_event_le_unconditioned G hloc a hK γ n hdiam ep m L x y
    (fun tail mid => ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
      (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices))).trans
    (raw_early_collision_bound G hloc a P hpos hsym hP hρ m L J x y pos neg hposD hnegD hxy)

 

theorem raw_tail_integrate_anchor_event (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V)
    (B : (mid : RawFrom (openSimpleGraph G Set.univ) L y) →
      segmentAnchors G hloc γ n hdiam ep mid.1 → Prop) [∀ mid h, Decidable (B mid h)] :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B mid h then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if B mid h then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) := by
  have he (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) :
      (if B mid h then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
        (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
      tail.2.mass (walkKernel G hloc a) *
        (if B mid h then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) := by
    split_ifs <;> ring
  simp only [he,tsum_mul_left,tsum_mul_right,rawFrom_probability_sum G hloc a,one_mul]

end EarlyAnchoredCollision
end Percolation

 
namespace Percolation
section DependentUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_threefold_event_or {α β : Type*} {γ : β → Type*}
    [Fintype α] [Fintype β] [∀ b, Fintype (γ b)]
    (μ : α → (b : β) → γ b → ℝ) (hμ : ∀ a b c, 0 ≤ μ a b c)
    (B C : α → (b : β) → γ b → Prop)
    [∀ a b c, Decidable (B a b c)] [∀ a b c, Decidable (C a b c)] :
    (∑ a, ∑ b, ∑ c, if B a b c ∨ C a b c then μ a b c else 0) ≤
      (∑ a, ∑ b, ∑ c, if B a b c then μ a b c else 0) +
      (∑ a, ∑ b, ∑ c, if C a b c then μ a b c else 0) := by
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  by_cases hb : B a b c <;> by_cases hc : C a b c <;>
    simp only [hb,hc,or_self,or_false,false_or,ite_true,ite_false,add_zero,zero_add,le_refl]
  exact le_add_of_nonneg_right (hμ a b c)

end DependentUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

def firstEscapeCollision (G : BondGraph V E) (J m L : ℕ) (x y : V)
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (tail : RawFrom (openSimpleGraph G Set.univ) m x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L y) (h : I → V) : Prop :=
  (((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
    (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices)) ∨
  ((∃ st : Fin (J+1) × Fin (J+1), h (j st.1) = neg st.2) ∨
    (∃ ij : Fin (m+1) × Fin (J+1), tail.2.position ij.1.val = h (j ij.2)))

noncomputable def suffixCollisionCost (ρ c : ℝ) (J : ℕ) : ℝ :=
  ((J:ℝ)+1)^2*Real.sqrt c + ((J:ℝ)+1)*Real.sqrt c/(1-ρ)

 

theorem raw_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  let μ := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (_h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
      (segmentAnchors G hloc γ n hdiam ep (γ ep)).card
  have hμ : ∀ tail mid h, 0 ≤ μ tail mid h := fun tail mid _ =>
    div_nonneg (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)) (Nat.cast_nonneg _)
  let B := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (_h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
      (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices)
  let C := fun (_tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ∃ st : Fin (J+1) × Fin (J+1), h.val (j st.1) = neg st.2
  let D := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ∃ ij : Fin (m+1) × Fin (J+1), tail.2.position ij.1.val = h.val (j ij.2)
  have hu := finite_threefold_event_or μ hμ B (fun tail mid h => C tail mid h ∨ D tail mid h)
  have hv := finite_threefold_event_or μ hμ C D
  have he := raw_anchor_early_collision_bound G hloc a γ n hdiam ep P hpos hsym hP hρ
    m L J x y pos neg hposD hnegD hxy
  have hn := raw_anchor_finite_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j neg P hpos hP L y
  rw [←raw_tail_integrate_anchor_event G hloc a γ n hdiam ep m L x y
    (fun _ h => ∃ st : Fin (J+1) × Fin (J+1), h.val (j st.1) = neg st.2)] at hn
  have ht := raw_tail_whole_suffix_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j P hpos hP hρ m L x y
  simp only [tsum_fintype,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at he hn ht ⊢
  have hr : earlyCollisionCost ‖P‖ J +
      ((((J:ℝ)+1)*((J:ℝ)+1)*Real.sqrt c*‖P‖^L) +
        ((J:ℝ)+1)*Real.sqrt c*‖P‖^L/(1-‖P‖)) =
      earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
    unfold suffixCollisionCost
    ring
  have hh := hu.trans ((add_le_add he (hv.trans (add_le_add hn ht))).trans_eq hr)
  apply le_trans ?_ hh
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro tail _
  apply Finset.sum_congr rfl
  intro mid _
  apply Finset.sum_congr rfl
  intro h _
  unfold firstEscapeCollision B C D μ
  split_ifs <;> rfl

end CombinedRawAvoidance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedFirstEscape
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem conditional_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (hy : y ∈ vertexOrbit G (γ ep))
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
        segmentReturnMass G hloc a γ ep L y ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  have hb := raw_first_escape_collision_bound G hloc a root weight Γ hΓ htr
    (fun r => (hw r).le) hw1 hcov c hc.le hmin γ n hdiam ep P hpos hsym hP hρ
    m L J x y pos neg j hposD hnegD hxy
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  rw [←segmentReturnMass_on_orbit G hloc a γ ep L y hy P hpos hP] at hq
  have htc : 0 < 2*c := mul_pos (by norm_num) hc
  have hqp : 0 < segmentReturnMass G hloc a γ ep L y := (one_div_pos.mpr htc).trans_le hq
  apply (div_le_iff₀ hqp).mpr
  apply hb.trans
  have hB : 0 ≤ earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
    unfold earlyCollisionCost suffixCollisionCost
    have : 0 < 1-‖P‖ := sub_pos.mpr hρ
    positivity
  have h1 : 1 ≤ (2*c)*segmentReturnMass G hloc a γ ep L y := by
    exact (div_le_iff₀ htc).mp hq |>.trans_eq (mul_comm _ _)
  have hh := mul_le_mul_of_nonneg_right h1 hB
  nlinarith only [hh]

end NormalizedFirstEscape
end Percolation

 
namespace Percolation
section FirstEscapeChoiceOrder

 

theorem exists_first_escape_uniform_cutoffs (ρ c ε : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      2*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L) < ε := by
  have hδ : 0 < ε/(4*c) := div_pos hε (by positivity)
  obtain ⟨J₀,hJ₀⟩ := exists_earlyCollisionCutoff ρ hρ hρ1 (ε/(4*c)) hδ
  let J := max J₀ 1
  have hJ : 0 < J := lt_of_lt_of_le (by omega : 0 < 1) (le_max_right _ _)
  have he : earlyCollisionCost ρ J < ε/(4*c) := hJ₀ J (le_max_left _ _)
  have hel : 2*c*earlyCollisionCost ρ J < ε := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*c)).mp he
    nlinarith
  have ht : Filter.Tendsto
      (fun L : ℕ => 2*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L))
      Filter.atTop (nhds (2*c*earlyCollisionCost ρ J)) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul
      (suffixCollisionCost ρ c J)).const_add (earlyCollisionCost ρ J)
    have hh' := hh.const_mul (2*c)
    simpa only [mul_zero,add_zero] using hh'
  obtain ⟨L₀,hL₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hel))
  exact ⟨J,hJ,L₀,hL₀⟩

end FirstEscapeChoiceOrder
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralConditionalMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_tail_anchor_total_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card) =
      segmentReturnMass G hloc a γ ep L y := by
  have hN : ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep (γ ep)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  have hh := raw_tail_integrate_anchor_event G hloc a γ n hdiam ep m L x y (fun _ _ => True)
  simp only [ite_true] at hh
  rw [hh]
  unfold segmentReturnMass
  apply tsum_congr
  intro mid
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
  split_ifs
  · field_simp
  · simp only [Nat.cast_zero,zero_mul]

 

theorem raw_tail_anchor_conditional_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V) (hq : segmentReturnMass G hloc a γ ep L y ≠ 0) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card /
              segmentReturnMass G hloc a γ ep L y) = 1 := by
  have hh := raw_tail_anchor_total_mass G hloc a γ n hdiam ep m L x y
  simp only [tsum_div_const] at hh ⊢
  rw [hh]
  exact div_self hq

end LiteralConditionalMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralGeodesicSeparation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem graph_dist_aut (G : BondGraph V E) (hconn : Connected G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    (openSimpleGraph G Set.univ).dist (a x) (a y) =
      (openSimpleGraph G Set.univ).dist x y := by
  have hreach (x y : V) : (openSimpleGraph G Set.univ).Reachable x y :=
    (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)
  obtain ⟨q,hq⟩ := (hreach x y).exists_walk_length_eq_dist
  obtain ⟨r,hr⟩ := (hreach (a x) (a y)).exists_walk_length_eq_dist
  have hq' := SimpleGraph.dist_le (q.map (autSimpleGraph G hab).toHom)
  have hr' := SimpleGraph.dist_le (r.map (autSimpleGraph G (isAut_symm G hab)).toHom)
  simp only [SimpleGraph.Walk.length_map,hq] at hq'
  change (openSimpleGraph G Set.univ).dist (a.symm (a x)) (a.symm (a y)) ≤ _ at hr'
  simp only [a.symm_apply_apply,SimpleGraph.Walk.length_map,hr] at hr'
  exact le_antisymm hq' hr'

 

theorem geodesic_anchor_early_separations (G : BondGraph V E) (hconn : Connected G)
    {x y : V} (q : (openSimpleGraph G Set.univ).Walk x y) (J : ℕ)
    (hlen : q.length = 2*J) (hq : q.length = (openSimpleGraph G Set.univ).dist x y)
    (s : Fin (2*J+1) → V) (hs : s ∈ segmentOrbit G (geodesicSegment G q (2*J))) :
    (∀ i : Fin (J+1), J ≤ (openSimpleGraph G Set.univ).dist
      (s ⟨0,by omega⟩) (s ⟨J+i.val,by omega⟩)) ∧
    (∀ i : Fin (J+1), J ≤ (openSimpleGraph G Set.univ).dist
      (s ⟨2*J,by omega⟩) (s ⟨i.val,by omega⟩)) ∧
    (2*J ≤ (openSimpleGraph G Set.univ).dist (s ⟨0,by omega⟩) (s ⟨2*J,by omega⟩)) := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  constructor
  · intro i
    dsimp only [Function.comp_apply,geodesicSegment]
    rw [graph_dist_aut G hconn hab]
    rw [geodesic_getVert_dist _ q hq 0 (J+i.val) (by omega) (by omega)]
    omega
  constructor
  · intro i
    dsimp only [Function.comp_apply,geodesicSegment]
    rw [graph_dist_aut G hconn hab,SimpleGraph.dist_comm]
    rw [geodesic_getVert_dist _ q hq i.val (2*J) (by omega) (by omega)]
    omega
  · dsimp only [Function.comp_apply,geodesicSegment]
    rw [graph_dist_aut G hconn hab]
    rw [geodesic_getVert_dist _ q hq 0 (2*J) (by omega) (by omega)]
    omega

end LiteralGeodesicSeparation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositiveFirstEscape
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem exists_positive_first_escape (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (hy : y ∈ vertexOrbit G (γ ep))
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y)
    (hsmall : 2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) < 1) :
    ∃ (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      ¬firstEscapeCollision G J m L x y pos neg j tail mid h.val ∧
      0 < tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) := by
  have hb := conditional_first_escape_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep P hpos hsym hP hdiag hρ m L J x y hy pos neg j hposD hnegD hxy
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  rw [←segmentReturnMass_on_orbit G hloc a γ ep L y hy P hpos hP] at hq
  have hqp : 0 < segmentReturnMass G hloc a γ ep L y :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  by_contra H
  have heq :
      (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
                (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
      ∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card := by
    apply tsum_congr
    intro tail
    apply tsum_congr
    intro mid
    apply tsum_congr
    intro h
    split_ifs with ht
    · rfl
    · have hz : tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) = 0 := by
        apply le_antisymm
        · exact le_of_not_gt (fun hp => H ⟨tail,mid,h,ht,hp⟩)
        · exact mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)
      rw [hz,zero_div]
  rw [heq,raw_tail_anchor_total_mass G hloc a γ n hdiam ep m L x y,div_self hqp.ne'] at hb
  exact (not_lt_of_ge hb) hsmall

end PositiveFirstEscape
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ProjectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_event_fiber_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (μ : α → ℝ) (B : β → Prop) [DecidablePred B] :
    (∑ a, if B (f a) then μ a else 0) =
      ∑ b, if B b then ∑ a, if f a = b then μ a else 0 else 0 := by
  calc
    _ = ∑ a, ∑ b, if B b then (if f a = b then μ a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      have hf : (fun b => if B b then (if f a = b then μ a else 0) else 0) =
          fun b => if f a = b then (if B (f a) then μ a else 0) else 0 := by
        funext b
        by_cases h : f a = b
        · subst b
          simp
        · simp [h]
      rw [hf]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : B b <;> simp [h]

 

theorem rooted_label_raw_event_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (B : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x → Prop) [DecidablePred B] :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if B (rootedEscapeLabelRaw G J L m γ hγ x ξ) then
        escapeLabelProbability G hloc a γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) ≤
      (∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x,
        if B w then w.2.mass (walkKernel G hloc a) else 0)/(a^(J+J)*q) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let : Fintype {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} := Fintype.ofFinite _
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) := Fintype.ofFinite _
  rw [←tsum_indicator_div]
  simp only [tsum_fintype]
  rw [finite_event_fiber_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : B w
  · simp only [hw,ite_true]
    simpa only [tsum_fintype] using
      rooted_label_raw_projection_bound G hloc a ha hK J L m γ hγ n hdiam x hx q hq hqle w
  · simp only [hw,ite_false,le_refl]

end ProjectionEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FirstLabeledMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
def labelFirstEscapeCollision (G : BondGraph V E) (γ : I → V) (ep neg : I)
    (J L m : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (ξ : EscapeLabel G γ ep neg L m) : Prop :=
  firstEscapeCollision G J m L (ξ.first neg) (ξ.first ep)
    (fun t => ξ.first (posIdx t)) (fun t => ξ.first (negIdx t)) suffixIdx
    ξ.leftTail ⟨ξ.last ep,ξ.middle⟩ ξ.last

theorem labelFromCode_first_collision (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx
      (labelFromCode G hloc γ n hdiam center ep neg L m x c).1 =
    firstEscapeCollision G J m L (c.1.val neg) (c.1.val ep)
      (fun t => c.1.val (posIdx t)) (fun t => c.1.val (negIdx t)) suffixIdx
      c.2.2.2.1 c.2.1 c.2.2.1.val := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem raw_rooted_first_collision_marginal (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        ξ.1.mass (walkKernel G hloc a) else 0) =
    ∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L (s.val neg) (s.val ep)
              (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) else 0 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass,labelFromCode_first_collision]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  apply tsum_congr
  intro s
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  have hh (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep)) :
      (∑' hh : Σ h : segmentAnchors G hloc γ n hdiam ep mid.1,
          RawFrom (openSimpleGraph G Set.univ) m (s.val neg) × RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if firstEscapeCollision G J m L (s.val neg) (s.val ep)
          (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx hh.2.1 mid hh.1.val then
          mid.2.mass (walkKernel G hloc a)*hh.2.1.2.mass (walkKernel G hloc a)*hh.2.2.2.mass (walkKernel G hloc a) else 0) =
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        ∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
          if firstEscapeCollision G J m L (s.val neg) (s.val ep)
            (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) else 0 := by
    rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
    apply tsum_congr
    intro h
    rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
    apply tsum_congr
    intro tail
    split_ifs
    · simp only [tsum_mul_left,rawFrom_probability_sum G hloc a,mul_one]
      exact mul_comm _ _
    · simp only [tsum_zero]
  simp_rw [hh]
  simp only [tsum_fintype]
  conv_lhs =>
    arg 2
    intro mid
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end FirstLabeledMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section NormalizedMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_first_collision_probability_marginal (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    (∑' s : segmentAnchors G hloc γ n hdiam center x,
      (∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L (s.val neg) (s.val ep)
              (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
                (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
          segmentReturnMass G hloc a γ ep L (γ ep)) /
      (segmentAnchors G hloc γ n hdiam center (γ center)).card := by
  simp only [escapeLabelProbability,tsum_indicator_div,tsum_div_const]
  rw [raw_rooted_first_collision_marginal G hloc a γ n hdiam center ep neg J L m x posIdx negIdx suffixIdx]
  ring

end NormalizedMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullFirstEscapeBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem rooted_first_collision_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  rw [rooted_first_collision_probability_marginal G hloc a γ n hdiam center ep neg J L m x posIdx negIdx suffixIdx]
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam center (γ center)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  apply (div_le_iff₀ hN).mpr
  simp only [tsum_fintype]
  calc
    _ ≤ ∑ s : segmentAnchors G hloc γ n hdiam center x,
        2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
      apply Finset.sum_le_sum
      intro s _
      have hs := ((mem_segmentAnchors G hloc γ n hdiam center x s.val).mp s.property).1
      have hy : s.val ep ∈ vertexOrbit G (γ ep) := by
        obtain ⟨g,b,hg,he⟩ := hs
        rw [he]
        exact ⟨g,b,hg,rfl⟩
      obtain ⟨hp,hn,hxy⟩ := hsep s.val hs
      have hh := conditional_first_escape_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
        c hc hmin γ n hdiam ep P hpos hsym hP hdiag hρ m L J (s.val neg) (s.val ep) hy
        (fun i => s.val (posIdx i)) (fun i => s.val (negIdx i)) suffixIdx hp hn hxy
      rw [segmentReturnMass_on_orbit G hloc a γ ep L (s.val ep) hy P hpos hP] at hh
      simpa only [tsum_fintype] using hh
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx]
      ring

end FullFirstEscapeBound
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CollisionNaturality
attribute [local instance] Classical.propDecidable Classical.decEq

namespace HoldingWalk
variable {W : Type*} {H : SimpleGraph V} {H' : SimpleGraph W}
theorem map_position (f : H →g H') {k : ℕ} {x y : V} (q : HoldingWalk H k x y) (i : ℕ) :
    (q.map f).position i = f (q.position i) := by
  induction q generalizing i with
  | nil => rfl
  | hold q ih => cases i <;> simp only [map,position,ih]
  | step h q ih => cases i <;> simp only [map,position,ih]
end HoldingWalk

theorem list_common_vertex_map_iff {W : Type*} (f : V → W) (hf : Function.Injective f)
    (l r : List V) :
    (∃ z, z ∈ l.map f ∧ z ∈ r.map f) ↔ ∃ z, z ∈ l ∧ z ∈ r := by
  constructor
  · rintro ⟨z,hz,hz'⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hz'
    have : y = x := hf he
    subst y
    exact ⟨x,hx,hy⟩
  · rintro ⟨z,hz,hz'⟩
    exact ⟨f z,List.mem_map.mpr ⟨z,hz,rfl⟩,List.mem_map.mpr ⟨z,hz',rfl⟩⟩

 
theorem labelFirstEscapeCollision_aut (G : BondGraph V E) (γ : I → V) (ep neg : I)
    (J L m : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx (EscapeLabel.autMap hab ξ) ↔
      labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ := by
  dsimp only [labelFirstEscapeCollision,firstEscapeCollision,EscapeLabel.autMap,Function.comp_apply,autSimpleGraph]
  simp only [HoldingWalk.map_vertices,HoldingWalk.map_position]
  change (((∃ s, a (ξ.first (posIdx s)) ∈ ξ.leftTail.2.vertices.map a) ∨
    (∃ s, a (ξ.first (negIdx s)) ∈ ξ.middle.vertices.map a)) ∨
    (∃ z, z ∈ ξ.leftTail.2.vertices.map a ∧ z ∈ ξ.middle.vertices.map a)) ∨
    ((∃ st : Fin (J+1) × Fin (J+1), a (ξ.last (suffixIdx st.1)) = a (ξ.first (negIdx st.2))) ∨
      (∃ ij : Fin (m+1) × Fin (J+1), a (ξ.leftTail.2.position ij.1.val) = a (ξ.last (suffixIdx ij.2)))) ↔ _
  rw [list_common_vertex_map_iff a a.injective]
  simp only [List.mem_map,Equiv.apply_eq_iff_eq]
  simp

end CollisionNaturality
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section BothEscapeEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rootOrbitWeight_pos (G : BondGraph V E)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (hw : ∀ i, 0 < weight i)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x) (x : V) :
    0 < ∑ i, if root i ∈ vertexOrbit G x then weight i else 0 := by
  obtain ⟨r,g,hg,he⟩ := hcov x
  obtain ⟨b,hab⟩ := hΓ hg
  have hr : root r ∈ vertexOrbit G x := by
    refine ⟨g.symm,b.symm,isAut_symm G hab,?_⟩
    rw [←he,Equiv.symm_apply_apply]
  have hh : (if root r ∈ vertexOrbit G x then weight r else 0) ≤
      ∑ i, if root i ∈ vertexOrbit G x then weight i else 0 :=
    Finset.single_le_sum (f := fun i => if root i ∈ vertexOrbit G x then weight i else 0)
      (fun i _ => by split_ifs <;> first | exact (hw i).le | rfl) (Finset.mem_univ r)
  simpa only [ite_eq_left hr] using lt_of_lt_of_le (by simpa only [ite_eq_left hr] using hw r) hh

 

theorem rooted_escape_collision_reversal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0 := by
  have hh := rooted_escape_label_reversal G hloc a root weight Γ hΓ htr γ n hdiam center ep neg L m
    (rootOrbitWeight_pos G root weight Γ hΓ hw hcov (γ center))
    (fun ξ => if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ then (1:ℝ) else 0)
    (fun g b hab ξ => by rw [labelFirstEscapeCollision_aut G γ ep neg J L m posIdx negIdx suffixIdx hab ξ]) x hx
  simpa only [mul_ite,mul_one,mul_zero] using hh

end BothEscapeEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section BothEscapeBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rooted_both_collision_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hb := rooted_first_collision_probability_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have he := rooted_escape_collision_reversal G hloc a root weight Γ hΓ htr hw hcov
    γ n hdiam center ep neg m L J x hx posIdx negIdx suffixIdx
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  have hu := finite_weighted_event_or
    (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1)
    (fun ξ => escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse)
  simp only [tsum_fintype] at hb he ⊢
  rw [←he] at hu
  linarith

end BothEscapeBound
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section PositiveTwoEscapes
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem exists_positive_two_escape_label (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) (hsmall : 4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) < 1) :
    ∃ ξ : EscapeLabel G γ ep neg L m, ξ.first center = x ∧
      ¬labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ ∧
      ¬labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.reverse ∧
      0 < escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  have hb := rooted_both_collision_probability_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have hs := (rooted_label_probability_hasSum G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx).tsum_eq
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  by_contra H
  have heq :
      (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
        if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
          labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
          escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 := by
    apply tsum_congr
    intro ξ
    split_ifs with ht
    · rfl
    · apply Eq.symm
      apply le_antisymm
      · exact le_of_not_gt (fun hp => H ⟨ξ.1,ξ.2,(not_or.mp ht).1,(not_or.mp ht).2,hp⟩)
      · exact escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1
  rw [heq,hs] at hb
  exact (not_lt_of_ge hb) hsmall

end PositiveTwoEscapes
end Percolation

end OAI
