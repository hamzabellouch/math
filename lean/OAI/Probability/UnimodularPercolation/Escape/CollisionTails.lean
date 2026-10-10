import Mathlib
import OAI.Probability.UnimodularPercolation.Escape.Labels

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawTimeMarginals
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_position_integral (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (i m : ℕ) (him : i ≤ m) (x : V) (f : V → ℝ) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * f (w.2.position i)) =
      RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) i x f := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction i generalizing m x with
  | zero =>
    simp only [HoldingWalk.position_zero,tsum_mul_right,rawFrom_probability_sum G hloc a,one_mul,RawFrom.integral_zero]
  | succ i ih =>
    cases m with
    | zero => omega
    | succ m =>
      rw [←(RawFrom.succEquiv m x).symm.tsum_eq,RawFrom.integral_succ]
      let (z : V) := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m z)
      let := Fintype.ofFinite ((openSimpleGraph G Set.univ).neighborSet x)
      have hh (z : V) := ih m (Nat.le_of_succ_le_succ him) z
      simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,RawFrom.succEquiv,
        Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,HoldingWalk.position,mul_assoc]
      simp only [tsum_fintype] at hh
      simp only [←Finset.mul_sum,hh]

theorem raw_position_probability (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m : ℕ) (him : i ≤ m) (x z : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if w.2.position i = z then w.2.mass (walkKernel G hloc a) else 0) =
      (matrixCoeff (P^i) x z).re := by
  have hh := raw_position_integral G hloc a i m him x (fun y => if y = z then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at hh
  rw [hh,raw_integral_operator G hloc a P hpos hP]
  simp only [mul_ite,mul_one,mul_zero,tsum_ite_eq]

end RawTimeMarginals
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_two_time_collision (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m j n : ℕ) (him : i ≤ m) (hjn : j ≤ n) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if w.1.2.position i = w.2.2.position j then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) =
      (matrixCoeff (P^(i+j)) x y).re := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) n y)
  have hi (w : RawFrom (openSimpleGraph G Set.univ) m x) :
      (∑' v : RawFrom (openSimpleGraph G Set.univ) n y,
        if w.2.position i = v.2.position j then w.2.mass (walkKernel G hloc a)*v.2.mass (walkKernel G hloc a) else 0) =
      w.2.mass (walkKernel G hloc a)*(matrixCoeff (P^j) y (w.2.position i)).re := by
    rw [← raw_position_probability G hloc a P hpos hP j n hjn y (w.2.position i),←tsum_mul_left]
    apply tsum_congr
    intro v
    by_cases hh : w.2.position i = v.2.position j
    · simp only [ite_eq_left hh,ite_eq_left hh.symm]
    · simp only [ite_eq_right hh,ite_eq_right (Ne.symm hh),mul_zero]
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
  simp only [hi]
  rw [raw_position_integral G hloc a i m him x (fun z => (matrixCoeff (P^j) y z).re),raw_integral_operator G hloc a P hpos hP]
  simp only [matrixCoeff_real_symm (P^j) (hsym.pow j) y]
  rw [((hpos.pow i).mul_hasSum (P^j) x y).tsum_eq,←pow_add]

theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

theorem matrixCoeff_power_le (P : Hilbert V →L[ℂ] Hilbert V) (k : ℕ) (x y : V) :
    (matrixCoeff (P^k) x y).re ≤ ‖P‖^k := by
  have hn (k : ℕ) : ‖P^k‖ ≤ ‖P‖^k := by
    induction k with
    | zero => simpa only [pow_zero,ContinuousLinearMap.one_def] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ k ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (P^k) x y).trans (hn k))

end IndependentRawCollisions
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePropagation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_exists_short_walk (G : BondGraph V E) (x : V) (k : ℕ) {y : V}
    (hy : y ∈ reachBall G x k) :
    ∃ q : (openSimpleGraph G Set.univ).Walk x y, q.length ≤ k := by
  induction k generalizing y with
  | zero =>
    have he : y = x := hy
    subst y
    exact ⟨.nil,by simp⟩
  | succ k ih =>
    rcases hy with hy | hy
    · obtain ⟨q,hq⟩ := ih hy
      exact ⟨q,hq.trans (Nat.le_succ _)⟩
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      obtain ⟨q,hq⟩ := ih hz
      by_cases he : z = y
      · subst z
        exact ⟨q,hq.trans (Nat.le_succ _)⟩
      · let h : (openSimpleGraph G Set.univ).Adj z y :=
          (openSimpleGraph_univ_adj G z y).mpr ⟨he,hzy⟩
        refine ⟨q.append (.cons h .nil),?_⟩
        simpa only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_nil,zero_add] using Nat.add_le_add_right hq 1

theorem dist_le_of_mem_reachBall (G : BondGraph V E) (x y : V) (k : ℕ)
    (hy : y ∈ reachBall G x k) : (openSimpleGraph G Set.univ).dist x y ≤ k := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G x k hy
  exact (SimpleGraph.dist_le q).trans hq

theorem walkPower_zero_of_lt_dist (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x y : V) (hk : k < (openSimpleGraph G Set.univ).dist x y) :
    (matrixCoeff (P^k) x y).re = 0 := by
  apply walkPower_support G hloc a P hpos hP
  intro hy
  exact Nat.not_le_of_gt hk (dist_le_of_mem_reachBall G x y k hy)

 

theorem raw_two_time_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m j n : ℕ) (him : i ≤ m) (hjn : j ≤ n) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if w.1.2.position i = w.2.2.position j then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      if i+j < (openSimpleGraph G Set.univ).dist x y then 0 else ‖P‖^(i+j) := by
  rw [raw_two_time_collision G hloc a P hpos hsym hP i m j n him hjn x y]
  split_ifs with hh
  · exact (walkPower_zero_of_lt_dist G hloc a P hpos hP (i+j) x y hh).le
  · exact matrixCoeff_power_le P (i+j) x y

end FinitePropagation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualCollisionUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_nonnegative_event_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (B : α → β → Prop) :
    (∑ a, if ∃ b, B a b then μ a else 0) ≤ ∑ b, ∑ a, if B a b then μ a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hh : ∃ b, B a b
  · obtain ⟨b,hb⟩ := hh
    rw [ite_eq_left ⟨b,hb⟩]
    calc
      μ a = (if B a b then μ a else 0) := (ite_eq_left hb).symm
      _ ≤ ∑ b, if B a b then μ a else 0 :=
        Finset.single_le_sum (f := fun b => if B a b then μ a else 0)
          (fun b _ => by split_ifs; exact hμ a; exact le_rfl) (Finset.mem_univ b)
  · rw [ite_eq_right hh]
    exact Finset.sum_nonneg (fun b _ => by split_ifs; exact hμ a; exact le_rfl)

 

theorem raw_intersection_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (m n : ℕ) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
    ∑ i : Fin (m+1), ∑ j : Fin (n+1),
      if i.val+j.val < (openSimpleGraph G Set.univ).dist x y then 0 else ‖P‖^(i.val+j.val) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) n y)
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have he (w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y) :
      (∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices) ↔
        ∃ ij : Fin (m+1) × Fin (n+1), w.1.2.position ij.1 = w.2.2.position ij.2 := by
    constructor
    · rintro ⟨z,hz,hz'⟩
      obtain ⟨i,hi,he⟩ := w.1.2.mem_vertices_iff_position.mp hz
      obtain ⟨j,hj,he'⟩ := w.2.2.mem_vertices_iff_position.mp hz'
      exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),he.trans he'.symm⟩
    · rintro ⟨⟨i,j⟩,hij⟩
      exact ⟨w.1.2.position i,w.1.2.position_mem_vertices i,hij ▸ w.2.2.position_mem_vertices j⟩
  simp only [he,tsum_fintype]
  have hu := finite_nonnegative_event_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y =>
      w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a))
    (fun w => mul_nonneg (w.1.2.mass_nonneg _ hK) (w.2.2.mass_nonneg _ hK))
    (fun w (ij : Fin (m+1) × Fin (n+1)) => w.1.2.position ij.1 = w.2.2.position ij.2)
  apply hu.trans
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [tsum_fintype] using
    raw_two_time_collision_bound G hloc a P hpos hsym hP i m j n (by omega) (by omega) x y

end ActualCollisionUnion
end Percolation

 
namespace Percolation
section UniformCollisionTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem geometric_cutoff_summable (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    Summable (fun i : ℕ => if J ≤ i then ρ^i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (fun i => by split_ifs <;> first | exact le_rfl | exact pow_nonneg hρ i)
    (summable_geometric_of_lt_one hρ hρ1)

theorem geometric_cutoff_tsum (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    (∑' i : ℕ, if J ≤ i then ρ^i else 0) = ρ^J/(1-ρ) := by
  have hs := geometric_cutoff_summable ρ hρ hρ1 J
  rw [←hs.sum_add_tsum_nat_add J]
  have hz : (∑ i ∈ Finset.range J, if J ≤ i then ρ^i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (Nat.not_le_of_gt (Finset.mem_range.mp hi))
  rw [hz,zero_add]
  simp only [Nat.le_add_left,ite_true,pow_add,tsum_mul_right,
    tsum_geometric_of_lt_one hρ hρ1,div_eq_mul_inv]
  exact mul_comm _ _

theorem finite_geometric_cutoff_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J M : ℕ) :
    (∑ i : Fin M, if J ≤ i.val then ρ^i.val else 0) ≤ ρ^J/(1-ρ) := by
  change (∑ i : Fin M, (fun n : ℕ => if J ≤ n then ρ^n else 0) i.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if J ≤ n then ρ^n else 0) M,←geometric_cutoff_tsum ρ hρ hρ1 J]
  exact Summable.sum_le_tsum (s := Finset.range M) (fun i _ => by split_ifs <;> positivity)
    (geometric_cutoff_summable ρ hρ hρ1 J)

 

theorem finite_double_geometric_cutoff_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (J M N D : ℕ) (hD : 2*J ≤ D) :
    (∑ i : Fin M, ∑ j : Fin N, if i.val+j.val < D then 0 else ρ^(i.val+j.val)) ≤
      2*ρ^J/(1-ρ)^2 := by
  let q : ℕ → ℝ := fun i => if J ≤ i then ρ^i else 0
  have hq (i : ℕ) : 0 ≤ q i := by dsimp [q]; split_ifs <;> positivity
  have hp (i : ℕ) : 0 ≤ ρ^i := pow_nonneg hρ i
  have hQ := finite_geometric_cutoff_bound ρ hρ hρ1 J M
  have hQ' := finite_geometric_cutoff_bound ρ hρ hρ1 J N
  have hS := finite_geometric_cutoff_bound ρ hρ hρ1 0 M
  have hS' := finite_geometric_cutoff_bound ρ hρ hρ1 0 N
  simp only [Nat.zero_le,ite_true,pow_zero,one_div] at hS hS'
  have hd : 0 < 1-ρ := sub_pos.mpr hρ1
  calc
    _ ≤ ∑ i : Fin M, ∑ j : Fin N, (q i.val*ρ^j.val + ρ^i.val*q j.val) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hh : i.val+j.val < D
      · rw [ite_eq_left hh]
        exact add_nonneg (mul_nonneg (hq _) (hp _)) (mul_nonneg (hp _) (hq _))
      · rw [ite_eq_right hh,pow_add]
        have hj : J ≤ i.val ∨ J ≤ j.val := by omega
        rcases hj with hi | hj
        · simp only [q,ite_eq_left hi]
          exact le_add_of_nonneg_right (mul_nonneg (hp _) (by split_ifs <;> positivity))
        · simp only [q,ite_eq_left hj]
          exact le_add_of_nonneg_left (mul_nonneg (by split_ifs <;> positivity) (hp _))
    _ = (∑ i : Fin M, q i.val)*(∑ j : Fin N, ρ^j.val) +
        (∑ i : Fin M, ρ^i.val)*(∑ j : Fin N, q j.val) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
    _ ≤ (ρ^J/(1-ρ))*(1-ρ)⁻¹ + (1-ρ)⁻¹*(ρ^J/(1-ρ)) := by
      apply add_le_add
      · exact mul_le_mul hQ hS' (Finset.sum_nonneg (fun i _ => hp _)) (by positivity)
      · exact mul_le_mul hS hQ' (Finset.sum_nonneg (fun i _ => hq _)) (by positivity)
    _ = _ := by field_simp; ring

end UniformCollisionTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawCollision
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_intersection_uniform_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hcontract : ‖P‖ < 1)
    (m n J : ℕ) (x y : V) (hD : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      2*‖P‖^J/(1-‖P‖)^2 :=
  (raw_intersection_probability_bound G hloc a P hpos hsym hP m n x y).trans
    (finite_double_geometric_cutoff_bound ‖P‖ (norm_nonneg _) hcontract J (m+1) (n+1) _ hD)

 
theorem exists_uniform_raw_collision_separation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hcontract : ‖P‖ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ m n : ℕ, ∀ x y : V,
      2*J ≤ (openSimpleGraph G Set.univ).dist x y →
      (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
        if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
          w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) < ε := by
  have ht : Filter.Tendsto (fun J : ℕ => 2*‖P‖^J/(1-‖P‖)^2) Filter.atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg P) hcontract).const_mul 2).div_const ((1-‖P‖)^2)
  obtain ⟨J₀,hJ⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨J₀,?_⟩
  intro J hJJ m n x y hd
  exact (raw_intersection_uniform_bound G hloc a P hpos hsym hP hcontract m n J x y hd).trans_lt (hJ J hJJ)

end UniformRawCollision
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def fromPositions : (k : ℕ) → (f : Fin (k+1) → V) →
    (∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) →
    HoldingWalk H k (f 0) (f (Fin.last k))
  | 0,f,_ => .nil (f 0)
  | k+1,f,h => .step (h 0) (fromPositions k (fun i => f i.succ) (fun i => h i.succ))

theorem mass_fromPositions (P : V → V → ℝ) (a : ℝ)
    (hP : ∀ x y, H.Adj x y → P x y = a)
    (k : ℕ) (f : Fin (k+1) → V) (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) :
    (fromPositions k f h).mass P = a^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change P (f 0) (f 1) * (fromPositions k (fun i => f i.succ) (fun i => h i.succ)).mass P = a^(k+1)
    have he : P (f 0) (f 1) = a := by simpa using hP _ _ (h 0)
    rw [he,ih,pow_succ']

theorem position_fromPositions (k : ℕ) (f : Fin (k+1) → V)
    (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) (i : ℕ) (hi : i ≤ k) :
    (fromPositions k f h).position i = f ⟨i,by omega⟩ := by
  induction k generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih (fun j => f j.succ) (fun j => h j.succ) i (by omega)

end HoldingWalk
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

theorem position_append_left {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) (i : ℕ) (hi : i ≤ k) :
    (w.append v).position i = w.position i := by
  induction w generalizing i with
  | nil =>
    obtain rfl : i = 0 := by omega
    exact v.position_zero
  | hold w ih => cases i with
    | zero => rfl
    | succ i => exact ih v i (by omega)
  | step h w ih => cases i with
    | zero => rfl
    | succ i => exact ih v i (by omega)

theorem position_append_right {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) (i : ℕ) :
    (w.append v).position (k+i) = v.position i := by
  induction w with
  | nil => simp only [Nat.zero_add,append]
  | hold w ih => simpa only [Nat.succ_add,append,position] using ih v
  | step h w ih => simpa only [Nat.succ_add,append,position] using ih v

 

theorem ext_positions {k : ℕ} {x y : V} (w v : HoldingWalk H k x y)
    (h : ∀ i : ℕ, i ≤ k → w.position i = v.position i) : w = v := by
  induction k generalizing x y with
  | zero => cases w; cases v; rfl
  | succ k ih =>
    cases w with
    | hold w =>
      cases v with
      | hold v =>
        congr 1
        exact ih w v (fun i hi => h (i+1) (Nat.succ_le_succ hi))
      | step hv v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        exact (hv.ne he).elim
    | step hw w =>
      cases v with
      | hold v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        exact (hw.ne he.symm).elim
      | step hv v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        cases he
        congr 1
        exact ih w v (fun i hi => h (i+1) (Nat.succ_le_succ hi))

end HoldingWalk
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

def segmentCenter (J : ℕ) : Fin (J+J+1) := ⟨J,by omega⟩

def segmentPositivePositions (J : ℕ) (s : Fin (J+J+1) → V) : Fin (J+1) → V :=
  fun i => s ⟨J+i.val,by omega⟩

def positiveStem (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) :
    HoldingWalk H J (s (segmentCenter J)) (s (Fin.last (J+J))) :=
  HoldingWalk.fromPositions J (segmentPositivePositions J s) (fun i => hs ⟨J+i.val,by omega⟩)

theorem positiveStem_mass (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ))
    (P : V → V → ℝ) (a : ℝ) (hP : ∀ x y, H.Adj x y → P x y = a) :
    (positiveStem H J s hs).mass P = a^J :=
  HoldingWalk.mass_fromPositions P a hP J _ _

theorem orbitSegment_consecutive (G : BondGraph V E) (J : ℕ) (γ s : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hs : s ∈ segmentOrbit G γ) :
    ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (s i.castSucc) (s i.succ) :=
  fun i => segmentOrbit_adj G γ s hs _ _ (hγ i)

 

def escapeLabelRaw (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    HoldingWalk (openSimpleGraph G Set.univ) ((J+L)+J)
      (ξ.first (segmentCenter J)) (ξ.last (segmentCenter J)) :=
  (positiveStem _ J ξ.first (orbitSegment_consecutive G J γ ξ.first hγ ξ.first_mem)).append
    (ξ.middle.append (positiveStem _ J ξ.last
      (orbitSegment_consecutive G J γ ξ.last hγ ξ.last_mem)).reverse)

theorem escapeLabelRaw_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    (escapeLabelRaw G J L m γ hγ ξ).mass (walkKernel G hloc a) =
      a^(J+J)*ξ.middle.mass (walkKernel G hloc a) := by
  simp only [escapeLabelRaw,HoldingWalk.mass_append,HoldingWalk.mass_reverse _ (walkKernel_symmetric G hloc a),
    positiveStem_mass _ _ _ _ _ a (fun _ _ h => walkKernel_step G hloc a h),pow_add]
  ring

theorem escapeLabelRaw_middle_position (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (i : ℕ) (hi : i ≤ L) :
    (escapeLabelRaw G J L m γ hγ ξ).position (J+i) = ξ.middle.position i := by
  rw [escapeLabelRaw,HoldingWalk.position_append_right,HoldingWalk.position_append_left _ _ i hi]

end IntrinsicVisibleBlocks
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace RawFrom
variable {H : SimpleGraph V}

 
theorem ext_positions {k : ℕ} {x : V} (w v : RawFrom H k x)
    (h : ∀ i : ℕ, i ≤ k → w.2.position i = v.2.position i) : w = v := by
  rcases w with ⟨y,w⟩
  rcases v with ⟨z,v⟩
  have he : y = z := by simpa only [HoldingWalk.position_length] using h k le_rfl
  subst z
  exact Sigma.ext rfl (heq_of_eq (HoldingWalk.ext_positions w v h))

theorem pairwise_disjoint_position_indicators {k : ℕ} {x : V} (f : ℕ → V)
    {w v : RawFrom H k x}
    (hw : ∀ i : ℕ, i ≤ k → w.2.position i = f i)
    (hv : ∀ i : ℕ, i ≤ k → v.2.position i = f i) : w = v :=
  ext_positions w v (fun i hi => (hw i hi).trans (hv i hi).symm)

end RawFrom

 

theorem finite_single_fiber_weight_bound {α : Type*} [Fintype α]
    (μ : α → ℝ) (B : α → Prop) [DecidablePred B] (C : ℝ) (hC : 0 ≤ C)
    (hunique : ∀ a b, B a → B b → a = b) (hbound : ∀ a, B a → μ a ≤ C) :
    (∑ a, if B a then μ a else 0) ≤ C := by
  classical
  by_cases hh : ∃ a, B a
  · obtain ⟨a,ha⟩ := hh
    calc
      _ = μ a := by
        rw [Finset.sum_eq_single a]
        · exact ite_eq_left ha
        · intro b _ hba
          exact ite_eq_right (fun hb => hba (hunique b a hb ha))
        · simp
      _ ≤ C := hbound a ha
  · simpa only [not_exists.mp hh,ite_false,Finset.sum_const_zero] using hC

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootedRawProjection
attribute [local instance] Classical.propDecidable Classical.decEq

def rootedEscapeLabelRaw (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact ⟨ξ.last (segmentCenter J),escapeLabelRaw G J L m γ hγ ξ⟩

theorem rootedEscapeLabelRaw_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    (rootedEscapeLabelRaw G J L m γ hγ x ξ).2.mass (walkKernel G hloc a) =
      a^(J+J)*ξ.1.middle.mass (walkKernel G hloc a) := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact escapeLabelRaw_mass G hloc a J L m γ hγ ξ

theorem rootedEscapeLabelRaw_middle_position (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (i : ℕ) (hi : i ≤ L) :
    (rootedEscapeLabelRaw G J L m γ hγ x ξ).2.position (J+i) = ξ.1.middle.position i := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact escapeLabelRaw_middle_position G J L m γ hγ ξ i hi

theorem rootedEscapeLabelRaw_fiber_middle_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (ha : 0 < a) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x)
    (hw : rootedEscapeLabelRaw G J L m γ hγ x ξ = w) :
    ξ.1.middle.mass (walkKernel G hloc a) = w.2.mass (walkKernel G hloc a)/a^(J+J) := by
  apply (eq_div_iff (ne_of_gt (pow_pos ha _))).mpr
  rw [mul_comm,←rootedEscapeLabelRaw_mass G hloc a J L m γ hγ x ξ,hw]

theorem rootedEscapeLabelRaw_fiber_middle_positions (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x)
    (hw : rootedEscapeLabelRaw G J L m γ hγ x ξ = w) :
    ∀ i : ℕ, i ≤ L → ξ.1.middle.position i = w.2.position (J+i) := by
  intro i hi
  rw [←rootedEscapeLabelRaw_middle_position G J L m γ hγ x ξ i hi,hw]

end RootedRawProjection
end Percolation

 
namespace Percolation
section FiniteFiberDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_auxiliary_event_bound {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hs : ∑ a, μ a = 1)
    (B : α → Prop) (c : ℝ) (hc : 0 ≤ c) :
    (∑ a, if B a then c*μ a else 0) ≤ c := by
  calc
    _ ≤ ∑ a, c*μ a := Finset.sum_le_sum (fun a _ => by
      split_ifs; exact le_rfl; exact mul_nonneg hc (hμ a))
    _ = c := by rw [←Finset.mul_sum,hs,mul_one]

 

theorem finite_nested_unique_fiber_bound {β : Type*} [Fintype β]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    {T : (b : β) → γ b → Type*} [∀ b c, Fintype (T b c)]
    (μ : β → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (ν : (b : β) → (c : γ b) → T b c → ℝ) (hν : ∀ b c t, 0 ≤ ν b c t)
    (hs : ∀ b c, ∑ t, ν b c t = 1)
    (B : (b : β) → (c : γ b) → T b c → Prop)
    (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hcard : ∀ b, (Fintype.card (γ b) : ℝ) ≤ N)
    (hunique : ∀ b c t b' c' t', B b c t → B b' c' t' → b = b')
    (hbound : ∀ b c t, B b c t → μ b ≤ C) :
    (∑ b, ∑ c, ∑ t, if B b c t then μ b*ν b c t else 0) ≤ N*C := by
  by_cases hh : ∃ b c t, B b c t
  · obtain ⟨b,c,t,hb⟩ := hh
    have he : (∑ b', ∑ c', ∑ t', if B b' c' t' then μ b'*ν b' c' t' else 0) =
        ∑ c', ∑ t', if B b c' t' then μ b*ν b c' t' else 0 := by
      apply Finset.sum_eq_single b
      · intro b' _ hne
        apply Finset.sum_eq_zero
        intro c' _
        apply Finset.sum_eq_zero
        intro t' _
        exact ite_eq_right (fun hb' => hne (hunique b' c' t' b c t hb' hb))
      · simp
    rw [he]
    calc
      _ ≤ ∑ _c : γ b, μ b := Finset.sum_le_sum (fun c' _ =>
        finite_auxiliary_event_bound (ν b c') (hν b c') (hs b c') (B b c') (μ b) (hμ b))
      _ = (Fintype.card (γ b) : ℝ)*μ b := by simp
      _ ≤ N*C := mul_le_mul (hcard b) (hbound b c t hb) (hμ b) hN
  · have hz : ∀ b c t, ¬B b c t := by simpa only [not_exists] using hh
    simp only [hz,ite_false,Finset.sum_const_zero]
    exact mul_nonneg hN hC

end FiniteFiberDomination
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CodeMiddleIdentities
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem labelFromCode_middle_position (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) (i : ℕ) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.middle.position i =
      c.2.1.2.position i := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

theorem labelFromCode_middle_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.middle.mass P =
      c.2.1.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

end CodeMiddleIdentities
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralFiberEstimate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rooted_code_single_anchor_fiber_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (s : segmentAnchors G hloc γ n hdiam (segmentCenter J) x)
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val (Fin.last (J+J))),
      ∑' h : segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) mid.1,
        ∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val 0) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val 0),
          if rootedEscapeLabelRaw G J L m γ hγ x
              (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
                ⟨s,mid,h,tails⟩) = w then
            mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
              tails.2.2.mass (walkKernel G hloc a) else 0) ≤
      ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
        (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  simp only [tsum_fintype,mul_assoc]
  convert finite_nested_unique_fiber_bound
    (β := RawFrom (openSimpleGraph G Set.univ) L (s.val (Fin.last (J+J))))
    (γ := fun mid => segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) mid.1)
    (T := fun _ h => RawFrom (openSimpleGraph G Set.univ) m (s.val 0) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val 0))
    (fun mid => mid.2.mass (walkKernel G hloc a))
    (fun mid => mid.2.mass_nonneg _ hK)
    (fun _ _ tails => tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a))
    (fun _ _ tails => mul_nonneg (tails.1.2.mass_nonneg _ hK) (tails.2.2.mass_nonneg _ hK)) ?_
    (fun mid h tails => rootedEscapeLabelRaw G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) = w)
    (((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ))
    (w.2.mass (walkKernel G hloc a)/a^(J+J)) ?_ ?_ ?_ ?_ ?_ using 1
  · apply Finset.sum_congr rfl
    intro mid _
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro tails _
    split_ifs <;> rfl
  · intro mid h
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    simpa only [tsum_fintype,mul_one] using congrArg₂ (fun r s : ℝ => r*s)
      (rawFrom_probability_sum G hloc a m (s.val 0))
      (rawFrom_probability_sum G hloc a m (h.val 0))
  · positivity
  · exact div_nonneg (w.2.mass_nonneg _ hK) (pow_nonneg ha.le _)
  · intro mid
    rw [Fintype.card_coe,segmentAnchors_card_eq_indicator G hloc γ n hdiam (Fin.last (J+J)) mid.1]
    split_ifs
    · exact le_rfl
    · exact_mod_cast Nat.zero_le _
  · intro mid h tails mid' h' tails' hh hh'
    apply RawFrom.ext_positions
    intro i hi
    have he := rootedEscapeLabelRaw_fiber_middle_positions G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) w hh i hi
    have he' := rootedEscapeLabelRaw_fiber_middle_positions G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid',h',tails'⟩) w hh' i hi
    have hm := labelFromCode_middle_position G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩ i
    have hm' := labelFromCode_middle_position G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid',h',tails'⟩ i
    exact hm.symm.trans (he.trans (he'.symm.trans hm'))
  · intro mid h tails hh
    have he := rootedEscapeLabelRaw_fiber_middle_mass G hloc a ha J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) w hh
    have hm := labelFromCode_middle_mass G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x (walkKernel G hloc a) ⟨s,mid,h,tails⟩
    exact (hm.symm.trans he).le

end LiteralFiberEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralProjectionDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem rooted_label_raw_fiber_mass_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if rootedEscapeLabelRaw G J L m γ hγ x ξ = w then ξ.1.mass (walkKernel G hloc a) else 0) ≤
      ((segmentAnchors G hloc γ n hdiam (segmentCenter J) x).card : ℝ) *
      ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
        (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let R := rootedLabelEquiv G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  calc
    _ ≤ ∑' _s : segmentAnchors G hloc γ n hdiam (segmentCenter J) x,
        ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
          (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
      apply (summable_of_hasFiniteSupport (Set.toFinite _)).tsum_le_tsum _
        (summable_of_hasFiniteSupport (Set.toFinite _))
      intro s
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      conv_lhs => arg 1; ext mid; rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      exact rooted_code_single_anchor_fiber_bound G hloc a ha hK J L m γ hγ n hdiam x s w
    _ = _ := by
      simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

end LiteralProjectionDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedProjection
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tsum_indicator_div {α : Type*} (f : α → ℝ) (B : α → Prop) [DecidablePred B] (d : ℝ) :
    (∑' a, if B a then f a/d else 0) = (∑' a, if B a then f a else 0)/d := by
  rw [←tsum_div_const]
  apply tsum_congr
  intro a
  split_ifs <;> simp

theorem rooted_label_raw_projection_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if rootedEscapeLabelRaw G J L m γ hγ x ξ = w then
        escapeLabelProbability G hloc a γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) ≤
      w.2.mass (walkKernel G hloc a)/(a^(J+J)*q) := by
  have hN (i : Fin (J+J+1)) : 0 < ((segmentAnchors G hloc γ n hdiam i (γ i)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i (γ i)).mpr
      (by exact ⟨Equiv.refl V,Equiv.refl E,(fun e => by simp),rfl⟩))
  have hQ := hq.trans_le hqle
  have hA := pow_pos ha (J+J)
  have hm := w.2.mass_nonneg (walkKernel G hloc a) hK
  simp only [escapeLabelProbability,tsum_indicator_div]
  have hb := rooted_label_raw_fiber_mass_bound G hloc a ha hK J L m γ hγ n hdiam x w
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam (segmentCenter J) x hx] at hb
  apply (div_le_div_of_nonneg_right hb (mul_nonneg (mul_nonneg (hN (segmentCenter J)).le (hN (Fin.last (J+J))).le) hQ.le)).trans
  calc
    _ = w.2.mass (walkKernel G hloc a)/
        (a^(J+J)*segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J)))) := by
      field_simp [(hN (segmentCenter J)).ne', (hN (Fin.last (J+J))).ne']
    _ ≤ _ := div_le_div_of_nonneg_left hm (mul_pos hA hq) (mul_le_mul_of_nonneg_left hqle hA.le)

end NormalizedProjection
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section SuffixCollisionOperator

theorem operator_pow_norm_le (P : Hilbert V →L[ℂ] Hilbert V) (k : ℕ) : ‖P^k‖ ≤ ‖P‖^k := by
  cases k with
  | zero => simpa only [pow_zero,ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
  | succ k => exact norm_pow_le' P (Nat.succ_pos k)

 

theorem positive_rows_collision_hasSum (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re*(matrixCoeff B y z).re)
      (matrixCoeff (A*star B) x y).re := by
  simpa only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_re] using
    hA.mul_hasSum (star B) x y

theorem positive_rows_collision_bound (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (x y : V) :
    (∑' z, (matrixCoeff A x z).re*(matrixCoeff B y z).re) ≤ ‖A‖*‖B‖ := by
  rw [(positive_rows_collision_hasSum A B hA x y).tsum_eq]
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (A*star B) x y).trans _)
  have hs : ‖star B‖ = ‖B‖ := ContinuousLinearMap.adjoint.norm_map B
  simpa only [hs] using norm_mul_le A (star B)

theorem walk_suffix_collision_operator_bound (P H : Hilbert V →L[ℂ] Hilbert V)
    (hP : PositiveRealMatrix P) (C : ℝ) (hH : ‖H‖ ≤ C) (l L : ℕ) (x y : V) :
    (∑' z, (matrixCoeff (P^l) x z).re*(matrixCoeff (P^L*H) y z).re) ≤
      C*‖P‖^(l+L) := by
  calc
    _ ≤ ‖P^l‖*‖P^L*H‖ := positive_rows_collision_bound _ _ (hP.pow l) x y
    _ ≤ ‖P‖^l*(‖P‖^L*C) := mul_le_mul (operator_pow_norm_le P l)
      ((norm_mul_le _ _).trans (mul_le_mul (operator_pow_norm_le P L) hH (norm_nonneg H)
        (pow_nonneg (norm_nonneg P) L))) (norm_nonneg _) (pow_nonneg (norm_nonneg P) l)
    _ = _ := by rw [pow_add]; ring

end SuffixCollisionOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchored_position_expectation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (L : ℕ) (x z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L x,
      mid.2.mass (walkKernel G hloc a)*anchoredPositionKernel G hloc γ n hdiam ep j mid.1 z) =
      (matrixCoeff (P^L*H) x z).re := by
  change RawFrom.integral (walkKernel G hloc a) L x
    (fun y => anchoredPositionKernel G hloc γ n hdiam ep j y z) = _
  rw [raw_integral_operator G hloc a P hpos hP]
  simpa only [hH,Complex.ofReal_re] using ((hpos.pow L).mul_hasSum H x z).tsum_eq

 

theorem raw_tail_anchored_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (C : ℝ) (hHC : ‖H‖ ≤ C) (l m L : ℕ) (hlm : l ≤ m) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) ≤
      C*‖P‖^(l+L) := by
  simp only [raw_anchored_position_expectation G hloc a γ n hdiam ep j P H hpos hP hH]
  rw [raw_position_integral G hloc a l m hlm x (fun z => (matrixCoeff (P^L*H) y z).re),
    raw_integral_operator G hloc a P hpos hP]
  exact walk_suffix_collision_operator_bound P H hpos C hHC l L x y

end ActualSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem raw_tail_anchored_collision_uniform (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (l m L : ℕ) (hlm : l ≤ m) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) ≤
      Real.sqrt c*‖P‖^(l+L) := by
  obtain ⟨H,hH,hHn⟩ := exists_anchoredPositionOperator_uniform G hloc root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j
  exact raw_tail_anchored_collision_bound G hloc a γ n hdiam ep j P H hpos hP hH
    (Real.sqrt c) hHn l m L hlm x y

end UniformSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GlobalAnchorDenominator
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem anchoredPositionKernel_global_denominator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I) (x z : V) :
    (∑ h : segmentAnchors G hloc γ n hdiam ep x,
      if h.val j = z then ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ)⁻¹ else 0) =
      anchoredPositionKernel G hloc γ n hdiam ep j x z := by
  rw [Finset.sum_coe_sort _ (fun h : I → V => if h j = z then
    ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ)⁻¹ else 0)]
  by_cases hx : x ∈ vertexOrbit G (γ ep)
  · unfold anchoredPositionKernel
    rw [segmentAnchors_card_on_orbit G hloc γ n hdiam ep x hx]
    apply Finset.sum_congr rfl
    intro h _
    simp only [eq_comm]
  · have hz := ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep x).not.mpr hx)
    have he := Finset.not_nonempty_iff_eq_empty.mp hz
    simp only [anchoredPositionKernel,he,Finset.sum_empty]

theorem finite_geometric_sum_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (M : ℕ) :
    (∑ i : Fin M, ρ^i.val) ≤ 1/(1-ρ) := by
  simpa only [Nat.zero_le,ite_true,pow_zero] using finite_geometric_cutoff_bound ρ hρ hρ1 0 M

end GlobalAnchorDenominator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralSuffixExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_tail_anchor_collision_identity (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (l m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if tail.2.position l = h.val j then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro tail _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mid _
  rw [←anchoredPositionKernel_global_denominator G hloc γ n hdiam ep j mid.1 (tail.2.position l)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : tail.2.position l = h.val j
  · simp only [ite_eq_left hh,ite_eq_left hh.symm,div_eq_mul_inv,mul_assoc]
  · simp only [ite_eq_right hh,ite_eq_right (Ne.symm hh),mul_zero]

end LiteralSuffixExperiment
end Percolation

 
namespace Percolation
section NestedFiniteUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_threefold_event_union {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    (μ : (a : α) → (b : β) → γ b → ℝ) (hμ : ∀ a b c, 0 ≤ μ a b c)
    (B : (a : α) → (b : β) → γ b → δ → Prop) :
    (∑ a, ∑ b, ∑ c, if ∃ d, B a b c d then μ a b c else 0) ≤
      ∑ d, ∑ a, ∑ b, ∑ c, if B a b c d then μ a b c else 0 := by
  have hh := finite_nonnegative_event_union
    (fun ξ : α × Sigma γ => μ ξ.1 ξ.2.1 ξ.2.2)
    (fun ξ => hμ ξ.1 ξ.2.1 ξ.2.2)
    (fun ξ : α × Sigma γ => B ξ.1 ξ.2.1 ξ.2.2)
  simpa only [Fintype.sum_prod_type,Fintype.sum_sigma] using hh

end NestedFiniteUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WholeSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι S : Type*} [Fintype I] [Fintype ι] [Fintype S]

 

theorem raw_tail_whole_suffix_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I) (j : S → I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hρ : ‖P‖ < 1) (m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if ∃ ij : Fin (m+1) × S, tail.2.position ij.1.val = h.val (j ij.2) then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L/(1-‖P‖) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  simp only [tsum_fintype]
  have hu := finite_threefold_event_union
    (α := RawFrom (openSimpleGraph G Set.univ) m x)
    (β := RawFrom (openSimpleGraph G Set.univ) L y)
    (γ := fun mid => segmentAnchors G hloc γ n hdiam ep mid.1)
    (δ := Fin (m+1) × S)
    (fun tail mid _ => tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
      (segmentAnchors G hloc γ n hdiam ep (γ ep)).card)
    (fun tail mid _ => div_nonneg (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)) (Nat.cast_nonneg _))
    (fun tail _ h ij => tail.2.position ij.1.val = h.val (j ij.2))
  apply hu.trans
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin (m+1), ∑ _s : S, Real.sqrt c*‖P‖^(i.val+L) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro s _
      have hh := raw_tail_anchored_collision_uniform G hloc a root weight Γ hΓ htr hw hw1 hcov c hc hmin
        γ n hdiam ep (j s) P hpos hP i.val m L (by omega) x y
      rw [←raw_tail_anchor_collision_identity G hloc a γ n hdiam ep (j s) i.val m L x y] at hh
      simpa only [tsum_fintype] using hh
    _ = ((Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L)*(∑ i : Fin (m+1), ‖P‖^i.val) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_add,←Finset.mul_sum,←Finset.sum_mul]
      ring
    _ ≤ ((Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L)*(1/(1-‖P‖)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_sum_bound ‖P‖ (norm_nonneg P) hρ (m+1)) (by positivity)
    _ = _ := by ring

end WholeSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualAnchorPointTest
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem raw_anchor_position_identity (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (L : ℕ) (y z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if h.val j = z then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      mid.2.mass (walkKernel G hloc a)*anchoredPositionKernel G hloc γ n hdiam ep j mid.1 z) := by
  apply tsum_congr
  intro mid
  rw [←anchoredPositionKernel_global_denominator G hloc γ n hdiam ep j mid.1 z,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp only [div_eq_mul_inv,mul_zero]

theorem raw_anchor_point_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (C : ℝ) (hC : ‖H‖ ≤ C) (L : ℕ) (y z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if h.val j = z then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤ C*‖P‖^L := by
  rw [raw_anchor_position_identity G hloc a γ n hdiam ep j L y z,
    raw_anchored_position_expectation G hloc a γ n hdiam ep j P H hpos hP hH L y z]
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (P^L*H) y z).trans _)
  calc
    _ ≤ ‖P^L‖*‖H‖ := norm_mul_le _ _
    _ ≤ ‖P‖^L*C := mul_le_mul (operator_pow_norm_le P L) hC (norm_nonneg _) (pow_nonneg (norm_nonneg P) L)
    _ = _ := mul_comm _ _

end ActualAnchorPointTest
end Percolation

end OAI
