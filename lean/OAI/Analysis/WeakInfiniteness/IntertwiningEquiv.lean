import Mathlib
import OAI.Analysis.WeakInfiniteness.IntertwiningConstruction

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter Topology TopologicalSpace

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma intertwiningStages_dist_limit (φ : A →⋆ₙₐ[ℂ] B) (hi : Isometry φ)
    (h : FiniteIntertwining φ) (d : ℕ → A) (hd : DenseRange d) (b : ℕ → B)
    (N : ℕ) (a : A) (ha : a ∈ (intertwiningStages φ h d b N).tests) :
    dist ((intertwiningStages φ h d b N).map φ a)
      (starHomLimit (fun n => (intertwiningStages φ h d b n).map φ)
        (intertwiningStages_cauchy φ hi h d hd b) a) ≤ 2*(1/2 : ℝ)^N := by
  let f := fun n => (intertwiningStages φ h d b n).map φ
  let hf := intertwiningStages_cauchy φ hi h d hd b
  have hs : Summable (fun n => (1/2 : ℝ)^(N+n)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).comp_injective
      (add_right_injective N)
  have ht : Tendsto (fun n => N+n) atTop atTop := by
    simpa only [Nat.add_comm] using (tendsto_add_atTop_nat N)
  have hc := (starHomLimitFun_tendsto f hf a).comp ht
  have hb : ∀ n,dist (f (N+n) a) (f (N+(n+1)) a) ≤ (1/2 : ℝ)^(N+n) := by
    intro n
    exact (intertwiningStages_step φ h d b (N+n)).2.2.1 a
      (intertwiningStages_tests_mono φ h d b (Nat.le_add_right _ _) ha)
  have he := dist_le_tsum_of_dist_le_of_tendsto₀ _ hb hs hc
  change dist (f N a) (starHomLimitFun f hf a) ≤ _
  calc
    dist (f N a) (starHomLimitFun f hf a) ≤ ∑' n,(1/2 : ℝ)^(N+n) := by
      simpa only [Nat.add_zero] using he
    _ = (1/2 : ℝ)^N * ∑' n,(1/2 : ℝ)^n := by
      simp only [pow_add,tsum_mul_left]
    _ = 2*(1/2 : ℝ)^N := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
      ring

lemma intertwiningStages_dense_limit (φ : A →⋆ₙₐ[ℂ] B) (hi : Isometry φ)
    (h : FiniteIntertwining φ) (d : ℕ → A) (hd : DenseRange d)
    (b : ℕ → B) (hb : DenseRange b) :
    DenseRange (starHomLimit (fun n => (intertwiningStages φ h d b n).map φ)
      (intertwiningStages_cauchy φ hi h d hd b)) := by
  let f := fun n => (intertwiningStages φ h d b n).map φ
  let hf := intertwiningStages_cauchy φ hi h d hd b
  let g := starHomLimit f hf
  have ht : Tendsto (fun n => 2*(1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)) :
      Tendsto (fun n => 2*(1/2 : ℝ)^n) atTop (𝓝 (2*0)))
  have hcl : Set.range b ⊆ closure (Set.range g) := by
    rintro _ ⟨i,rfl⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
    let n := max i N
    obtain ⟨a,ha,hea⟩ := (intertwiningStages_step φ h d b n).2.2.2 i (le_max_left _ _)
    have hel := intertwiningStages_dist_limit φ hi h d hd b (n+1) a ha
    refine ⟨g a,⟨a,rfl⟩,?_⟩
    have htri := dist_triangle (b i) (f (n+1) a) (g a)
    rw [dist_comm (b i) (f (n+1) a)] at htri
    have he : (1/2 : ℝ)^n + 2*(1/2 : ℝ)^(n+1) = 2*(1/2 : ℝ)^n := by
      rw [pow_succ]; ring
    have hle : dist (b i) (g a) ≤ 2*(1/2 : ℝ)^n := by
      calc
        dist (b i) (g a) ≤ dist (f (n+1) a) (b i) + dist (f (n+1) a) (g a) := htri
        _ ≤ (1/2 : ℝ)^n + 2*(1/2 : ℝ)^(n+1) := add_le_add hea hel
        _ = _ := he
    exact hle.trans_lt (hN n (le_max_right _ _))
  intro y
  exact closure_minimal hcl isClosed_closure (hb y)

def finiteIntertwiningStarEquiv [SeparableSpace A] [SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (hi : Isometry φ) (h : FiniteIntertwining φ) : A ≃⋆ₐ[ℂ] B :=
  starEquivOfConvergentIsometries
    (fun n => (intertwiningStages φ h (denseSeq A) (denseSeq B) n).map φ)
    (intertwiningStages_cauchy φ hi h (denseSeq A) (denseRange_denseSeq A) (denseSeq B))
    (intertwiningStages_isometry φ hi h (denseSeq A) (denseSeq B))
    (intertwiningStages_dense_limit φ hi h (denseSeq A) (denseRange_denseSeq A)
      (denseSeq B) (denseRange_denseSeq B))

end

end WeakPureInfiniteness
end

end OAI
