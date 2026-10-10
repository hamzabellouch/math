import OAI.Analysis.TreePotential.DualCoordinates

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
open scoped Classical

lemma rootPath_root (n : ℕ) : rootPath (root n)=lp.single 2 (root n) (1:ℝ) := by
  have he : pathNodes (root n)={root n} := by
    ext s
    simp [mem_pathNodes_iff,root,Subtype.ext_iff]
  simp only [rootPath,he,Finset.sum_singleton]

/-- The sharp root normalization for the quadratic cost, distinct from L_n. -/
theorem quadraticBlockCost_root (n : ℕ) :
    quadraticBlockCost n (lp.single 2 (root n) (1:ℝ))=1/Real.sqrt 2 := by
  apply le_antisymm _ (quadraticBlockCost_single_bounds (root n)).1
  let e : TreeHilbert n := lp.single 2 (root n) (1:ℝ)
  let μ : L1Mass (Tree n) := lp.single 1 (root n) (1/2:ℝ)
  have hn : ‖e‖=1 := by simp [e,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
  have hm : ‖μ‖=(1/2:ℝ) := by simp [μ,lp.norm_single (by norm_num : (0:ℝ≥0∞)<1)]
  have hout : (1/2:ℝ) • e+pathSynthesis n μ=e := by
    rw [pathSynthesis_single,rootPath_root]
    change (1/2:ℝ) • e+(1/2:ℝ) • e=e
    module
  have hh := quadraticCost_representation_le (pathSynthesis n) ((1/2:ℝ) • e) μ
  rw [hout] at hh
  change quadraticBlockCost n e ≤ pairCost ((1/2:ℝ) • e) μ at hh
  apply hh.trans
  rw [pairCost,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),hn,hm]
  norm_num only [mul_one]
  have h2 : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have h22 : 0< Real.sqrt (2:ℝ) := by positivity
  have hs : Real.sqrt (((1/2:ℝ))^2+(1/2)^2)^2=(1/2:ℝ)^2+(1/2)^2 := Real.sq_sqrt (by positivity)
  apply (le_div_iff₀ h22).mpr
  nlinarith [Real.sqrt_nonneg (((1/2:ℝ))^2+(1/2)^2),
    sq_nonneg (Real.sqrt (((1/2:ℝ))^2+(1/2)^2)*Real.sqrt 2-1)]

theorem quadratic_finite_support_dense :
    Dense (ForestCoordinates.finiteNodeSpace (fun n => quadraticBlockHilbertEquiv (n+1)) : Set QuadraticOuter) :=
  ForestCoordinates.dense_finiteNodeSpace _

namespace TreeCalculus
/-- Completeness, separability and infinite dimension for every literal test-norm completion. -/


theorem four_completed_space (r : Bool) (k : QuadraticKind) :
    CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
    TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
    ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k)) := by
  exact ⟨inferInstance,inferInstance,testCompletion_infiniteDimensional _⟩
end TreeCalculus
end BoundedTreePotentials

namespace BoundedTreePotentials.CostHeads

/-- A uniform positive e_t independent of the unit center; the finite-codimensional tail
may depend on the center. -/

theorem quadratic_uniform_maximum {t : ℝ} (ht : 0< t) :
    ∃ e : ℝ,0< e ∧ ∀ x : QuadraticOuter,‖x‖=1 →
      ∃ F : ClosedFiniteCodim QuadraticOuter,∀ u : QuadraticOuter,
        u ∈ F.space → ‖u‖=1 → 1+e ≤ max ‖x+t • u‖ ‖x-t • u‖ := by
  let b := Real.sqrt (1+t^2/16)-1
  have hb : 0< b := by
    have hh := Real.sq_sqrt (show 0≤1+t^2/16 by positivity)
    have hs := Real.sqrt_nonneg (1+t^2/16)
    dsimp [b]
    nlinarith [sq_pos_of_pos ht]
  refine ⟨b/2,by positivity,?_⟩
  intro x hx
  obtain ⟨F,hF⟩ := quadratic_completed_tail_bound x hx ht (show 0< b/2 by positivity)
  refine ⟨F,?_⟩
  intro u hu hun
  have hh := hF u hu hun.ge
  change b-b/2 ≤ (‖x+t • u‖+‖x-t • u‖)/2-1 at hh
  linarith [le_max_left ‖x+t • u‖ ‖x-t • u‖,le_max_right ‖x+t • u‖ ‖x-t • u‖]

end BoundedTreePotentials.CostHeads

namespace BoundedTreePotentials.Segments

/-- The segment-start midpoint consequence. -/
theorem start_unit_sphere_bound (x : StartSpace) (hx : ‖x‖=1)
    {t ε : ℝ} (ht : 0< t) (hε : 0<ε) :
    ∃ F : ClosedFiniteCodim StartSpace,
      ((Real.sqrt (1+t^2/64)-ε : ℝ) : EReal) ≤
        ⨅ y : {y : StartSpace // y ∈ F.space ∧ ‖y‖=1},
          ((max ‖x+t • y.val‖ ‖x-t • y.val‖ : ℝ) : EReal) := by
  obtain ⟨F,hF⟩ := start_completed_tail_bound x hx ht hε
  refine ⟨F,le_iInf fun y => ?_⟩
  apply EReal.coe_le_coe_iff.mpr
  have hh := hF y.val y.property.1 y.property.2.ge
  linarith

end BoundedTreePotentials.Segments

end

end OAI
