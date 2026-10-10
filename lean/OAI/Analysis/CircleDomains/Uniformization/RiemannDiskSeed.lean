module

public import Mathlib.Analysis.Complex.BranchLogRoot
import all Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.Analysis.Complex.Schwarz

namespace OAI

/-! A normalized nonconstant disk embedding from the existing square-root
construction. This is the initial competitor for extremal circularization. -/
public section

open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

structure NormalizedDiskEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f U
  injective : InjOn f U
  mapsTo : MapsTo f U (ball 0 1)
  at_base : f a=0

lemma exists_normalized_disk_embedding {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ deriv f a ≠ 0 := by
  obtain ⟨f,hmap,hinj,hd⟩ := Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero hU hc hproper
  let g : ℂ → ℂ := fun z => (f z-f a)/2
  have hdiff : DifferentiableOn ℂ f U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hd z hz)).differentiableWithinAt
  have hg : NormalizedDiskEmbedding U a g := by
    refine ⟨hdiff.sub_const (f a) |>.div_const 2,?_,?_,?_⟩
    · intro x hx y hy he
      apply hinj hx hy
      change (f x-f a)/2=(f y-f a)/2 at he
      have hh := (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp he
      linear_combination hh
    · intro z hz
      apply mem_ball_zero_iff.mpr
      change ‖(f z-f a)/2‖<1
      rw [norm_div]
      have hza : ‖f z‖<1 := mem_ball_zero_iff.mp (hmap hz)
      have haa : ‖f a‖<1 := mem_ball_zero_iff.mp (hmap ha)
      have hb := norm_sub_le (f z) (f a)
      norm_num
      linarith
    · dsimp [g]
      simp
  refine ⟨g,hg,?_⟩
  have hdg : HasDerivAt g (deriv f a/2) a :=
    ((differentiableAt_of_deriv_ne_zero (hd a ha)).hasDerivAt.sub_const (f a)).div_const 2
  rw [hdg.deriv]
  exact div_ne_zero (hd a ha) (by norm_num)

lemma normalized_disk_derivative_bound {U : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : NormalizedDiskEmbedding U a f) {r : ℝ} (hr : 0<r) (hball : ball a r ⊆ U) :
    ‖deriv f a‖≤1/r := by
  apply Complex.norm_deriv_le_div_of_mapsTo_ball (hf.holomorphic.mono hball) _ hr
  intro z hz
  rw [hf.at_base]
  exact ball_subset_closedBall (hf.mapsTo (hball hz))

end CircleDomainRigidity

end
end

end OAI
