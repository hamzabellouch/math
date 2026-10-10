import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LightPoint
import OAI.Analysis.MatrixSigning.Realization.ScalarRealization
import OAI.Combinatorics.ThinTrees.Duality

namespace OAI

/-! Concave alternative. -/

section

namespace AlgorithmicThinTrees.ConvexAlternative
noncomputable section
open Finset
open scoped Classical
variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [Fintype I]

theorem compact_concave_alternative (C : Set E) (hcompact : IsCompact C)
    (hne : C.Nonempty) (hconvex : Convex ℝ C) (f : I → E → ℝ)
    (hcontinuous : ∀i, ContinuousOn (f i) C)
    (hconcave : ∀i, ConcaveOn ℝ C (f i))
    (hinfeasible : ¬∃x ∈ C, ∀i, 0 ≤ f i x) :
    ∃ε : ℝ, 0 < ε ∧ ∃w : I → ℝ, (∀i, 0 ≤ w i) ∧ (∑i, w i)=1 ∧
      ∀x ∈ C, (∑i, w i*f i x) ≤ -ε := by
  let b : E → ℝ := fun x => ∑i, max 0 (-f i x)
  have hbcont : ContinuousOn b C := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.sup (hcontinuous i).neg
  have hbpos : ∀x ∈ C, 0 < b x := by
    intro x hx
    have he : ∃i, f i x < 0 := by
      by_contra hh
      apply hinfeasible
      exact ⟨x,hx,fun i => le_of_not_gt (fun hi => hh ⟨i,hi⟩)⟩
    obtain ⟨i,hi⟩ := he
    apply sum_pos' (fun _ _ => le_max_left _ _)
    exact ⟨i,mem_univ i,(neg_pos.mpr hi).trans_le (le_max_right _ _)⟩
  obtain ⟨x₀,hx₀,hmin⟩ := hcompact.exists_isMinOn hne hbcont
  let ε := b x₀/((Fintype.card I:ℝ)+1)
  have hε : 0 < ε := div_pos (hbpos x₀ hx₀) (by positivity)
  have heq : ((Fintype.card I:ℝ)+1)*ε=b x₀ := by
    dsimp [ε]
    exact mul_div_cancel₀ _ (by positivity)
  have hno : ¬∃x ∈ C, ∀i, (-f i x)-ε < 0 := by
    rintro ⟨x,hx,hh⟩
    have hbx : b x ≤ (Fintype.card I:ℝ)*ε := by
      calc
        _ ≤ ∑i : I, ε := sum_le_sum (fun i _ => max_le hε.le (by linarith [hh i]))
        _ = _ := by simp
    have hminx := (isMinOn_iff.mp hmin) x hx
    nlinarith only [hbx,hminx,heq,hε]
  have hc : ∀i, ConvexOn ℝ C (fun x => -f i x-ε) := by
    intro i
    refine ⟨hconvex,?_⟩
    intro x hx y hy a d ha hd had
    have hh := (hconcave i).2 hx hy ha hd had
    change a*f i x+d*f i y ≤ f i (a • x+d • y) at hh
    change -f i (a • x+d • y)-ε ≤ a*(-f i x-ε)+d*(-f i y-ε)
    nlinarith only [hh,congrArg (fun z : ℝ => z*ε) had]
  obtain ⟨w,hw,hws,hbound⟩ := StrongThinTree.Duality.convex_alternative C hconvex hne
    (fun i x => -f i x-ε) hc hno
  refine ⟨ε,hε,w,hw,hws,?_⟩
  intro x hx
  have hh := hbound x hx
  simp only [mul_sub,mul_neg,sum_sub_distrib,sum_neg_distrib,←sum_mul,hws,one_mul] at hh
  linarith

end
end AlgorithmicThinTrees.ConvexAlternative
end

end OAI
