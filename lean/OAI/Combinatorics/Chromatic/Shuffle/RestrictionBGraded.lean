import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Interaction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem restrictionB_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hs : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (k : ℤ)
    (hf : f∈gradeB a (SlopeArithmetic.slope c η) T.dim k) (j : T.Degrees)
    (hj : T.totalDegree j≠k) :
    componentTensor a (SlopeArithmetic.slope c η) T j (restrictionB a c η hc θ T hs f)=0 := by
  classical
  induction T generalizing k with
  | leaf d =>
    change componentB a (SlopeArithmetic.slope c η) d j f=0
    rw [← (mem_gradeB_iff a _ d k f).mp hf,componentB_componentB,ite_eq_right hj]
  | node l r ihl ihr =>
    let μ:=SlopeArithmetic.slope c η
    let Rl := (restrictionB a c η hc θ l hs.1).toLinearMap
    let Rr := (restrictionB a c η hc θ r hs.2).toLinearMap
    let Cl := componentTensor a μ l j.1
    let Cr := componentTensor a μ r j.2
    let x:=RawShuffle.restrictionB a c η hc
      ((slope_dim c η hc hs.1).trans (slope_dim c η hc hs.2).symm) (firstCut l.dim r.dim) f
    let F:=TensorProduct.map Cl Cr ∘ₗ TensorProduct.map Rl Rr
    change F x=0
    obtain ⟨s,hout,he⟩ := componentTensor_finite_decomposition a μ (.node (.leaf l.dim) (.leaf r.dim)) x
    change (∑ mn∈s,TensorProduct.map (componentB a μ l.dim mn.1)
      (componentB a μ r.dim mn.2) x)=x at he
    have hterm : ∀ mn∈s,F (TensorProduct.map (componentB a μ l.dim mn.1)
        (componentB a μ r.dim mn.2) x)=0 := by
      intro mn hmn
      by_cases hm : mn.1+mn.2=k
      · have hsep : l.totalDegree j.1≠mn.1 ∨ r.totalDegree j.2≠mn.2 := by
          by_contra hh
          push Not at hh
          apply hj
          change l.totalDegree j.1+r.totalDegree j.2=k
          rw [hh.1,hh.2,hm]
        generalize x=y
        induction y using TensorProduct.inductionOn with
        | tmul g h =>
          change Cl (Rl (componentB a μ l.dim mn.1 g)) ⊗ₜ[ℚ]
            Cr (Rr (componentB a μ r.dim mn.2 h))=0
          rcases hsep with hl|hr
          · have hzero := ihl hs.1 (componentB a μ l.dim mn.1 g) mn.1
              (⟨g,rfl⟩) j.1 hl
            rw [show Cl (Rl (componentB a μ l.dim mn.1 g))=0 from hzero,TensorProduct.zero_tmul]
          · have hzero := ihr hs.2 (componentB a μ r.dim mn.2 h) mn.2
              (⟨h,rfl⟩) j.2 hr
            rw [show Cr (Rr (componentB a μ r.dim mn.2 h))=0 from hzero,TensorProduct.tmul_zero]
        | add y z hy hz => simp only [map_add,hy,hz,add_zero]
      · have hzero := RawShuffle.restrictionB_graded a c η hc
          ((slope_dim c η hc hs.1).trans (slope_dim c η hc hs.2).symm)
          (firstCut l.dim r.dim) f k hf mn.1 mn.2 hm
        change TensorProduct.map (componentB a μ l.dim mn.1)
          (componentB a μ r.dim mn.2) x=0 at hzero
        rw [hzero,map_zero]
    calc
      F x = F (∑ mn∈s,TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x) :=
        congrArg F he.symm
      _ = 0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
