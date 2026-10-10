import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.LeadingIndex
import OAI.Combinatorics.Chromatic.Shuffle.TensorFiltration
import OAI.Combinatorics.Chromatic.Shuffle.Degree
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree
lemma restrictionTest_homogeneous (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hs : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (ℓ : ℤ)
    (hf : f∈gradeB a (SlopeArithmetic.slope c η) T.dim ℓ)
    (k : T.Degrees) (z : T.Centers →₀ ℕ)
    (hz : T.totalDegree k+Finsupp.weight (fun _=>(1:ℤ)) z≠ℓ) :
    restrictionTest a c η hc θ T hs rfl k z f=0 := by
  classical
  induction T generalizing ℓ with
  | leaf d =>
    have hzs : z=Finsupp.single () (z ()) := by apply Finsupp.ext; intro x; cases x; simp
    rw [hzs]
    rw [restrictionTest_leaf_coeff]
    have hh:=taylorB_coeff_graded a (SlopeArithmetic.slope c η) d f ℓ hf (z ())
    have hne : k≠ℓ-(z () : ℤ) := by
      rw [hzs,Finsupp.weight_single] at hz
      change (k : ℤ)+(z () : ℤ) • (1 : ℤ)≠ℓ at hz
      simp only [zsmul_eq_mul, mul_one] at hz
      change (k : ℤ)+(z () : ℤ)≠ℓ at hz
      intro h
      apply hz
      rw [h,sub_add_cancel]
    rw [←(mem_gradeB_iff a _ d (ℓ-(z ():ℤ)) _).mp hh,componentB_componentB,ite_eq_right hne]
    rfl
  | node l r ihl ihr =>
    let z₁:=z.comapDomain Sum.inl Sum.inl_injective.injOn
    let z₂:=z.comapDomain Sum.inr Sum.inr_injective.injOn
    have hzs : z₁.sumElim z₂=z := Finsupp.comapDomain_sumElim_comapDomain z
    rw [←hzs] at hz ⊢
    rw [totalWeight_sumElim] at hz
    rw [restrictionTest_node]
    let μ:=SlopeArithmetic.slope c η
    let Rl:=restrictionTest a c η hc θ l hs.1 rfl k.1 z₁
    let Rr:=restrictionTest a c η hc θ r hs.2 rfl k.2 z₂
    let x:=RawShuffle.restrictionB a c η hc
      ((slope_dim c η hc hs.1).trans (slope_dim c η hc hs.2).symm) (firstCut l.dim r.dim) f
    let F:=TensorProduct.map Rl Rr
    change F x=0
    obtain ⟨s,_,he⟩:=componentTensor_finite_decomposition a μ (.node (.leaf l.dim) (.leaf r.dim)) x
    change (∑ mn∈s,TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x)=x at he
    have hterm : ∀ mn∈s,F (TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x)=0 := by
      intro mn _
      by_cases hm : mn.1+mn.2=ℓ
      · have hsep : l.totalDegree k.1+Finsupp.weight (fun _=>(1:ℤ)) z₁≠mn.1 ∨
            r.totalDegree k.2+Finsupp.weight (fun _=>(1:ℤ)) z₂≠mn.2 := by
          change l.totalDegree k.1+r.totalDegree k.2+_≠ℓ at hz
          by_contra hh
          push Not at hh
          apply hz
          rw [←hm,←hh.1,←hh.2]
          ring
        generalize x=y
        induction y using TensorProduct.inductionOn with
        | tmul g h =>
          change Rl (componentB a μ l.dim mn.1 g) ⊗ₜ[ℚ] Rr (componentB a μ r.dim mn.2 h)=0
          rcases hsep with hl|hr
          · have hzero:=ihl hs.1 (componentB a μ l.dim mn.1 g) mn.1 ⟨g,rfl⟩ k.1 z₁ hl
            rw [show Rl (componentB a μ l.dim mn.1 g)=0 from hzero,TensorProduct.zero_tmul]
          · have hzero:=ihr hs.2 (componentB a μ r.dim mn.2 h) mn.2 ⟨h,rfl⟩ k.2 z₂ hr
            rw [show Rr (componentB a μ r.dim mn.2 h)=0 from hzero,TensorProduct.tmul_zero]
        | add g h hg hh => simp only [map_add,hg,hh,add_zero]
      · have hzero:=RawShuffle.restrictionB_graded a c η hc
          ((slope_dim c η hc hs.1).trans (slope_dim c η hc hs.2).symm)
          (firstCut l.dim r.dim) f ℓ hf mn.1 mn.2 hm
        change TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x=0 at hzero
        rw [hzero,map_zero]
    rw [←he,map_sum]
    exact Finset.sum_eq_zero hterm

lemma restrictionTest_component (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (hs : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (ℓ : ℤ) (k : T.Degrees) (z : T.Centers →₀ ℕ) :
    restrictionTest a c η hc θ T hs rfl k z (componentB a (SlopeArithmetic.slope c η) T.dim ℓ f)=
      if ℓ=T.totalDegree k+Finsupp.weight (fun _=>(1:ℤ)) z
      then restrictionTest a c η hc θ T hs rfl k z f else 0 := by
  classical
  split_ifs with h
  · obtain ⟨s,hs',he⟩:=componentB_finite_decomposition a (SlopeArithmetic.slope c η) T.dim f
    let R:=restrictionTest a c η hc θ T hs rfl k z
    change R (componentB a (SlopeArithmetic.slope c η) T.dim ℓ f)=R f
    have hsum : (∑ i∈s,R (componentB a (SlopeArithmetic.slope c η) T.dim i f))=
        R (componentB a (SlopeArithmetic.slope c η) T.dim ℓ f) := by
      apply Finset.sum_eq_single ℓ
      · intro i _ hi
        exact restrictionTest_homogeneous a c η hc θ T hs _ i ⟨f,rfl⟩ k z (by omega)
      · intro hl
        rw [hs' ℓ hl,map_zero]
    rw [←hsum,←map_sum,he]
  · exact restrictionTest_homogeneous a c η hc θ T hs _ ℓ ⟨f,rfl⟩ k z (Ne.symm h)
end SplitTree

lemma sourceFiltration_component_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    componentB a (SlopeArithmetic.slope c η) d ℓ f∈sourceFiltration a c η hc θ d W := by
  intro T ho hs hd k z hw
  subst d
  rw [SplitTree.restrictionTest_component]
  split_ifs
  · exact hf T ho hs rfl k z hw
  · rfl
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def derivativeS (d : I → ℕ) : Module.End ℚ (S d) :=
  ((Polynomial.lcoeff (S d) 1).restrictScalars ℚ).comp (taylorS d).toLinearMap

omit [Fintype I] [DecidableEq I] in
lemma derivativeS_val (d : I → ℕ) (f : S d) :
    (derivativeS d f).val=D f.val := by
  have h:=congrArg (fun p : Polynomial (MvPolynomial (Σi,Fin (d i)) ℚ)=>p.coeff 1)
    (map_taylorS d f)
  simpa [derivativeS] using h

noncomputable def derivativeB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Module.End ℚ (B a μ d) :=
  ((Polynomial.lcoeff (B a μ d) 1).restrictScalars ℚ).comp (taylorB a μ d).toLinearMap

lemma derivativeB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    derivativeB a μ d (quotientAlg a μ d f)=quotientAlg a μ d (derivativeS d f) := by
  change (taylorB a μ d (quotientAlg a μ d f)).coeff 1=_
  rw [taylorB_mk,Polynomial.coeff_map]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma derivativeS_pow_val (d : I → ℕ) (n : ℕ) (f : S d) :
    ((derivativeS d^n) f).val=(D.toLinearMap^n) f.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ',Module.End.mul_apply,derivativeS_val,ih]
    rfl

lemma derivativeB_pow_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (n : ℕ) (f : S d) :
    (derivativeB a μ d^n) (quotientAlg a μ d f)=quotientAlg a μ d ((derivativeS d^n) f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,ih,derivativeB_mk]

theorem derivativeB_locally_nilpotent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) : ∃ N : ℕ,(derivativeB a μ d^N) f=0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    refine ⟨(taylor f.val).natDegree+1,?_⟩
    change (derivativeB a μ d^_) (quotientAlg a μ d f)=0
    rw [derivativeB_pow_mk]
    have h : (derivativeS d^((taylor f.val).natDegree+1)) f=0 := by
      apply Subtype.ext
      rw [derivativeS_pow_val,locally_nilpotent_D]
      rfl
    rw [h,map_zero]

lemma derivativeB_mul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f g : B a μ d) :
    derivativeB a μ d (f*g)=derivativeB a μ d f*g+f*derivativeB a μ d g := by
  change (taylorB a μ d (f*g)).coeff 1=_
  rw [map_mul,Polynomial.mul_coeff_one,taylorB_coeff_zero,taylorB_coeff_zero]
  exact add_comm _ _

lemma derivativeB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    derivativeB a (SlopeArithmetic.slope c η) d f∈sourceFiltration a c η hc θ d W := by
  apply polynomial_coeff_mem (sourceFiltration a c η hc θ d W) (taylorB a _ d f)
  intro t
  rw [taylorB_eval]
  exact sourceFiltration_translation_mem a c η hc θ d W f hf t

noncomputable def gradeDerivative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Module.End ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearFiltration.map (sourceFiltration a c η hc θ d W)
    (sourceFiltration a c η hc θ d (W+1))
    (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1))
    (derivativeB a (SlopeArithmetic.slope c η) d)
    (fun f hf=>derivativeB_filtered a c η hc θ d W f hf)
    (fun f hf=>derivativeB_filtered a c η hc θ d (W+1) f hf)

end ElementaryPositivity.RawShuffle

end

end OAI
