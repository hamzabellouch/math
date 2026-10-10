import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CrossScalar
import OAI.Combinatorics.Chromatic.Shuffle.RestrictionTestHomogeneity
import OAI.Combinatorics.Chromatic.Walls.LinearFiltrationOperators

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def variableSum (d : I → ℕ) : S d := by
  classical
  refine ⟨∑ v : Σi,Fin (d i),X v,?_⟩
  intro σ
  simp only [map_sum,rename_X]
  exact Equiv.sum_comp (packAction (fun i=>Fin (d i)) σ) _

omit [DecidableEq I] in
lemma derivativeS_variableSum (d : I → ℕ) :
    derivativeS d (variableSum d)=(Fintype.card (Σi,Fin (d i)) : S d) := by
  classical
  apply Subtype.ext
  rw [derivativeS_val]
  change D (∑ v : Σi,Fin (d i),X v)=_
  simp only [map_sum,D_X,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma variables_nonempty_of_ne_zero (d : I → ℕ) (hd : d≠0) : Nonempty (Σi,Fin (d i)) := by
  classical
  by_contra h
  apply hd
  funext i
  by_contra hi
  exact h ⟨⟨i,⟨0,Nat.pos_of_ne_zero hi⟩⟩⟩

noncomputable def meanS (d : I → ℕ) : S d :=
  (Fintype.card (Σi,Fin (d i)) : ℚ)⁻¹ • variableSum d

omit [DecidableEq I] in
lemma derivativeS_meanS (d : I → ℕ) (hd : d≠0) : derivativeS d (meanS d)=1 := by
  have :=variables_nonempty_of_ne_zero d hd
  have hn : (Fintype.card (Σi,Fin (d i)) : ℚ)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [meanS,map_smul,derivativeS_variableSum]
  change _ • (algebraMap ℚ (S d) (Fintype.card (Σi,Fin (d i))))=1
  rw [Algebra.smul_def,←map_mul,inv_mul_cancel₀ hn,map_one]

noncomputable def meanB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) : B a μ d :=
  quotientAlg a μ d (meanS d)

lemma derivativeB_meanB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (hd : d≠0) :
    derivativeB a μ d (meanB a μ d)=1 := by
  rw [meanB,derivativeB_mk,derivativeS_meanS d hd,map_one]

noncomputable def meanMultiplyB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Module.End ℚ (B a μ d) := Algebra.lmul ℚ _ (meanB a μ d)

lemma derivativeB_meanMultiply_weyl (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (hd : d≠0) (f : B a μ d) :
    derivativeB a μ d (meanMultiplyB a μ d f)=
      meanMultiplyB a μ d (derivativeB a μ d f)+f := by
  change derivativeB a μ d (meanB a μ d*f)=meanB a μ d*derivativeB a μ d f+f
  rw [derivativeB_mul,derivativeB_meanB a μ d hd,one_mul,add_comm]

lemma meanMultiplyB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    meanMultiplyB a (SlopeArithmetic.slope c η) d f∈sourceFiltration a c η hc θ d W := by
  change meanB a (SlopeArithmetic.slope c η) d*f∈_
  rw [mul_comm]
  exact sourceFiltration_mul_mem a c η hc θ d W f _ hf

noncomputable def gradeMeanMultiply (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Module.End ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearFiltration.map (sourceFiltration a c η hc θ d W)
    (sourceFiltration a c η hc θ d (W+1))
    (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1))
    (meanMultiplyB a (SlopeArithmetic.slope c η) d)
    (fun f hf=>meanMultiplyB_filtered a c η hc θ d W f hf)
    (fun f hf=>meanMultiplyB_filtered a c η hc θ d (W+1) f hf)

lemma gradeDerivative_meanMultiply_weyl (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (W : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    gradeDerivative a c η hc θ d W (gradeMeanMultiply a c η hc θ d W f)=
      gradeMeanMultiply a c η hc θ d W (gradeDerivative a c η hc θ d W f)+f := by
  exact LinearFiltration.map_weyl _ _ _ _ _ _ _ _
    (derivativeB_meanMultiply_weyl a (SlopeArithmetic.slope c η) d hd) f

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus ElementaryPositivity.CoefficientIdeals
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree

def IsProper : SplitTree I → Prop
  | .leaf _ => False
  | .node _ _ => True
end SplitTree

noncomputable def properSourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Submodule ℚ (B a (SlopeArithmetic.slope c η) d) where
  carrier := {f | ∀ (T : SplitTree I),T.IsOrderedList → T.IsProper →
    ∀ (hT : T.OnSlope c η θ) (h : T.dim=d) k z,
      2*T.totalDegree k+T.doubleShift a<W → restrictionTest a c η hc θ T hT h k z f=0}
  zero_mem' := by
    intro T ho hp hT h k z hw
    exact (restrictionTest a c η hc θ T hT h k z).map_zero
  add_mem' := by intro f g hf hg T ho hp hT h k z hw; rw [map_add,hf T ho hp hT h k z hw,hg T ho hp hT h k z hw,add_zero]
  smul_mem' := by intro r f hf T ho hp hT h k z hw; rw [map_smul,hf T ho hp hT h k z hw,smul_zero]

lemma sourceFiltration_le_proper (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W≤properSourceFiltration a c η hc θ d W := by
  intro f hf T ho _ hT h k z hw
  exact hf T ho hT h k z hw

lemma properSourceFiltration_translation_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) (t : ℚ) :
    translationB a (SlopeArithmetic.slope c η) d t f∈properSourceFiltration a c η hc θ d W := by
  intro T hT hp hs hd k z hw
  subst d
  let P:=SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k
  have h0 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs f)=0 := by
    ext s
    rw [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
    exact hf T hT hp hs rfl k s hw
  have h1 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs
      (translationB a (SlopeArithmetic.slope c η) T.dim t f))=0 := by
    apply eq_of_evalRat
    intro v
    rw [map_zero,evalRat_mapLinear,SplitTree.centeredRestrictionB_translate_eval,
      ←evalRat_mapLinear,h0,map_zero]
  have he:=congrArg (fun polynomial=>AddMonoidAlgebra.coeff polynomial z) h1
  change P ((SplitTree.centeredRestrictionB a c η hc θ T hs
    (translationB a (SlopeArithmetic.slope c η) T.dim t f)).coeff z)=0
  simpa only [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using he

lemma properSourceFiltration_mul_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (x y : B a (SlopeArithmetic.slope c η) d)
    (hx : x∈properSourceFiltration a c η hc θ d W) :
    x*y∈properSourceFiltration a c η hc θ d W := by
  intro T hT hp hs hd k z hw
  subst d
  let ρ:=SplitTree.centeredRestrictionB a c η hc θ T hs
  let J:=SplitTree.degreeCutIdeal a (SlopeArithmetic.slope c η) T W
  have hxc : ∀ m,(ρ x).coeff m∈J := by
    intro m j hj
    exact hx T hT hp hs rfl j m hj
  have hxy:=coeff_mul_mem J (ρ x) (ρ y) hxc z
  change SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k ((ρ (x*y)).coeff z)=0
  rw [map_mul]
  exact hxy k hw

lemma proper_next_iff_leading_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : sourceFiltration a c η hc θ d W) :
    f.val∈properSourceFiltration a c η hc θ d (W+1) ↔
      ∀ j : LeadingIndex c η θ a d W,j.tree.IsProper → leadingRawMap a c η hc θ d W f j=0 := by
  constructor
  · intro h j hp
    exact h j.tree j.ordered hp j.onSlope j.dimension j.degree j.center (by rw [j.weight]; omega)
  · intro h T ho hp hT hd k z hw
    by_cases hl : 2*T.totalDegree k+T.doubleShift a<W
    · exact f.property T ho hT hd k z hl
    · have he : 2*T.totalDegree k+T.doubleShift a=W := by omega
      exact h ⟨T,ho,hT,hd,k,z,he⟩ hp

end ElementaryPositivity.RawShuffle

end

end OAI
