import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SignedCoproductGridGrade
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductCoassociative

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
  ElementaryPositivity.LinearDetection DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
noncomputable def globalTripleGradeLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ) :
    TensorGrade (unitalSourceTensorFiltration a c η hc θ d.val e.val)
      (unitalSourceFiltration a c η hc θ f.val) W →ₗ[ℚ]
      (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)⊗[ℚ]UnitalShuffle a c η hc θ :=
  tensorGradeLift (unitalSourceTensorFiltration a c η hc θ d.val e.val)
    (unitalSourceFiltration a c η hc θ f.val) (unitalSourceTensorFiltration_antitone a c η hc θ d.val e.val)
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (globalTensorGradeInclusion a c η hc θ d e)
    (fun w=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,w)) W

noncomputable def globalTripleGradeRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ) :
    TensorGrade (unitalSourceFiltration a c η hc θ d.val)
      (unitalSourceTensorFiltration a c η hc θ e.val f.val) W →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ](UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :=
  tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
    (unitalSourceTensorFiltration a c η hc θ e.val f.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceTensorFiltration_antitone a c η hc θ e.val f.val)
    (fun w=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,w))
    (globalTensorGradeInclusion a c η hc θ e f) W

lemma globalTripleGrade_assoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : TensorGrade (unitalSourceTensorFiltration a c η hc θ d.val e.val)
      (unitalSourceFiltration a c η hc θ f.val) W) :
    globalTripleGradeRight a c η hc θ d e f W
      (tensorGradeAssoc (unitalSourceFiltration a c η hc θ d.val)
        (unitalSourceFiltration a c η hc θ e.val) (unitalSourceFiltration a c η hc θ f.val) W x)=
      TensorProduct.assoc ℚ _ _ _ (globalTripleGradeLeft a c η hc θ d e f W x) :=
  tensorGradeLift_assoc _ _ _ (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ e.val)
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u))
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,u))
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,u)) W x

lemma globalTripleGrade_left_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ (d.val+e.val) f.val W) :
    globalTripleGradeLeft a c η hc θ d e f W
      (unitalTensorCoproductLeft a c η hc θ d.val e.val f.val (d.property.compatible e.property) W x)=
      tensorGradeLift (unitalSourceFiltration a c η hc θ (d.val+e.val))
        (unitalSourceFiltration a c η hc θ f.val)
        (unitalSourceFiltration_antitone a c η hc θ (d.val+e.val))
        (unitalSourceFiltration_antitone a c η hc θ f.val)
        (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
          (unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u))
        (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,u)) W x := by
  have H := tensorGradeLift_map_natural
    (unitalSourceFiltration a c η hc θ (d.val+e.val))
    (unitalSourceFiltration a c η hc θ f.val)
    (unitalSourceTensorFiltration a c η hc θ d.val e.val)
    (unitalSourceFiltration a c η hc θ f.val)
    (unitalSourceFiltration_antitone a c η hc θ (d.val+e.val))
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (unitalSourceTensorFiltration_antitone a c η hc θ d.val e.val)
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (unitalSeparationConstant a c η hc d.val e.val (d.property.compatible e.property))
    LinearMap.id
    (unitalSeparationConstant_filtered a c η hc θ d.val e.val (d.property.compatible e.property))
    (fun _ _ h=>h)
    (globalTensorGradeInclusion a c η hc θ d e)
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,u)) W x
  simp only [gradeMap_id] at H
  exact H

lemma globalTripleGrade_right_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val (e.val+f.val) W) :
    globalTripleGradeRight a c η hc θ d e f W
      (unitalTensorCoproductRight a c η hc θ d.val e.val f.val (e.property.compatible f.property) W x)=
      tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
        (unitalSourceFiltration a c η hc θ (e.val+f.val))
        (unitalSourceFiltration_antitone a c η hc θ d.val)
        (unitalSourceFiltration_antitone a c η hc θ (e.val+f.val))
        (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u))
        (fun u=>(globalTensorGradeInclusion a c η hc θ e f u).comp
          (unitalGradeCoproduct a c η hc θ e.val f.val (e.property.compatible f.property) u)) W x := by
  have H := tensorGradeLift_map_natural
    (unitalSourceFiltration a c η hc θ d.val)
    (unitalSourceFiltration a c η hc θ (e.val+f.val))
    (unitalSourceFiltration a c η hc θ d.val)
    (unitalSourceTensorFiltration a c η hc θ e.val f.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ (e.val+f.val))
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceTensorFiltration_antitone a c η hc θ e.val f.val)
    LinearMap.id
    (unitalSeparationConstant a c η hc e.val f.val (e.property.compatible f.property))
    (fun _ _ h=>h)
    (unitalSeparationConstant_filtered a c η hc θ e.val f.val (e.property.compatible f.property))
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u))
    (globalTensorGradeInclusion a c η hc θ e f) W x
  simp only [gradeMap_id] at H
  exact H

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev LeftSlopeTriple (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :=
  Σ s : SlopeSplit c η hc θ d,SlopeSplit c η hc θ (left s.val)
abbrev RightSlopeTriple (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :=
  Σ s : SlopeSplit c η hc θ d,SlopeSplit c η hc θ (right s.val)
abbrev SlopeTriple (c η : I → ℝ) (_hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :=
  {p : (I → ℕ) × (I → ℕ) × (I → ℕ) //
    (p.1+p.2.1)+p.2.2=d ∧ OnSlopeOrZero c η θ p.1 ∧
      OnSlopeOrZero c η θ p.2.1 ∧ OnSlopeOrZero c η θ p.2.2}

def leftTripleView (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : LeftSlopeTriple c η hc θ d) : SlopeTriple c η hc θ d :=
  ⟨(left p.2.val,right p.2.val,right p.1.val),by
    exact ⟨by rw [left_add_right,left_add_right],p.2.property.1,p.2.property.2,p.1.property.2⟩⟩
def rightTripleView (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : RightSlopeTriple c η hc θ d) : SlopeTriple c η hc θ d :=
  ⟨(left p.1.val,left p.2.val,right p.2.val),by
    exact ⟨by rw [add_assoc,left_add_right,left_add_right],p.1.property.1,p.2.property.1,p.2.property.2⟩⟩

omit [DecidableEq I] in
lemma leftTripleView_injective (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    Function.Injective (leftTripleView c η hc θ d) := by
  rintro ⟨s,t⟩ ⟨s',t'⟩ h
  have h1 : left t.val=left t'.val := congrArg (fun p=>p.val.1) h
  have h2 : right t.val=right t'.val := congrArg (fun p=>p.val.2.1) h
  have hs : s=s' := by
    apply Subtype.ext
    apply DimensionSplit.ext
    rw [←left_add_right t.val,←left_add_right t'.val,h1,h2]
  subst s'
  have ht : t=t' := Subtype.ext (DimensionSplit.ext h1)
  subst t'
  rfl

omit [DecidableEq I] in
lemma rightTripleView_injective (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    Function.Injective (rightTripleView c η hc θ d) := by
  rintro ⟨s,t⟩ ⟨s',t'⟩ h
  have h1 : left s.val=left s'.val := congrArg (fun p=>p.val.1) h
  have h2 : left t.val=left t'.val := congrArg (fun p=>p.val.2.1) h
  have hs : s=s' := Subtype.ext (DimensionSplit.ext h1)
  subst s'
  have ht : t=t' := Subtype.ext (DimensionSplit.ext h2)
  subst t'
  rfl

omit [DecidableEq I] in
lemma leftTripleView_surjective (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    Function.Surjective (leftTripleView c η hc θ d) := by
  rintro ⟨⟨a,b,f⟩,hs,ha,hb,hf⟩
  let s : SlopeSplit c η hc θ d :=
    ⟨ofPair (a+b) f hs,by simpa only [left_ofPair,right_ofPair] using And.intro (ha.add hc hb) hf⟩
  let t : SlopeSplit c η hc θ (a+b) :=
    ⟨ofPair a b (rfl : a+b=a+b),by simpa only [left_ofPair,right_ofPair] using And.intro ha hb⟩
  refine ⟨⟨s,t⟩,?_⟩
  apply Subtype.ext
  change (left (ofPair a b rfl),right (ofPair a b rfl),right (ofPair (a+b) f hs))=(a,b,f)
  simp only [left_ofPair,right_ofPair]

omit [DecidableEq I] in
lemma rightTripleView_surjective (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    Function.Surjective (rightTripleView c η hc θ d) := by
  rintro ⟨⟨a,b,f⟩,hs,ha,hb,hf⟩
  have hs' : a+(b+f)=d := (add_assoc a b f).symm.trans hs
  let s : SlopeSplit c η hc θ d :=
    ⟨ofPair a (b+f) hs',by simpa only [left_ofPair,right_ofPair] using And.intro ha (hb.add hc hf)⟩
  have hr : b+f=right s.val := (right_ofPair a (b+f) hs').symm
  let t : SlopeSplit c η hc θ (right s.val) :=
    ⟨ofPair b f hr,by simpa only [left_ofPair,right_ofPair] using And.intro hb hf⟩
  refine ⟨⟨s,t⟩,?_⟩
  apply Subtype.ext
  change (left (ofPair a (b+f) hs'),left (ofPair b f hr),right (ofPair b f hr))=(a,b,f)
  simp only [left_ofPair,right_ofPair]

noncomputable def leftTripleEquiv (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    LeftSlopeTriple c η hc θ d ≃ SlopeTriple c η hc θ d :=
  Equiv.ofBijective (leftTripleView c η hc θ d)
    ⟨leftTripleView_injective c η hc θ d,leftTripleView_surjective c η hc θ d⟩
noncomputable def rightTripleEquiv (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    RightSlopeTriple c η hc θ d ≃ SlopeTriple c η hc θ d :=
  Equiv.ofBijective (rightTripleView c η hc θ d)
    ⟨rightTripleView_injective c η hc θ d,rightTripleView_surjective c η hc θ d⟩

def leftTripleBuild (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) : LeftSlopeTriple c η hc θ d :=
  ⟨⟨ofPair (p.val.1+p.val.2.1) p.val.2.2 p.property.1,
      by simpa only [left_ofPair,right_ofPair] using
        And.intro (p.property.2.1.add hc p.property.2.2.1) p.property.2.2.2⟩,
    ⟨ofPair p.val.1 p.val.2.1 rfl,
      by simpa only [left_ofPair,right_ofPair] using
        And.intro p.property.2.1 p.property.2.2.1⟩⟩

def rightTripleBuild (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) : RightSlopeTriple c η hc θ d :=
  ⟨⟨ofPair p.val.1 (p.val.2.1+p.val.2.2)
      ((add_assoc _ _ _).symm.trans p.property.1),
      by simpa only [left_ofPair,right_ofPair] using
        And.intro p.property.2.1 (p.property.2.2.1.add hc p.property.2.2.2)⟩,
    ⟨ofPair p.val.2.1 p.val.2.2 (by rw [right_ofPair]),
      by simpa only [left_ofPair,right_ofPair] using
        And.intro p.property.2.2.1 p.property.2.2.2⟩⟩

omit [DecidableEq I] in
lemma leftTripleView_build (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) :
    leftTripleView c η hc θ d (leftTripleBuild c η hc θ d p)=p := by
  apply Subtype.ext
  simp only [leftTripleView,leftTripleBuild,left_ofPair,right_ofPair]

omit [DecidableEq I] in
lemma rightTripleView_build (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) :
    rightTripleView c η hc θ d (rightTripleBuild c η hc θ d p)=p := by
  apply Subtype.ext
  simp only [rightTripleView,rightTripleBuild,left_ofPair,right_ofPair]

omit [DecidableEq I] in
lemma leftTripleBuild_view (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : LeftSlopeTriple c η hc θ d) :
    leftTripleBuild c η hc θ d (leftTripleView c η hc θ d p)=p :=
  leftTripleView_injective c η hc θ d (leftTripleView_build c η hc θ d _)

omit [DecidableEq I] in
lemma rightTripleBuild_view (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (p : RightSlopeTriple c η hc θ d) :
    rightTripleBuild c η hc θ d (rightTripleView c η hc θ d p)=p :=
  rightTripleView_injective c η hc θ d (rightTripleView_build c η hc θ d _)

lemma sum_slopeTriple {A : Type*} [AddCommMonoid A]
    (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ)
    (F : SlopeTriple c η hc θ d → A) :
    ∑ s : SlopeSplit c η hc θ d,∑ t : SlopeSplit c η hc θ (left s.val),
      F (leftTripleView c η hc θ d ⟨s,t⟩)=
    ∑ s : SlopeSplit c η hc θ d,∑ t : SlopeSplit c η hc θ (right s.val),
      F (rightTripleView c η hc θ d ⟨s,t⟩) := by
  rw [←Fintype.sum_sigma',←Fintype.sum_sigma']
  let e := (leftTripleEquiv c η hc θ d).trans (rightTripleEquiv c η hc θ d).symm
  exact Fintype.sum_equiv e _ _ (fun p=>by
    apply congrArg F
    exact ((rightTripleEquiv c η hc θ d).apply_symm_apply
      (leftTripleEquiv c η hc θ d p)).symm)
end ElementaryPositivity.RawShuffle

end

end OAI
