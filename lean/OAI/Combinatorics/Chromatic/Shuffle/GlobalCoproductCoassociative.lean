import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalCoproductCocommutative
import OAI.Combinatorics.Chromatic.Shuffle.GlobalTripleGradeInclusion
import OAI.Combinatorics.Chromatic.Shuffle.GlobalCoproductIteration

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalTripleCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (p : SlopeTriple c η hc θ k.1.val) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ](UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :=
  (globalTripleGradeRight a c η hc θ ⟨p.val.1,p.property.2.1⟩
    ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ k.2).comp
    ((unitalTensorCoproductRight a c η hc θ p.val.1 p.val.2.1 p.val.2.2
      (p.property.2.2.1.compatible p.property.2.2.2) k.2).comp
      ((unitalGradeCoproduct a c η hc θ p.val.1 (p.val.2.1+p.val.2.2)
        (p.property.2.1.compatible (p.property.2.2.1.add hc p.property.2.2.2)) k.2).comp
        (unitalGradeCast a c η hc θ
          ((add_assoc _ _ _).symm.trans p.property.1).symm rfl).toLinearMap))

noncomputable def globalLeftTripleOutput (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (d e f : slopeDimensions c η hc θ) (hp : d.val+e.val+f.val=k.1.val)
    (x : unitalComponent a c η hc θ k) :=
    TensorProduct.assoc ℚ _ _ _ (globalTripleGradeLeft a c η hc θ d e f k.2
      (unitalTensorCoproductLeft a c η hc θ d.val e.val f.val (d.property.compatible e.property) k.2
        (unitalGradeCoproduct a c η hc θ (d.val+e.val) f.val
          ((d.property.add hc e.property).compatible f.property) k.2
          (unitalGradeCast a c η hc θ hp.symm rfl x))))

noncomputable def globalLeftTripleCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :=
    globalLeftTripleOutput a c η hc θ k ⟨p.val.1,p.property.2.1⟩
      ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ p.property.1 x

lemma globalTripleCoproduct_left_explicit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (globalTripleGradeLeft a c η hc θ ⟨p.val.1,p.property.2.1⟩
        ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ k.2
        (unitalTensorCoproductLeft a c η hc θ p.val.1 p.val.2.1 p.val.2.2
          (p.property.2.1.compatible p.property.2.2.1) k.2
          (unitalGradeCoproduct a c η hc θ (p.val.1+p.val.2.1) p.val.2.2
            ((p.property.2.1.add hc p.property.2.2.1).compatible p.property.2.2.2) k.2
            (unitalGradeCast a c η hc θ p.property.1.symm rfl x))))=
      globalTripleCoproduct a c η hc θ k p x := by
  have H := unitalGradeCoproduct_coassociative a c η hc θ hχ
    p.val.1 p.val.2.1 p.val.2.2 p.property.2.1 p.property.2.2.1 p.property.2.2.2
    k.2 (unitalGradeCast a c η hc θ p.property.1.symm rfl x)
  have HH := congrArg (globalTripleGradeRight a c η hc θ ⟨p.val.1,p.property.2.1⟩
    ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ k.2) H
  rw [globalTripleGrade_assoc] at HH
  rw [unitalGradeCast_trans] at HH
  exact HH

lemma globalTripleCoproduct_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalLeftTripleCoproduct a c η hc θ k p x=
      globalTripleCoproduct a c η hc θ k p x := by
  dsimp only [globalLeftTripleCoproduct,globalLeftTripleOutput]
  exact globalTripleCoproduct_left_explicit a c η hc θ hχ k p x

lemma unitalGradeCast_refl (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    unitalGradeCast a c η hc θ (rfl : d=d) (rfl : W=W)=LinearEquiv.refl ℚ _ := rfl

lemma unitalGradeCoproduct_comp_cast_refl (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (h : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ) :
    (unitalGradeCoproduct a c η hc θ d e h W).comp
      (unitalGradeCast a c η hc θ (rfl : d+e=d+e) (rfl : W=W)).toLinearMap=
      unitalGradeCoproduct a c η hc θ d e h W := rfl

lemma globalTensorGrade_coproduct_family_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) :
    (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
      ((unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u).comp
        (unitalGradeCast a c η hc θ (rfl : d.val+e.val=d.val+e.val) (rfl : u=u)).toLinearMap) :
      (u : ℤ) → FGrade (unitalSourceFiltration a c η hc θ (d.val+e.val)) u →ₗ[ℚ]
        UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)=
    (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
      (unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u)) := rfl

lemma globalTripleGrade_left_cast_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ (d.val+e.val) f.val W) :
    TensorProduct.assoc ℚ _ _ _
      (tensorGradeLift (unitalSourceFiltration a c η hc θ (d.val+e.val))
        (unitalSourceFiltration a c η hc θ f.val)
        (unitalSourceFiltration_antitone a c η hc θ (d.val+e.val))
        (unitalSourceFiltration_antitone a c η hc θ f.val)
        (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
          ((unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u).comp
            (unitalGradeCast a c η hc θ rfl rfl).toLinearMap))
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,v)) W x)=
    TensorProduct.assoc ℚ _ _ _ (globalTripleGradeLeft a c η hc θ d e f W
      (unitalTensorCoproductLeft a c η hc θ d.val e.val f.val (d.property.compatible e.property) W x)) := by
  rw [globalTensorGrade_coproduct_family_cast]
  exact congrArg (TensorProduct.assoc ℚ _ _ _) (globalTripleGrade_left_natural a c η hc θ d e f W x).symm

lemma globalTripleGrade_right_cast_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val (e.val+f.val) W) :
    tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
        (unitalSourceFiltration a c η hc θ (e.val+f.val))
        (unitalSourceFiltration_antitone a c η hc θ d.val)
        (unitalSourceFiltration_antitone a c η hc θ (e.val+f.val))
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,v))
        (fun u=>(globalTensorGradeInclusion a c η hc θ e f u).comp
          ((unitalGradeCoproduct a c η hc θ e.val f.val (e.property.compatible f.property) u).comp
            (unitalGradeCast a c η hc θ rfl rfl).toLinearMap)) W x=
    globalTripleGradeRight a c η hc θ d e f W
      (unitalTensorCoproductRight a c η hc θ d.val e.val f.val (e.property.compatible f.property) W x) := by
  rw [globalTensorGrade_coproduct_family_cast]
  exact (globalTripleGrade_right_natural a c η hc θ d e f W x).symm

lemma globalIteratedLeftSplit_dimensions (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (left s.val))
    (b d e f : I → ℕ) (hb : left s.val=b) (hd : left t.val=d)
    (he : right t.val=e) (hf : right s.val=f)
    (hbs : OnSlopeOrZero c η θ b) (hds : OnSlopeOrZero c η θ d)
    (hes : OnSlopeOrZero c η θ e) (hfs : OnSlopeOrZero c η θ f)
    (hde : d+e=b) (hbf : b+f=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalIteratedLeftSplit a c η hc θ k s t x =
      tensorGradeLift (unitalSourceFiltration a c η hc θ b)
        (unitalSourceFiltration a c η hc θ f)
        (unitalSourceFiltration_antitone a c η hc θ b)
        (unitalSourceFiltration_antitone a c η hc θ f)
        (fun u=>(globalTensorGradeInclusion a c η hc θ ⟨d,hds⟩ ⟨e,hes⟩ u).comp
          ((unitalGradeCoproduct a c η hc θ d e (hds.compatible hes) u).comp
            (unitalGradeCast a c η hc θ hde.symm rfl).toLinearMap))
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨f,hfs⟩,v)) k.2
        (unitalGradeCoproduct a c η hc θ b f (hbs.compatible hfs) k.2
          (unitalGradeCast a c η hc θ hbf.symm rfl x)) := by
  subst b; subst d; subst e; subst f
  rfl

lemma globalIteratedRightSplit_dimensions (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (right s.val))
    (b d e f : I → ℕ) (hb : right s.val=b) (hd : left s.val=d)
    (he : left t.val=e) (hf : right t.val=f)
    (hbs : OnSlopeOrZero c η θ b) (hds : OnSlopeOrZero c η θ d)
    (hes : OnSlopeOrZero c η θ e) (hfs : OnSlopeOrZero c η θ f)
    (hef : e+f=b) (hdb : d+b=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k s t x =
      tensorGradeLift (unitalSourceFiltration a c η hc θ d)
        (unitalSourceFiltration a c η hc θ b)
        (unitalSourceFiltration_antitone a c η hc θ d)
        (unitalSourceFiltration_antitone a c η hc θ b)
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨d,hds⟩,v))
        (fun u=>(globalTensorGradeInclusion a c η hc θ ⟨e,hes⟩ ⟨f,hfs⟩ u).comp
          ((unitalGradeCoproduct a c η hc θ e f (hes.compatible hfs) u).comp
            (unitalGradeCast a c η hc θ hef.symm rfl).toLinearMap)) k.2
        (unitalGradeCoproduct a c η hc θ d b (hds.compatible hbs) k.2
          (unitalGradeCast a c η hc θ hdb.symm rfl x)) := by
  subst b; subst d; subst e; subst f
  rfl

lemma globalIteratedLeftSplit_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (left s.val))
    (d e f : slopeDimensions c η hc θ)
    (hb : left s.val=d.val+e.val) (hd : left t.val=d.val)
    (he : right t.val=e.val) (hf : right s.val=f.val)
    (hp : d.val+e.val+f.val=k.1.val) (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _ (globalIteratedLeftSplit a c η hc θ k s t x)=
    globalLeftTripleOutput a c η hc θ k d e f hp x := by
  unfold globalLeftTripleOutput
  rw [globalIteratedLeftSplit_dimensions a c η hc θ k s t (d.val+e.val) d.val e.val f.val
    hb hd he hf (d.property.add hc e.property) d.property e.property f.property rfl hp x]
  exact globalTripleGrade_left_cast_natural a c η hc θ d e f k.2 _

lemma globalIteratedRightSplit_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (right s.val))
    (d e f : slopeDimensions c η hc θ)
    (hb : right s.val=e.val+f.val) (hd : left s.val=d.val)
    (he : left t.val=e.val) (hf : right t.val=f.val)
    (hp : d.val+(e.val+f.val)=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k s t x=
    globalTripleGradeRight a c η hc θ d e f k.2
      (unitalTensorCoproductRight a c η hc θ d.val e.val f.val (e.property.compatible f.property) k.2
        (unitalGradeCoproduct a c η hc θ d.val (e.val+f.val)
          (d.property.compatible (e.property.add hc f.property)) k.2
          (unitalGradeCast a c η hc θ hp.symm rfl x))) := by
  rw [globalIteratedRightSplit_dimensions a c η hc θ k s t (e.val+f.val) d.val e.val f.val
    hb hd he hf (e.property.add hc f.property) d.property e.property f.property rfl hp x]
  exact globalTripleGrade_right_cast_natural a c η hc θ d e f k.2 _

lemma globalIteratedLeftSplit_build_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (globalIteratedLeftSplit a c η hc θ k (leftTripleBuild c η hc θ k.1.val p).1
        (leftTripleBuild c η hc θ k.1.val p).2 x)=
      globalLeftTripleCoproduct a c η hc θ k p x := by
  exact globalIteratedLeftSplit_natural a c η hc θ k
    (leftTripleBuild c η hc θ k.1.val p).1 (leftTripleBuild c η hc θ k.1.val p).2
    ⟨p.val.1,p.property.2.1⟩ ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ rfl rfl
    (right_ofPair p.val.1 p.val.2.1 rfl) (right_ofPair (p.val.1+p.val.2.1) p.val.2.2 p.property.1)
    p.property.1 x

lemma globalIteratedLeftSplit_build (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (globalIteratedLeftSplit a c η hc θ k (leftTripleBuild c η hc θ k.1.val p).1
        (leftTripleBuild c η hc θ k.1.val p).2 x)=
      globalTripleCoproduct a c η hc θ k p x := by
  exact (globalIteratedLeftSplit_build_left a c η hc θ k p x).trans
    (globalTripleCoproduct_left a c η hc θ hχ k p x)

lemma globalIteratedRightSplit_build (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k (rightTripleBuild c η hc θ k.1.val p).1
      (rightTripleBuild c η hc θ k.1.val p).2 x=
      globalTripleCoproduct a c η hc θ k p x := by
  simpa only [globalTripleCoproduct, LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (globalIteratedRightSplit_natural a c η hc θ k
    (rightTripleBuild c η hc θ k.1.val p).1 (rightTripleBuild c η hc θ k.1.val p).2
    ⟨p.val.1,p.property.2.1⟩ ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩
    (right_ofPair p.val.1 (p.val.2.1+p.val.2.2) ((add_assoc _ _ _).symm.trans p.property.1)) rfl
    rfl (right_ofPair p.val.2.1 p.val.2.2 (by simp only [rightTripleBuild, right_ofPair]))
    ((add_assoc _ _ _).symm.trans p.property.1) x)

lemma globalIteratedLeftSplit_view (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : LeftSlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _ (globalIteratedLeftSplit a c η hc θ k p.1 p.2 x)=
      globalTripleCoproduct a c η hc θ k (leftTripleView c η hc θ k.1.val p) x := by
  have hh := globalIteratedLeftSplit_build a c η hc θ hχ k
    (leftTripleView c η hc θ k.1.val p) x
  rw [leftTripleBuild_view] at hh
  exact hh

lemma globalIteratedRightSplit_view (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (p : RightSlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k p.1 p.2 x=
      globalTripleCoproduct a c η hc θ k (rightTripleView c η hc θ k.1.val p) x := by
  have hh := globalIteratedRightSplit_build a c η hc θ k
    (rightTripleView c η hc θ k.1.val p) x
  rw [rightTripleBuild_view] at hh
  exact hh

lemma globalIteratedLeft_sum (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (left s.val),
        globalIteratedLeftSplit a c η hc θ k s t x)=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (left s.val),
        globalTripleCoproduct a c η hc θ k (leftTripleView c η hc θ k.1.val ⟨s,t⟩) x := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact globalIteratedLeftSplit_view a c η hc θ hχ k ⟨s,t⟩ x

lemma globalIteratedRight_sum (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    (∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (right s.val),
        globalIteratedRightSplit a c η hc θ k s t x)=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (right s.val),
        globalTripleCoproduct a c η hc θ k (rightTripleView c η hc θ k.1.val ⟨s,t⟩) x := by
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact globalIteratedRightSplit_view a c η hc θ k ⟨s,t⟩ x

lemma globalCoproduct_coassociative_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)))=
      TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ)
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)) := by
  rw [globalCoproduct_iterated_left_lof,globalCoproduct_iterated_right_lof,
    globalIteratedLeft_sum a c η hc θ hχ,globalIteratedRight_sum]
  exact sum_slopeTriple c η hc θ k.1.val (fun p=>globalTripleCoproduct a c η hc θ k p x)

theorem globalCoproduct_coassociative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (x : UnitalShuffle a c η hc θ) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id (globalCoproduct a c η hc θ x))=
      TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ) (globalCoproduct a c η hc θ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of k x => exact globalCoproduct_coassociative_lof a c η hc θ hχ k x
end ElementaryPositivity.RawShuffle

end

end OAI
