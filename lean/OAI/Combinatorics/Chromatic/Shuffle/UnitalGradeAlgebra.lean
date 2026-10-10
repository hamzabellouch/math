import Mathlib
import OAI.Combinatorics.Chromatic.Walls.Grade

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma slopeZero (c η : I → ℝ) (θ : ℝ) : OnSlopeOrZero c η θ (0 : I → ℕ) := Or.inl rfl

lemma shuffleBUnit_assoc (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e b : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (he : OnSlopeOrZero c η θ e) (hb : OnSlopeOrZero c η θ b)
    (f : B a (slope c η) d) (g : B a (slope c η) e) (h : B a (slope c η) b) :
    castB a (slope c η) (add_assoc d e b)
      (shuffleBUnit a c η hc (d+e) b ((hd.add hc he).compatible hb)
        (shuffleBUnit a c η hc d e (hd.compatible he) f g) h)=
    shuffleBUnit a c η hc d (e+b) (hd.compatible (he.add hc hb)) f
      (shuffleBUnit a c η hc e b (he.compatible hb) g h) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      induction h using Submodule.Quotient.induction_on with
      | H h =>
        change castB a (slope c η) (add_assoc d e b)
          (quotientAlg a (slope c η) ((d+e)+b) (shufflePolynomial a (shufflePolynomial a f g) h))=
          quotientAlg a (slope c η) (d+(e+b)) (shufflePolynomial a f (shufflePolynomial a g h))
        rw [castB_mk,shufflePolynomial_assoc]

noncomputable def unitalFiltrationCast (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V) :
    unitalSourceFiltration a c η hc θ d U ≃ₗ[ℚ] unitalSourceFiltration a c η hc θ e V := by
  subst e
  subst V
  exact LinearEquiv.refl _ _

noncomputable def unitalGradeCast (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V) :
    UnitalSourceGrade a c η hc θ d U ≃ₗ[ℚ] UnitalSourceGrade a c η hc θ e V := by
  subst e
  subst V
  exact LinearEquiv.refl _ _

lemma unitalFiltrationCast_val (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V)
    (f : unitalSourceFiltration a c η hc θ d U) :
    (unitalFiltrationCast a c η hc θ h k f).val=castB a (slope c η) h f.val := by
  subst e
  subst V
  rfl

lemma unitalGradeCast_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V)
    (f : unitalSourceFiltration a c η hc θ d U) :
    unitalGradeCast a c η hc θ h k (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk (unitalFiltrationCast a c η hc θ h k f) :
        UnitalSourceGrade a c η hc θ e V) := by
  subst e
  subst V
  rfl

lemma unitalGradeShuffle_assoc (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e b : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (hb : OnSlopeOrZero c η θ b)
    (U V W : ℤ) (f : UnitalSourceGrade a c η hc θ d U)
    (g : UnitalSourceGrade a c η hc θ e V) (h : UnitalSourceGrade a c η hc θ b W) :
    unitalGradeCast a c η hc θ (add_assoc d e b) (add_assoc U V W)
      (unitalGradeShuffle a c η hc θ hχ (d+e) b (hd.add hc he) hb (U+V) W
        (unitalGradeShuffle a c η hc θ hχ d e hd he U V f g) h)=
    unitalGradeShuffle a c η hc θ hχ d (e+b) hd (he.add hc hb) U (V+W) f
      (unitalGradeShuffle a c η hc θ hχ e b he hb V W g h) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      induction h using Submodule.Quotient.induction_on with
      | H h =>
        simp only [unitalGradeShuffle_mk,unitalGradeCast_mk]
        congr 1
        apply Subtype.ext
        rw [unitalFiltrationCast_val]
        exact shuffleBUnit_assoc a c η hc θ d e b hd he hb f.val g.val h.val

noncomputable def unitalGradeOne (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) : UnitalSourceGrade a c η hc θ 0 0 :=
  Submodule.Quotient.mk ⟨1,by simp [unitalSourceFiltration_zero]⟩

lemma unitalGradeShuffle_one_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (W : ℤ) (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeShuffle a c η hc θ hχ 0 d (slopeZero c η θ) hd 0 W (unitalGradeOne a c η hc θ) f=
      unitalGradeCast a c η hc θ (zero_add d).symm (zero_add W).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [unitalGradeOne,unitalGradeShuffle_mk,unitalGradeCast_mk]
    congr 1
    apply Subtype.ext
    rw [unitalFiltrationCast_val]
    exact shuffleBUnit_one_left a c η hc d _ f.val

lemma unitalGradeShuffle_one_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (W : ℤ) (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeShuffle a c η hc θ hχ d 0 hd (slopeZero c η θ) W 0 f (unitalGradeOne a c η hc θ)=
      unitalGradeCast a c η hc θ (add_zero d).symm (add_zero W).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [unitalGradeOne,unitalGradeShuffle_mk,unitalGradeCast_mk]
    congr 1
    apply Subtype.ext
    rw [unitalFiltrationCast_val]
    exact shuffleBUnit_one_right a c η hc d _ f.val
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev slopeDimensions (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) : AddSubmonoid (I → ℕ) where
  carrier := {d | OnSlopeOrZero c η θ d}
  zero_mem' := Or.inl rfl
  add_mem' := fun hd he=>hd.add hc he

abbrev SlopeWeight (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) :=
  slopeDimensions c η hc θ × ℤ

abbrev unitalComponent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (k : SlopeWeight c η hc θ) :=
  UnitalSourceGrade a c η hc θ k.1.val k.2

lemma unitalGradeCast_heq (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V)
    (f : UnitalSourceGrade a c η hc θ d U) :
    HEq (unitalGradeCast a c η hc θ h k f) f := by
  subst e
  subst V
  rfl

noncomputable instance componentGradedMul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)] :
    GradedMonoid.GMul (unitalComponent a c η hc θ) where
  mul {i j} f g := unitalGradeShuffle a c η hc θ hχ.out i.1.val j.1.val i.1.property j.1.property i.2 j.2 f g

noncomputable instance componentGradedOne (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) : GradedMonoid.GOne (unitalComponent a c η hc θ) where
  one := unitalGradeOne a c η hc θ

lemma component_one_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (f : GradedMonoid (unitalComponent a c η hc θ)) : 1*f=f := by
  apply Sigma.ext (zero_add _)
  exact (heq_of_eq (unitalGradeShuffle_one_left a c η hc θ hχ.out f.1.1.val f.1.1.property f.1.2 f.2)).trans
    (unitalGradeCast_heq a c η hc θ _ _ f.2)

lemma component_mul_one (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (f : GradedMonoid (unitalComponent a c η hc θ)) : f*1=f := by
  apply Sigma.ext (add_zero _)
  exact (heq_of_eq (unitalGradeShuffle_one_right a c η hc θ hχ.out f.1.1.val f.1.1.property f.1.2 f.2)).trans
    (unitalGradeCast_heq a c η hc θ _ _ f.2)

lemma component_mul_assoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (f g h : GradedMonoid (unitalComponent a c η hc θ)) : (f*g)*h=f*(g*h) := by
  apply Sigma.ext (add_assoc _ _ _)
  exact (unitalGradeCast_heq a c η hc θ (add_assoc f.1.1.val g.1.1.val h.1.1.val)
    (add_assoc f.1.2 g.1.2 h.1.2) _).symm.trans
    (heq_of_eq (unitalGradeShuffle_assoc a c η hc θ hχ.out f.1.1.val g.1.1.val h.1.1.val
      f.1.1.property g.1.1.property h.1.1.property f.1.2 g.1.2 h.1.2 f.2 g.2 h.2))

noncomputable instance componentGradedMonoid (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    GradedMonoid.GMonoid (unitalComponent a c η hc θ) :=
  gradedMonoidOfLaws (component_one_mul a c η hc θ)
    (component_mul_one a c η hc θ) (component_mul_assoc a c η hc θ)

noncomputable instance componentGradedRing (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)] :
    DirectSum.GRing (unitalComponent a c η hc θ) :=
  gradedRingOfAddLaws
    (fun _=>map_zero _)
    (fun {i j} x=>by
      change unitalGradeShuffle a c η hc θ hχ.out i.1.val j.1.val
        i.1.property j.1.property i.2 j.2 0 x=0
      rw [map_zero]
      rfl)
    (fun _ _ _=>map_add _ _ _)
    (fun {i j} x y z=>by
      change unitalGradeShuffle a c η hc θ hχ.out i.1.val j.1.val
        i.1.property j.1.property i.2 j.2 (x+y) z=_
      rw [map_add]
      rfl)

lemma component_smul_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (r : ℚ) (x y : GradedMonoid (unitalComponent a c η hc θ)) : (r•x)*y=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  apply heq_of_eq
  change unitalGradeShuffle a c η hc θ hχ.out x.1.1.val y.1.1.val
    x.1.1.property y.1.1.property x.1.2 y.1.2 (r•x.2) y.2=r•_
  rw [map_smul,LinearMap.smul_apply]
  rfl

lemma component_mul_smul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (r : ℚ) (x y : GradedMonoid (unitalComponent a c η hc θ)) : x*(r•y)=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  apply heq_of_eq
  exact map_smul (unitalGradeShuffle a c η hc θ hχ.out x.1.1.val y.1.1.val
    x.1.1.property y.1.1.property x.1.2 y.1.2 x.2) r y.2

noncomputable instance componentGradedAlgebra (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    DirectSum.GAlgebra ℚ (unitalComponent a c η hc θ) :=
  gradedAlgebraOfBilinear (component_smul_mul a c η hc θ) (component_mul_smul a c η hc θ)

abbrev UnitalShuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) :=
  ⨁ k : SlopeWeight c η hc θ,unitalComponent a c η hc θ k

end ElementaryPositivity.RawShuffle

end

end OAI
