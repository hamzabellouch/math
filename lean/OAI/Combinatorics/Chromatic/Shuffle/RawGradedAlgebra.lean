import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNSpanning
import OAI.Combinatorics.Chromatic.Shuffle.ShuffleUnits
import OAI.Combinatorics.Chromatic.GradedAlgebra.GradedBuilders

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

def rawComponent (_a : I → I → ℕ) (d : I → ℕ) := S d
noncomputable instance (a : I → I → ℕ) (d : I → ℕ) : AddCommGroup (rawComponent a d) :=
  inferInstanceAs (AddCommGroup (S d))
noncomputable instance (a : I → I → ℕ) (d : I → ℕ) : Module ℚ (rawComponent a d) :=
  inferInstanceAs (Module ℚ (S d))

noncomputable instance rawGradedMul (a : I → I → ℕ) : GradedMonoid.GMul (rawComponent a) where
  mul f g := shufflePolynomial a f g
noncomputable instance rawGradedOne (a : I → I → ℕ) : GradedMonoid.GOne (rawComponent a) where
  one := (1 : S (0 : I → ℕ))

omit [Fintype I] [DecidableEq I] in
lemma castS_heq {d e : I → ℕ} (h : d=e) (f : S d) : HEq (castS h f) f := by
  subst e
  rfl

lemma raw_one_mul (a : I → I → ℕ) (x : GradedMonoid (rawComponent a)) : 1*x=x := by
  apply Sigma.ext (zero_add _)
  exact (heq_of_eq (shufflePolynomial_unit_left a x.1 x.2)).trans (castS_heq _ _)
lemma raw_mul_one (a : I → I → ℕ) (x : GradedMonoid (rawComponent a)) : x*1=x := by
  apply Sigma.ext (add_zero _)
  exact (heq_of_eq (shufflePolynomial_unit_right a x.1 x.2)).trans (castS_heq _ _)
lemma raw_mul_assoc (a : I → I → ℕ) (x y z : GradedMonoid (rawComponent a)) : x*y*z=x*(y*z) := by
  apply Sigma.ext (add_assoc _ _ _)
  exact (castS_heq (add_assoc x.1 y.1 z.1) _).symm.trans (heq_of_eq (shufflePolynomial_assoc a x.2 y.2 z.2))
noncomputable instance rawGradedMonoid (a : I → I → ℕ) : GradedMonoid.GMonoid (rawComponent a) :=
  gradedMonoidOfLaws (raw_one_mul a) (raw_mul_one a) (raw_mul_assoc a)
noncomputable instance rawGradedRing (a : I → I → ℕ) : DirectSum.GRing (rawComponent a) :=
  gradedRingOfAddLaws (fun _=>shufflePolynomial_zero_right a _ _ _)
    (fun _=>shufflePolynomial_zero_left a _ _ _)
    (fun _ _ _=>shufflePolynomial_add_right a _ _ _)
    (fun _ _ _=>shufflePolynomial_add_left a _ _ _)
lemma raw_smul_mul (a : I → I → ℕ) (r : ℚ) (x y : GradedMonoid (rawComponent a)) :
    (r•x)*y=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  exact heq_of_eq (shufflePolynomial_smul_left a r x.2 y.2)
lemma raw_mul_smul (a : I → I → ℕ) (r : ℚ) (x y : GradedMonoid (rawComponent a)) :
    x*(r•y)=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  exact heq_of_eq (shufflePolynomial_smul_right a r x.2 y.2)
noncomputable instance rawGradedAlgebra (a : I → I → ℕ) : DirectSum.GAlgebra ℚ (rawComponent a) :=
  gradedAlgebraOfBilinear (raw_smul_mul a) (raw_mul_smul a)

abbrev RawAlgebra (a : I → I → ℕ) := ⨁ d : I → ℕ,rawComponent a d
noncomputable def rawLof (a : I → I → ℕ) (d : I → ℕ) : S d →ₗ[ℚ] RawAlgebra a :=
  DirectSum.lof ℚ _ (rawComponent a) d
lemma rawLof_mul (a : I → I → ℕ) (d e : I → ℕ) (x : S d) (y : S e) :
    rawLof a d x*rawLof a e y=rawLof a (d+e) (shufflePolynomial a x y) := by
  exact DirectSum.of_mul_of (A:=rawComponent a) x y
omit [DecidableEq I] in
lemma rawLof_cast (a : I → I → ℕ) {d e : I → ℕ} (h : d=e) (x : S d) :
    rawLof a e (castS h x)=rawLof a d x := by subst e; rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)
noncomputable def rawDimensionSpace (d : I → ℕ) : Submodule ℚ (RawAlgebra a) :=
  LinearMap.range (rawLof a d)
noncomputable def rawSectionSpace
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) : Submodule ℚ (RawAlgebra a) :=
  LinearMap.range ((rawLof a d).comp (σ d))
lemma rawSectionSpace_le (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    rawSectionSpace a c η σ d ≤ rawDimensionSpace a d := by
  rintro _ ⟨x,rfl⟩
  exact ⟨σ d x,rfl⟩
lemma rawDimensionSpace_mul (d e : I → ℕ) :
    rawDimensionSpace a d*rawDimensionSpace a e ≤ rawDimensionSpace a (d+e) := by
  apply Submodule.mul_le.mpr
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
  exact ⟨shufflePolynomial a x y,(rawLof_mul a d e x y).symm⟩
lemma rawDimensionSpace_zero : rawDimensionSpace a 0 ≤ 1 := by
  rintro _ ⟨x,rfl⟩
  rw [S_zero_eq_scalar x,map_smul]
  change MvPolynomial.constantCoeff x.val • (1 : RawAlgebra a) ∈ (1 : Submodule ℚ _)
  exact Submodule.smul_mem _ _ (Submodule.one_le.mp le_rfl)

variable (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
variable (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
include hσ in
lemma rawDimensionSpace_decompose (d : I → ℕ) (_hd : d≠0) :
    rawDimensionSpace a d ≤ rawSectionSpace a c η σ d ⊔
      ⨆ (u : I → ℕ) (v : I → ℕ) (_ : u+v=d) (_ : u≠0) (_ : v≠0)
        (_ : slope c η d < slope c η u),rawDimensionSpace a u*rawDimensionSpace a v := by
  let Q := destabilizingSpace a (slope c η) d
  let U : Submodule ℚ (RawAlgebra a) :=
    ⨆ (u : I → ℕ) (v : I → ℕ) (_ : u+v=d) (_ : u≠0) (_ : v≠0)
      (_ : slope c η d < slope c η u),rawDimensionSpace a u*rawDimensionSpace a v
  have hQ : Q ≤ U.comap (rawLof a d) := by
    apply Submodule.span_le.mpr
    rintro f ⟨u,v,h,x,y,hu,hv,hμ,rfl⟩
    change rawLof a d (dimensionCast h (shufflePolynomial a x y)) ∈ U
    have hc : dimensionCast h (shufflePolynomial a x y)=castS h (shufflePolynomial a x y) := by
      subst d; rfl
    rw [hc,rawLof_cast,←rawLof_mul]
    have hi : rawDimensionSpace a u*rawDimensionSpace a v ≤ U :=
      le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le h
        (le_iSup_of_le hu (le_iSup_of_le hv (le_iSup_of_le hμ le_rfl)))))
    apply hi
    exact Submodule.mul_mem_mul (show rawLof a u x∈rawDimensionSpace a u from ⟨x,rfl⟩)
      (show rawLof a v y∈rawDimensionSpace a v from ⟨y,rfl⟩)
  rintro _ ⟨f,rfl⟩
  have hm : f-σ d (Q.mkQ f)∈Q := by
    apply (Submodule.Quotient.mk_eq_zero Q).mp
    change Q.mkQ (f-σ d (Q.mkQ f))=0
    rw [map_sub,hσ d,sub_self]
  have hleft : rawLof a d (σ d (Q.mkQ f))∈rawSectionSpace a c η σ d := ⟨Q.mkQ f,rfl⟩
  have hright : rawLof a d (f-σ d (Q.mkQ f))∈U := hQ hm
  have hh := Submodule.add_mem_sup hleft hright
  simpa only [map_sub,add_sub_cancel] using hh

include hσ in

theorem raw_hn_spanning (hc : ∀ i,0 < c i) (d : I → ℕ) :
    rawDimensionSpace a d ≤ hnOrderedSpan c η (rawSectionSpace a c η σ) d :=
  hn_spanning c η (rawSectionSpace a c η σ) hc (rawDimensionSpace a)
    (rawSectionSpace_le a c η σ) (rawDimensionSpace_mul a) (rawDimensionSpace_zero a)
    (rawDimensionSpace_decompose a c η σ hσ) d

noncomputable def quotientSection (d : I → ℕ) : B a (slope c η) d →ₗ[ℚ] S d :=
  Classical.choose ((destabilizingSpace a (slope c η) d).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _))
lemma quotientSection_rightInverse (d : I → ℕ) :
    Function.RightInverse (quotientSection a c η d) (destabilizingSpace a (slope c η) d).mkQ := by
  have h := Classical.choose_spec ((destabilizingSpace a (slope c η) d).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _))
  intro x
  exact LinearMap.congr_fun h x

theorem actual_raw_hn_spanning (hc : ∀ i,0 < c i) (d : I → ℕ) :
    rawDimensionSpace a d ≤ hnOrderedSpan c η (rawSectionSpace a c η (quotientSection a c η)) d :=
  raw_hn_spanning a c η (quotientSection a c η) (quotientSection_rightInverse a c η) hc d
end ElementaryPositivity.RawShuffle

end

end OAI
