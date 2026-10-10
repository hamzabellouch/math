import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalEchelon02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

noncomputable section
open scoped BigOperators
namespace RationalMatrix
lemma real_polynomial {n m : ℕ} (p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) (j : Fin m) :
    RationalPolynomialMap.IsPolynomial (fun x=>real p x j) := by
  refine ⟨∑ i : Fin n,MvPolynomial.X i*MvPolynomial.C (p (Pi.single i 1) j),?_⟩
  intro x
  simp [real_apply]

lemma exists_matrix {n m : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hL : ∀ j,RationalPolynomialMap.IsPolynomial (fun x=>L x j)) :
    ∃ p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ),real p=L := by
  have hc (i : Fin n) (j : Fin m) : ∃ q : ℚ,(q:ℝ)=L (Pi.single i 1) j := by
    obtain ⟨P,hP⟩:=hL j
    dsimp only at hP
    rw [hP]
    apply RationalLattice.eval_rational
    intro a
    by_cases ha : a=i
    · subst a; exact ⟨1,by simp⟩
    · exact ⟨0,by simp [ha]⟩
  choose a ha using hc
  let p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ):=
    ∑ i : Fin n,(LinearMap.proj i).smulRight (a i)
  refine ⟨p,?_⟩
  apply (Pi.basisFun ℝ (Fin n)).ext
  intro i
  ext j
  simp only [Pi.basisFun_apply,real_single]
  have he : p (Pi.single i 1)=a i := by simp [p,LinearMap.sum_apply,Pi.single_apply]
  rw [he,ha]
end RationalMatrix

namespace RationalLattice
open MalcevCharacters
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates H m)
variable (hsk : SecondKind c) (F : G →* H) (hF : Continuous F)
variable (hrat : ∀ x,IsRational c x → IsRational d (F x))
include hsk hF hrat in
lemma logHom_rational_polynomial (i : Fin m) :
    RationalPolynomialMap.IsPolynomial (fun x=>logHom d c F x i) := by
  have hh (j : Fin m) : RationalPolynomialMap.IsPolynomial
      (fun x=>d.coord (F (canonicalExp c x)) j) := by
    simpa only [Homeomorph.symm_apply_apply] using
      RationalPolynomialMap.comp (rationalHom_polynomial d c hsk F hF hrat j)
        (canonicalExp_polynomial c)
  simpa only [logHom,Homeomorph.symm_apply_apply] using
    RationalPolynomialMap.comp (canonicalLog_polynomial d i) hh

include hsk hF hrat in
 

theorem exists_log_matrix :
    ∃ p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ),
      RationalMatrix.real p=(logHomLinear d c F).toLinearMap := by
  apply RationalMatrix.exists_matrix
  intro i
  simpa only [ContinuousLinearMap.coe_coe,logHomLinear_apply d c hsk F hF] using
    logHom_rational_polynomial c d hsk F hF hrat i

end RationalLattice
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
open Topology
namespace RationalLattice.QuotientLogImage
open MalcevCharacters
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates H m)
variable (hsk : SecondKind c) (F : G →* H) (hF : Continuous F)
variable (p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ))
variable (hp : RationalMatrix.real p=(logHomLinear d c F).toLinearMap)
variable (E : RationalEchelon.Chart (LinearMap.ker p))

def parametrization (x : Fin E.freeSet.card → ℝ) : F.range :=
  ⟨F (canonicalExp c (RationalMatrix.real E.sectionMap x)),⟨_,rfl⟩⟩

include hsk hF hp in
lemma parametrization_exp (x : Fin E.freeSet.card → ℝ) :
    (parametrization c F p E x:H)=
      canonicalExp d (RationalMatrix.real (p.comp E.sectionMap) x) := by
  change F (canonicalExp c (RationalMatrix.real E.sectionMap x))=_
  rw [map_canonicalExp d c hsk F hF,RationalMatrix.real_comp,hp]
  rfl

include hsk hF hp in
lemma parametrization_quotient (g : G) :
    parametrization c F p E (RationalMatrix.real E.quotientMap (canonicalLog c g))=F.rangeRestrict g := by
  apply Subtype.ext
  rw [parametrization_exp c d hsk F hF p hp E,RationalMatrix.real_comp]
  change canonicalExp d (RationalMatrix.real p (RationalMatrix.real E.sectionMap
      (RationalMatrix.real E.quotientMap (canonicalLog c g))))=F g
  rw [E.real_map_section_quotient p rfl,hp]
  change canonicalExp d (logHomLinear d c F (canonicalLog c g))=F g
  rw [logHomLinear_log d c hsk F hF,canonicalExp_log]

include hsk hF hp in
lemma parametrization_embedding : IsEmbedding (parametrization c F p E) := by
  have hi:=RationalMatrix.real_injective_of_injective _ (E.section_map_injective p rfl)
  have he:=LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hcomp : IsEmbedding (fun x=>(parametrization c F p E x:H)) := by
    have hh:=(logHomeomorph d).symm.isEmbedding.comp he.isEmbedding
    change IsEmbedding (fun x=>canonicalExp d (RationalMatrix.real (p.comp E.sectionMap) x)) at hh
    simpa only [← parametrization_exp c d hsk F hF p hp E] using hh
  exact { toIsInducing:=IsInducing.subtypeVal.of_comp_iff.mp hcomp.toIsInducing
          injective:=fun x y hx=>hcomp.injective (congrArg Subtype.val hx) }

include hsk hF hp in
lemma parametrization_surjective : Function.Surjective (parametrization c F p E) := by
  intro y
  obtain ⟨g,hg⟩:=y.property
  refine ⟨RationalMatrix.real E.quotientMap (canonicalLog c g),?_⟩
  rw [parametrization_quotient c d hsk F hF p hp E]
  exact Subtype.ext hg

 

def coordinates : F.range ≃ₜ (Fin E.freeSet.card → ℝ) :=
  ((parametrization_embedding c d hsk F hF p hp E).toHomeomorphOfSurjective
    (parametrization_surjective c d hsk F hF p hp E)).symm

lemma coordinates_symm (x : Fin E.freeSet.card → ℝ) :
    (coordinates c d hsk F hF p hp E).symm x=parametrization c F p E x := rfl

lemma coordinates_map (g : G) :
    coordinates c d hsk F hF p hp E (F.rangeRestrict g)=
      RationalMatrix.real E.quotientMap (canonicalLog c g) := by
  rw [← parametrization_quotient c d hsk F hF p hp E]
  exact (coordinates c d hsk F hF p hp E).apply_symm_apply _

lemma coordinates_one : coordinates c d hsk F hF p hp E 1=0 := by
  have hh:=coordinates_map c d hsk F hF p hp E 1
  simpa only [map_one,canonicalLog_one,map_zero] using hh

include hsk hF hp E in
 
theorem image_isClosed : IsClosed (F.range : Set H) := by
  have hi:=RationalMatrix.real_injective_of_injective _ (E.section_map_injective p rfl)
  have he:=LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hh:=(logHomeomorph d).symm.isClosedEmbedding.comp he
  have hr : Set.range (fun x=>(logHomeomorph d).symm (RationalMatrix.real (p.comp E.sectionMap) x))=
      (F.range : Set H) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      change canonicalExp d (RationalMatrix.real (p.comp E.sectionMap) x)∈F.range
      rw [← parametrization_exp c d hsk F hF p hp E]
      exact (parametrization c F p E x).property
    · intro hy
      obtain ⟨x,hx⟩:=parametrization_surjective c d hsk F hF p hp E ⟨y,hy⟩
      refine ⟨x,?_⟩
      change canonicalExp d (RationalMatrix.real (p.comp E.sectionMap) x)=y
      rw [← parametrization_exp c d hsk F hF p hp E]
      exact congrArg Subtype.val hx
  exact hr ▸ hh.isClosed_range

include hsk hF in
lemma parametrization_polynomial (hrat : ∀ x,IsRational c x → IsRational d (F x)) :
    IsPolynomialMap d (fun x=>(parametrization c F p E x:H)) := by
  have hh (j : Fin m) : RationalPolynomialMap.IsPolynomial
      (fun x=>d.coord (F (canonicalExp c x)) j) := by
    simpa only [Homeomorph.symm_apply_apply] using
      RationalPolynomialMap.comp (rationalHom_polynomial d c hsk F hF hrat j)
        (canonicalExp_polynomial c)
  intro j
  exact RationalPolynomialMap.comp (hh j) (RationalMatrix.real_polynomial E.sectionMap)

end RationalLattice.QuotientLogImage
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.QuotientLaw
open WeightedPolynomial MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable {W : Submodule ℚ (Fin n → ℚ)} (E : RationalEchelon.Chart W)

def multiply (x : (Fin E.freeSet.card ⊕ Fin E.freeSet.card) → ℝ) : Fin E.freeSet.card → ℝ:=
  RationalMatrix.real E.quotientMap (canonicalLog c
    (canonicalExp c (RationalMatrix.real E.sectionMap (fun j=>x (Sum.inl j)))*
      canonicalExp c (RationalMatrix.real E.sectionMap (fun j=>x (Sum.inr j)))))

omit [IsTopologicalGroup G] in
lemma multiply_left (y : Fin E.freeSet.card → ℝ) :
    multiply c E (Sum.elim (fun _=>0) y)=y := by
  change RationalMatrix.real E.quotientMap (canonicalLog c
    (canonicalExp c (RationalMatrix.real E.sectionMap 0)*canonicalExp c (RationalMatrix.real E.sectionMap y)))=y
  rw [map_zero,canonicalExp_zero,one_mul,canonicalLog_exp,E.real_quotient_section]
omit [IsTopologicalGroup G] in
lemma multiply_right (x : Fin E.freeSet.card → ℝ) :
    multiply c E (Sum.elim x (fun _=>0))=x := by
  change RationalMatrix.real E.quotientMap (canonicalLog c
    (canonicalExp c (RationalMatrix.real E.sectionMap x)*canonicalExp c (RationalMatrix.real E.sectionMap 0)))=x
  rw [map_zero,canonicalExp_zero,mul_one,canonicalLog_exp,E.real_quotient_section]

omit [IsTopologicalGroup G] in
lemma multiply_polynomial (i : Fin E.freeSet.card) :
    RationalPolynomialMap.IsPolynomial (fun x=>multiply c E x i) := by
  have hl (j : Fin n) := RationalPolynomialMap.comp (RationalMatrix.real_polynomial E.sectionMap j)
    (fun k=>RationalPolynomialMap.coordinate (Sum.inl k : Fin E.freeSet.card ⊕ Fin E.freeSet.card))
  have hr (j : Fin n) := RationalPolynomialMap.comp (RationalMatrix.real_polynomial E.sectionMap j)
    (fun k=>RationalPolynomialMap.coordinate (Sum.inr k : Fin E.freeSet.card ⊕ Fin E.freeSet.card))
  have hml (j : Fin n):=RationalPolynomialMap.comp (canonicalExp_polynomial c j) hl
  have hmr (j : Fin n):=RationalPolynomialMap.comp (canonicalExp_polynomial c j) hr
  have hmul:=polynomialMap_mul c hml hmr
  have hlog (j : Fin n):=RationalPolynomialMap.comp (canonicalLog_polynomial c j) hmul
  have hq:=RationalPolynomialMap.comp (RationalMatrix.real_polynomial E.quotientMap i) hlog
  simpa only [multiply,Homeomorph.symm_apply_apply] using hq

variable (hsk : SecondKind c) (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hmono : Monotone w)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
include hmono in
lemma quotient_preserves : WeightedLinear.Preserves w (fun i=>w (E.free i))
    (RationalMatrix.real E.quotientMap) := by
  intro k x hx
  exact E.real_quotient_level w hmono k x hx
lemma section_preserves : WeightedLinear.Preserves (fun i=>w (E.free i)) w
    (RationalMatrix.real E.sectionMap) := by
  intro k x hx
  exact E.real_section_level w k x hx

include hsk hmono hA in
lemma multiply_weighted (i : Fin E.freeSet.card) :
    IsWeighted (Sum.elim (fun i=>w (E.free i)) (fun i=>w (E.free i))) (w (E.free i))
      (fun x=>multiply c E x i) := by
  have hs:=section_preserves E w
  have hlin (j : Fin n ⊕ Fin n) :
      IsWeighted (Sum.elim (fun i=>w (E.free i)) (fun i=>w (E.free i))) (Sum.elim w w j)
      (fun x=>Sum.elim
        (RationalMatrix.real E.sectionMap (fun i=>x (Sum.inl i)))
        (RationalMatrix.real E.sectionMap (fun i=>x (Sum.inr i))) j) := by
    cases j with
    | inl j => exact (hs.weighted j).comp (fun k=>IsWeighted.coordinate _ (Sum.inl k))
    | inr j => exact (hs.weighted j).comp (fun k=>IsWeighted.coordinate _ (Sum.inr k))
  have hm (j : Fin n):=(log_multiplication_weighted c hsk A w hA j).comp hlin
  simp only [Sum.elim_inl,Sum.elim_inr] at hm
  exact ((quotient_preserves E w hmono).weighted i).comp hm

end RationalLattice.QuotientLaw

end
end
end

end OAI
