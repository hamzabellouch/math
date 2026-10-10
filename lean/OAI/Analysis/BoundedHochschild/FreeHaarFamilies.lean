import Mathlib
import OAI.Analysis.BoundedHochschild.AlternatingMoments
import OAI.Analysis.BoundedHochschild.PathWords

namespace OAI

/-! Free Haar extensions, graded families and finite free-group erasure. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open BoundedHochschild HochschildRigidity TracialUltrapower HochschildPatching HochschildComparison
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def powerFamily {A : Type*} [CStarAlgebra A] (w : unitary A) : Multiplicative ℤ →* A :=
  (unitary A).subtype.comp (zpowersHom (unitary A) w)
@[simp] lemma powerFamily_apply {A : Type*} [CStarAlgebra A] (w : unitary A) (k : Multiplicative ℤ) :
    powerFamily w k=((w^k.toAdd : unitary A):A) := rfl

include e in
theorem exists_free_haar_extension
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    {G : Type*} [Group G] [Countable G] (ν : ℕ → G →* unitary M) :
    ∃ w : ℕ → unitary M,
      (∀ k : ℤ, k ≠ 0 → quotientTrace τ h1 ω htr
        (((quotientUnitary τ h1 ω htr w)^k : unitary (Ultrapower τ h1 ω htr)) : Ultrapower τ h1 ω htr)=0) ∧
      ∀ l : List (G ⊕ Multiplicative ℤ),
        l.IsChain (fun x y => HochschildGradedFree.tag x ≠ HochschildGradedFree.tag y) → l ≠ [] →
        quotientTrace τ h1 ω htr
          (HochschildGradedFree.centeredEval (quotientFamily τ h1 ω htr ν)
            (powerFamily (quotientUnitary τ h1 ω htr w)) (quotientTrace τ h1 ω htr).toLinearMap l)=0 := by
  have hnorm (g : G) (n : ℕ) : ‖boundedHom ν g n‖ ≤ 1 := by
    have hh := CStarRing.norm_coe_unitary_mul (ν n g) (1:M)
    simp only [mul_one] at hh
    change ‖(ν n g:M)‖ ≤ 1
    rw [hh]
    exact IsStarProjection.norm_le _ (IsStarProjection.one M)
  obtain ⟨w,hw⟩ := exists_quotient_unitary_all_moments e τ hτ h1 htr hfaith hfactor hdiff ω hω
    (fun g => boundedHom ν g) hnorm
  let U := quotientFamily τ h1 ω htr ν
  let W := quotientUnitary τ h1 ω htr w
  let T := quotientTrace τ h1 ω htr
  let F : G → Ultrapower τ h1 ω htr := fun g => U g-T (U g) • 1
  have hm (a : Option G) (l : List (IntAtom G)) (hl : admissibleIntTail l)
      (hk : ∀ b ∈ l, b.1 ≠ 0) : T (integerEval F W a l)=0 :=
    integer_moments_of_bounded T F W hw a l hl hk
  have hpower (k : ℤ) (hk : k ≠ 0) : T ((W^k : unitary (Ultrapower τ h1 ω htr)):Ultrapower τ h1 ω htr)=0 := by
    have hh := hm none [(k,none)] ⟨by simp,by simp⟩ (by simpa using hk)
    simpa only [integerEval,wordCoeff,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul] using hh
  refine ⟨w,hpower,fun l hc hl => ?_⟩
  let R : Multiplicative ℤ → Ultrapower τ h1 ω htr := fun h => powerFamily W h-T (powerFamily W h) • 1
  have hF (g : G) : T (F g)=0 := by
    simp only [F,map_sub,map_smul,smul_eq_mul,quotientTrace_one,T,mul_one,sub_self]
  have hR (h : Multiplicative ℤ) : R h=0 ∨ ∃ k : ℤ, k ≠ 0 ∧ R h=((W^k : unitary (Ultrapower τ h1 ω htr)):Ultrapower τ h1 ω htr) := by
    by_cases hh : h.toAdd=0
    · left
      simp [R,powerFamily_apply,hh,T,quotientTrace_one]
    · right
      exact ⟨h.toAdd,hh,by simp only [R,powerFamily_apply,hpower _ hh,zero_smul,sub_zero]⟩
  have hz := alternating_moment_zero T.toLinearMap F R W hF hR hm l hc hl
  have he : HochschildGradedFree.centeredEval U (powerFamily W) T.toLinearMap l =
      (l.map (Sum.elim F R)).prod := by
    unfold HochschildGradedFree.centeredEval
    congr 1
    apply List.map_congr_left
    intro x hx
    cases x <;> rfl
  change T (HochschildGradedFree.centeredEval U (powerFamily W) T.toLinearMap l)=0
  rw [he]
  exact hz

end HochschildUltrapower

 

 

namespace HochschildSplitWord
variable {A G H B : Type*} [Group G] [Group H] [Monoid B]
def invLetter : G ⊕ H → G ⊕ H := Sum.map Inv.inv Inv.inv
def signedLetter (f : A → G ⊕ H) (x : A × Bool) : G ⊕ H :=
  if x.2 then f x.1 else invLetter (f x.1)
def sumProduct (u : G →* B) (v : H →* B) (l : List (G ⊕ H)) : B :=
  (l.map (Sum.elim u v)).prod

def splitWord [DecidableEq A] (f : A → G ⊕ H) (q : FreeGroup A) : List (G ⊕ H) :=
  q.toWord.map (signedLetter f)

lemma hom_mk (σ : FreeGroup A →* B) (l : List (A × Bool)) :
    σ (FreeGroup.mk l)=(l.map (fun x => if x.2 then σ (FreeGroup.of x.1) else σ ((FreeGroup.of x.1)⁻¹))).prod := by
  conv_lhs => rw [← FreeGroup.lift_of_apply (FreeGroup.mk l),FreeGroup.lift_mk]
  rw [map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  rcases x with ⟨a,b⟩
  cases b <;> rfl

lemma sumProduct_splitWord [DecidableEq A]
    (u : G →* B) (v : H →* B) (σ : FreeGroup A →* B) (f : A → G ⊕ H)
    (hp : ∀ a, σ (FreeGroup.of a)=Sum.elim u v (f a))
    (hn : ∀ a, σ ((FreeGroup.of a)⁻¹)=Sum.elim u v (invLetter (f a))) (q : FreeGroup A) :
    sumProduct u v (splitWord f q)=σ q := by
  conv_rhs => rw [← FreeGroup.mk_toWord (x := q),hom_mk]
  simp only [sumProduct,splitWord,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  cases hb : x.2 <;> simp only [Function.comp_apply,signedLetter,hb,Bool.false_eq_true,ite_false,ite_true]
  · exact (hn x.1).symm
  · exact (hp x.1).symm

lemma sumProduct_splitWord_group {B : Type*} [Group B] [DecidableEq A]
    (u : G →* B) (v : H →* B) (σ : FreeGroup A →* B) (f : A → G ⊕ H)
    (hp : ∀ a, σ (FreeGroup.of a)=Sum.elim u v (f a)) (q : FreeGroup A) :
    sumProduct u v (splitWord f q)=σ q := by
  apply sumProduct_splitWord u v σ f hp
  intro a
  rw [map_inv,hp]
  cases h : f a <;> simp [invLetter,Sum.elim,map_inv]
end HochschildSplitWord

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open BoundedHochschild HochschildRigidity HochschildPatching HochschildComparison HochschildSplitWord
variable {C D : Type*} [DecidableEq D]
def gradedDegree (s : Finset D) : FreeGroup (C ⊕ D) →* FreeGroup D :=
  FreeGroup.lift (Sum.elim (fun _ => 1) (fun d => if d ∈ s then FreeGroup.of d else 1))
@[simp] lemma gradedDegree_left (s : Finset D) (c : C) : gradedDegree s (FreeGroup.of (Sum.inl c))=1 := by
  simp [gradedDegree]
@[simp] lemma gradedDegree_right (s : Finset D) (d : D) :
    gradedDegree (C := C) s (FreeGroup.of (Sum.inr d))=if d ∈ s then FreeGroup.of d else 1 := by
  simp [gradedDegree]
@[simp] lemma gradedDegree_empty (q : FreeGroup (C ⊕ D)) : gradedDegree ∅ q=1 := by
  have hhom : gradedDegree (C := C) (∅:Finset D)=1 := by
    apply FreeGroup.ext_hom
    intro x
    cases x <;> simp
  rw [hhom]
  rfl

def splitNew (d : D) : C ⊕ D → FreeGroup (C ⊕ D) ⊕ Multiplicative ℤ :=
  Sum.elim (fun c => Sum.inl (FreeGroup.of (Sum.inl c)))
    (fun j => if j=d then Sum.inr (Multiplicative.ofAdd 1) else Sum.inl (FreeGroup.of (Sum.inr j)))

lemma degree_splitNew (s : Finset D) (d : D) (x : C ⊕ D) :
    gradedDegree (insert d s) (FreeGroup.of x)=
      Sum.elim (gradedDegree s) (zpowersHom (FreeGroup D) (FreeGroup.of d)) (splitNew d x) := by
  cases x with
  | inl c => simp [splitNew]
  | inr j =>
    by_cases hj : j=d
    · subst j; simp [splitNew,zpowersHom]
    · simp [splitNew,hj]

lemma powerFamily_star {A : Type*} [CStarAlgebra A] (w : unitary A) (h : Multiplicative ℤ) :
    star (powerFamily w h)=powerFamily w h⁻¹ := by
  change star ((w^h.toAdd : unitary A):A)=((w^(-h.toAdd) : unitary A):A)
  rw [zpow_neg,← Unitary.coe_star,Unitary.star_eq_inv]

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
def mixedFamily (v : C → unitary M) (u : D → unitary M) : FreeGroup (C ⊕ D) →* unitary M :=
  FreeGroup.lift (Sum.elim v u)

def updateFamily (u : ℕ → D → unitary M) (w : ℕ → unitary M) (d : D) : ℕ → D → unitary M :=
  fun n j => if j=d then w n else u n j

lemma mixedFamily_splitNew (v : C → unitary M) (u : ℕ → D → unitary M) (w : ℕ → unitary M)
    (d : D) (x : C ⊕ D) :
    quotientFamily τ h1 ω htr (fun n => mixedFamily v (updateFamily u w d n)) (FreeGroup.of x)=
      Sum.elim (quotientFamily τ h1 ω htr (fun n => mixedFamily v (u n)))
        (powerFamily (quotientUnitary τ h1 ω htr w)) (splitNew d x) := by
  cases x with
  | inl c =>
    change quotientHom τ h1 ω htr (boundedHom _ (FreeGroup.of (Sum.inl c)))=
      quotientHom τ h1 ω htr (boundedHom _ (FreeGroup.of (Sum.inl c)))
    congr 1
  | inr j =>
    by_cases hj : j=d
    · subst j
      simp only [splitNew,Sum.elim_inr,ite_true,powerFamily_apply]
      change _ = (((quotientUnitary τ h1 ω htr w) ^ (1:ℤ) : unitary (Ultrapower τ h1 ω htr)) : Ultrapower τ h1 ω htr)
      rw [zpow_one]
      change quotientHom τ h1 ω htr (boundedHom _ (FreeGroup.of (Sum.inr d)))=
        quotientHom τ h1 ω htr (unitarySequence w)
      congr 1
      ext n
      simp [mixedFamily,updateFamily]
    · simp only [splitNew,Sum.elim_inr,hj,ite_false,Sum.elim_inl]
      change quotientHom τ h1 ω htr (boundedHom _ (FreeGroup.of (Sum.inr j)))=
        quotientHom τ h1 ω htr (boundedHom _ (FreeGroup.of (Sum.inr j)))
      congr 1
      ext n
      simp [mixedFamily,updateFamily,hj]

lemma mixedFamily_splitNew_inv (v : C → unitary M) (u : ℕ → D → unitary M) (w : ℕ → unitary M)
    (d : D) (x : C ⊕ D) :
    quotientFamily τ h1 ω htr (fun n => mixedFamily v (updateFamily u w d n)) ((FreeGroup.of x)⁻¹)=
      Sum.elim (quotientFamily τ h1 ω htr (fun n => mixedFamily v (u n)))
        (powerFamily (quotientUnitary τ h1 ω htr w)) (invLetter (splitNew d x)) := by
  rw [← quotientFamily_star,mixedFamily_splitNew]
  cases h : splitNew d x with
  | inl g => exact quotientFamily_star τ h1 ω htr _ g
  | inr k => exact powerFamily_star _ k
end HochschildUltrapower

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open BoundedHochschild HochschildRigidity HochschildPatching HochschildComparison HochschildSplitWord
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
 

theorem exists_finite_graded_family
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    {C D : Type*} [Countable C] [Countable D] [DecidableEq D]
    (v : C → unitary M) (s : Finset D) :
    ∃ u : ℕ → D → unitary M, ∀ q : FreeGroup (C ⊕ D), gradedDegree s q ≠ 1 →
      quotientTrace τ h1 ω htr (quotientFamily τ h1 ω htr (fun n => mixedFamily v (u n)) q)=0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ _ => 1,fun q hq => ?_⟩
    exact (hq (gradedDegree_empty q)).elim
  | @insert d s hd ih =>
    obtain ⟨u,hu⟩ := ih
    let ν : ℕ → FreeGroup (C ⊕ D) →* unitary M := fun n => mixedFamily v (u n)
    obtain ⟨w,hpower,hfree⟩ := exists_free_haar_extension e τ hτ h1 htr hfaith hfactor hdiff ω hω ν
    refine ⟨updateFamily u w d,fun q hq => ?_⟩
    let U := quotientFamily τ h1 ω htr ν
    let W := quotientUnitary τ h1 ω htr w
    let V := powerFamily W
    let T := quotientTrace τ h1 ω htr
    let β := zpowersHom (FreeGroup D) (FreeGroup.of d)
    let l := splitWord (splitNew (C := C) d) q
    have hev : sumProduct U V l=
        quotientFamily τ h1 ω htr (fun n => mixedFamily v (updateFamily u w d n)) q :=
      sumProduct_splitWord U V _ (splitNew d)
        (mixedFamily_splitNew τ h1 ω htr v u w d)
        (mixedFamily_splitNew_inv τ h1 ω htr v u w d) q
    have hdeg : HochschildGradedFree.degree (gradedDegree s) β l=gradedDegree (insert d s) q :=
      sumProduct_splitWord_group (gradedDegree s) β (gradedDegree (insert d s)) (splitNew d)
        (degree_splitNew s d) q
    have hβ (k : Multiplicative ℤ) (hk : β k ≠ 1) : T (V k)=0 := by
      apply hpower k.toAdd
      intro hzero
      apply hk
      simp [β,zpowersHom,hzero]
    have hz := HochschildGradedFree.moment_eq_zero_of_degree_ne_one U V (gradedDegree s) β T.toLinearMap
      (quotientTrace_tracial τ h1 ω htr) hu hβ hfree l (fun hh => hq (hdeg.symm.trans hh))
    change T (sumProduct U V l)=0 at hz
    rw [hev] at hz
    exact hz

end HochschildUltrapower
end

end OAI
