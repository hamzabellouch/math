import Mathlib
import OAI.Analysis.BoundedHochschild.RareScales

namespace OAI

/-! Finite additive characters, phase matrices and orthogonality. -/

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
namespace HochschildFinitePhase
variable {I : Type*} [Fintype I]

def character (v : I → ZMod 3) : AddChar (I → ZMod 3) ℂ where
  toFun g := ZMod.stdAddChar (∑ i,v i*g i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' g h := by
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,AddChar.map_add_eq_mul]

lemma character_apply (v g : I → ZMod 3) :
    character v g=ZMod.stdAddChar (∑ i,v i*g i) := rfl

lemma character_zero (g : I → ZMod 3) : character 0 g=1 := by simp [character_apply]
lemma character_add (v w g : I → ZMod 3) :
    character (v+w) g=character v g*character w g := by
  simp only [character_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib,AddChar.map_add_eq_mul]
lemma character_norm (v g : I → ZMod 3) : ‖character v g‖=1 := by
  simp only [character_apply,ZMod.stdAddChar_apply,Circle.norm_coe]
lemma character_star (v g : I → ZMod 3) : star (character v g)=character (-v) g := by
  simp only [character_apply,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,
    AddChar.map_neg_eq_inv,ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj _).symm

lemma character_eq_one_iff (v : I → ZMod 3) : character v=1 ↔ v=0 := by
  classical
  constructor
  · intro h
    ext i
    have hh := congrArg (fun χ : AddChar (I → ZMod 3) ℂ => χ (Pi.single i 1)) h
    simp only [character_apply,AddChar.one_apply] at hh
    have hsum : (∑ j,v j*((Pi.single i (1:ZMod 3) : I → ZMod 3) j))=v i := by
      simp [Pi.single_apply]
    rw [hsum,← (ZMod.stdAddChar : AddChar (ZMod 3) ℂ).map_zero_eq_one] at hh
    exact ZMod.injective_stdAddChar hh
  · rintro rfl
    ext g
    exact character_zero g

variable [DecidableEq I]

lemma sum_character (v : I → ZMod 3) :
    ∑ g,character v g=if v=0 then (Fintype.card (I → ZMod 3):ℂ) else 0 := by
  classical
  by_cases hv : v=0
  · subst v
    simp only [character_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,ite_true]
  · rw [ite_eq_right hv]
    exact AddChar.sum_eq_zero_of_ne_one ((character_eq_one_iff v).not.mpr hv)

lemma orthogonality (v w : I → ZMod 3) :
    ∑ g,star (character v g)*character w g=
      if v=w then (Fintype.card (I → ZMod 3):ℂ) else 0 := by
  classical
  simp only [character_star,← character_add,sum_character]
  congr 1
  exact propext neg_add_eq_zero

lemma character_parseval {J H : Type*} [Fintype J] [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f : J → (I → ZMod 3)) (hf : Function.Injective f) (v : J → H) :
    (∑ g : I → ZMod 3, ‖∑ j, character (f j) g • v j‖^2)=
      (Fintype.card (I → ZMod 3):ℝ)*(∑ j,‖v j‖^2) := by
  classical
  have hh : (∑ g : I → ZMod 3, ⟪∑ j, character (f j) g • v j,
      ∑ j,character (f j) g • v j⟫_ℂ)=
      (Fintype.card (I → ZMod 3):ℂ)*(∑ j,⟪v j,v j⟫_ℂ) := by
    simp only [sum_inner,inner_sum]
    simp only [inner_smul_left,inner_smul_right]
    calc
      _ = ∑ j,∑ k,(∑ g,star (character (f k) g)*character (f j) g)*⟪v k,v j⟫_ℂ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro g hg
        simp only [Complex.star_def]
        ring
      _ = _ := by simp only [orthogonality,hf.eq_iff]; simp [← Finset.mul_sum]
  have hr := congrArg Complex.re hh
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero] at hr
  simpa only [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex] using hr

end HochschildFinitePhase

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildFinitePhase
variable {I : Type*} [DecidableEq I]

def frequency (i j : I) : I → ZMod 3 := Pi.single j 1 - Pi.single i 1

abbrev OffDiagonal (I : Type*) := {p : I × I // p.1 ≠ p.2}

lemma frequency_ne_zero {i j : I} (hij : i ≠ j) : frequency i j ≠ 0 := by
  intro h
  have hh := congrFun h i
  norm_num [frequency,Pi.single_apply,hij,Ne.symm hij] at hh

lemma frequency_injective {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l)
    (h : frequency i j = frequency k l) : i=k ∧ j=l := by
  have hik : i=k := by
    by_contra hik
    have hh := congrFun h i
    by_cases hil : i=l
    · subst l
      norm_num [frequency,Pi.single_apply,hij,Ne.symm hij,hik,Ne.symm hik] at hh
      exact (by decide : (-1 : ZMod 3) ≠ 1) hh
    · norm_num [frequency,Pi.single_apply,hij,Ne.symm hij,hik,Ne.symm hik,hil,Ne.symm hil] at hh
  subst k
  refine ⟨rfl,?_⟩
  by_contra hjl
  have hh := congrFun h j
  norm_num [frequency,Pi.single_apply,hij,Ne.symm hij,hjl,Ne.symm hjl] at hh

def extendedFrequency : Option (OffDiagonal I) → (I → ZMod 3)
  | none => 0
  | some p => frequency p.val.1 p.val.2

lemma extendedFrequency_injective : Function.Injective (extendedFrequency (I:=I)) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (frequency_ne_zero b.property h.symm)
  | some a =>
    cases b with
    | none => exact False.elim (frequency_ne_zero a.property h)
    | some b =>
      have hab := frequency_injective a.property b.property h
      congr 1
      exact Subtype.ext (Prod.ext hab.1 hab.2)

def phase (g : I → ZMod 3) (i : I) : ℂ := ZMod.stdAddChar (g i)

omit [DecidableEq I] in
lemma phase_norm (g : I → ZMod 3) (i : I) : ‖phase g i‖=1 := by
  simp only [phase,ZMod.stdAddChar_apply,Circle.norm_coe]

variable [Fintype I]

lemma character_single (i : I) (g : I → ZMod 3) : character (Pi.single i 1) g=phase g i := by
  simp [character_apply,Pi.single_apply,phase]

lemma character_frequency (i j : I) (g : I → ZMod 3) :
    character (frequency i j) g=star (phase g i)*phase g j := by
  rw [frequency,sub_eq_add_neg,character_add,← character_star]
  simp only [character_single]
  exact mul_comm _ _

lemma offDiagonal_sum {A : Type*} [AddCommMonoid A] (f : I → I → A) :
    (∑ p : OffDiagonal I, f p.val.1 p.val.2)=∑ i,∑ j,if i=j then 0 else f i j := by
  classical
  rw [← Fintype.sum_prod_type (f := fun p : I × I => if p.1=p.2 then (0:A) else f p.1 p.2)]
  change (∑ p : {p : I × I // p.1 ≠ p.2}, f p.val.1 p.val.2)=_
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : I × I => p.1 ≠ p.2)) (by simp)
    (fun p => f p.1 p.2),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

lemma phase_star_self (g : I → ZMod 3) (i : I) : star (phase g i)*phase g i=1 := by
  rw [← character_single i g,character_star,← character_add,neg_add_cancel,character_zero]

lemma extended_sum {A : Type*} [AddCommMonoid A] [Module ℂ A] (c : I → I → A)
    (g : I → ZMod 3) :
    (∑ p : Option (OffDiagonal I),character (extendedFrequency p) g •
      (Option.rec (∑ i,c i i) (fun p : OffDiagonal I => c p.val.1 p.val.2) p))=
      ∑ i,∑ j,(star (phase g i)*phase g j) • c i j := by
  classical
  rw [Fintype.sum_option]
  simp only [extendedFrequency,character_zero,one_smul,character_frequency]
  rw [offDiagonal_sum (fun i j => (star (phase g i)*phase g j) • c i j),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : c i i = ∑ j : I,if i=j then c i i else 0 := by simp
  rw [hd,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,ite_eq_left rfl,add_zero,phase_star_self,one_smul]
  · simp [hij]

lemma phase_parseval {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : I → I → H) :
    (∑ g : I → ZMod 3, ‖∑ i,∑ j,(star (phase g i)*phase g j) • c i j‖^2)=
      (Fintype.card (I → ZMod 3):ℝ)*
        (‖∑ i,c i i‖^2+∑ i,∑ j,if i=j then 0 else ‖c i j‖^2) := by
  let v : Option (OffDiagonal I) → H := fun p => Option.rec (∑ i,c i i)
    (fun p : OffDiagonal I => c p.val.1 p.val.2) p
  calc
    _ = ∑ g : I → ZMod 3,‖∑ p,character (extendedFrequency p) g • v p‖^2 := by
      apply Finset.sum_congr rfl
      intro g hg
      congr 2
      exact (extended_sum c g).symm
    _ = _ := by
      rw [character_parseval extendedFrequency extendedFrequency_injective v]
      simp only [v,Fintype.sum_option]
      rw [offDiagonal_sum (fun i j => ‖c i j‖^2)]

end HochschildFinitePhase
end

end OAI
