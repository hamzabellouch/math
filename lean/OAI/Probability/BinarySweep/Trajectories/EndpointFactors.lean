import Mathlib
import OAI.Probability.BinarySweep.Trajectories.EndpointPlacement
import OAI.Probability.BinarySweep.Trajectories.EndpointValidity
import OAI.Probability.BinarySweep.FiniteLaws.OccurrenceMoment

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

abbrev EndpointLineIndex (bits : Fin b → ℕ) := Σj, GridOutside bits j

def endpointPathLine {I : Type*} (e : I → GridSlot bits × GridSlot bits)
    (i : I) (j : Fin b) : EndpointLineIndex bits := ⟨j,endpointLine (e i) j⟩

def endpointLineCount {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) : ℕ :=
  Fintype.card {i : A // endpointLine (e i) j=y}

lemma trackedLineCount_restrict (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) (g : ConditionalChoices H)
    (he : ∀i∈A, gridSweep bits g.val (x i).val=(y i).val)
    (j : Fin b) (l : GridOutside bits j) :
    trackedLineCount H (restrictPlacement H x A) g j l =
      endpointLineCount A (fun i => ((x i).val,(y i).val)) j l := by
  apply Fintype.card_congr
  apply ((Fintype.equivFin A).symm).subtypeEquiv
  intro i
  change (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc
    (x ((Fintype.equivFin A).symm i)).val a)=l ↔ _
  rw [gridPartialSweep_endpoint g.val
    ((x ((Fintype.equivFin A).symm i)).val,(y ((Fintype.equivFin A).symm i)).val)
    (he _ ((Fintype.equivFin A).symm i).property)]
  rfl

theorem endpointProbability_zero_scaled (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H 0 A (fun i => ((x i).val,(y i).val)) =
      if EndpointValid H A (fun i => ((x i).val,(y i).val)) then
        ∏j, ∏l : GridOutside bits j,
          fallingMoment (2^bits j) (lineHoles H j l)
            (endpointLineCount A (fun i => ((x i).val,(y i).val)) j l)
      else 0 := by
  by_cases hv : EndpointValid H A (fun i => ((x i).val,(y i).val))
  · rw [ite_eq_left hv]
    obtain ⟨g,hg⟩ := (endpointValid_placement_iff H x y A).mp hv
    have he := (restrictPlacement_event H x y A g).mpr hg
    rw [endpointProbability_placement,← he]
    simpa only [Fintype.card_coe,trackedLineCount_restrict H x y A g hg] using
      placementProbability_zero_scaled H (restrictPlacement H x A) g
  · rw [ite_eq_right hv,endpointProbability_conditional]
    have hz : conditionalEventWeight H 0 (fun g => ∀i∈A,
      gridSweep bits g (x i).val=(y i).val)=0 := by
      unfold conditionalEventWeight
      apply Finset.sum_eq_zero
      intro g _
      rw [ite_eq_right]
      exact fun hg => hv (endpointValid_of_placement_event H x y A g hg)
    rw [hz,mul_zero]

lemma pathLine_occurrences {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) :
    occurrences (fun a : A × Fin b => endpointPathLine e a.1 a.2) ⟨j,y⟩ =
      endpointLineCount A e j y := by
  let : DecidableEq (EndpointLineIndex bits) := Classical.decEq _
  unfold occurrences endpointLineCount
  exact Fintype.card_congr
    {toFun := fun ⟨⟨i,a⟩,ha⟩ => ⟨i,by
       have hj : a=j := congrArg Sigma.fst ha
       subst a
       exact (Sigma.mk.inj ha).2.eq⟩
     invFun := fun a => ⟨(a.val,j),congrArg (Sigma.mk j) a.property⟩
     left_inv := fun ⟨⟨i,a⟩,ha⟩ => by
       have hj : a=j := congrArg Sigma.fst ha
       subst a
       rfl
     right_inv := fun a => rfl}

lemma multilineMoment_X_prod {L A : Type*} [Fintype L] [Fintype A]
    (m h : L → ℕ) (f : A → L) :
    multilineMoment m h (∏a, (MvPolynomial.X (f a) : MvPolynomial L ℝ)) =
      ∏l, fallingMoment (m l) (h l) (occurrences f l) := by
  have hh := occurrenceMoment_eq m h (fun a : Empty => a.elim) f
  simpa only [Finset.univ_eq_empty,Finset.prod_empty,one_mul,occurrences,
    Fintype.card_of_isEmpty,centeredLineMoment_zero] using hh

theorem endpointProbability_zero_polynomial (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H 0 A (fun i => ((x i).val,(y i).val)) =
      if EndpointValid H A (fun i => ((x i).val,(y i).val)) then
        multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
          (fun l => lineHoles H l.1 l.2)
          (∏i : A, ∏j : Fin b, (MvPolynomial.X
            (endpointPathLine (fun i => ((x i).val,(y i).val)) i j) :
            MvPolynomial (EndpointLineIndex bits) ℝ))
      else 0 := by
  rw [endpointProbability_zero_scaled]
  congr 1
  have hp := Fintype.prod_prod_type (fun a : A × Fin b =>
    (MvPolynomial.X (endpointPathLine (fun i => ((x i).val,(y i).val)) a.1 a.2) :
      MvPolynomial (EndpointLineIndex bits) ℝ))
  rw [← hp,multilineMoment_X_prod,Fintype.prod_sigma]
  simp only [pathLine_occurrences]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I R : Type*} [DecidableEq I] [CommRing R]

def mobiusSum (U : Finset I) (f : Finset I → R) : R :=
  ∑A ∈ U.powerset, (-1:R)^(U.card-A.card)*f A

omit [DecidableEq I] in
lemma mobiusSum_empty (f : Finset I → R) : mobiusSum ∅ f=f ∅ := by simp [mobiusSum]

omit [DecidableEq I] in
lemma mobiusSum_congr (U : Finset I) (f g : Finset I → R)
    (hfg : ∀A⊆U, f A=g A) : mobiusSum U f=mobiusSum U g := by
  apply Finset.sum_congr rfl
  intro A hA
  rw [hfg A (Finset.mem_powerset.mp hA)]

omit [DecidableEq I] in
lemma mobiusSum_sub (U : Finset I) (f g : Finset I → R) :
    mobiusSum U (fun A => f A-g A)=mobiusSum U f-mobiusSum U g := by
  simp only [mobiusSum,mul_sub,Finset.sum_sub_distrib]

lemma mobiusSum_insert (U : Finset I) (i : I) (hi : i∉U) (f : Finset I → R) :
    mobiusSum (insert i U) f=mobiusSum U (fun A => f (insert i A)-f A) := by
  unfold mobiusSum
  rw [Finset.sum_powerset_insert hi,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAU := Finset.mem_powerset.mp hA
  have hiA : i∉A := fun ha => hi (hAU ha)
  have hc := Finset.card_le_card hAU
  rw [Finset.card_insert_of_notMem hi,Finset.card_insert_of_notMem hiA]
  rw [show U.card+1-A.card=U.card-A.card+1 by omega,
      show U.card+1-(A.card+1)=U.card-A.card by omega,pow_succ]
  ring

lemma mobiusSum_union (G C : Finset I) (hGC : Disjoint G C) (f : Finset I → R) :
    mobiusSum (G∪C) f=mobiusSum C (fun J => mobiusSum G (fun B => f (J∪B))) := by
  induction C using Finset.induction_on generalizing f with
  | empty => simp only [Finset.union_empty,mobiusSum_empty,Finset.empty_union]
  | @insert i C hi ih =>
    have hiG : i∉G := fun hg => Finset.disjoint_left.mp hGC hg (Finset.mem_insert_self _ _)
    have hGC' : Disjoint G C := hGC.mono_right (Finset.subset_insert _ _)
    have hiU : i∉G∪C := by simp only [Finset.mem_union,not_or]; exact ⟨hiG,hi⟩
    rw [Finset.union_insert,mobiusSum_insert _ _ hiU,mobiusSum_insert _ _ hi]
    rw [ih hGC']
    apply mobiusSum_congr
    intro J _
    rw [← mobiusSum_sub]
    apply mobiusSum_congr
    intro B _
    rw [Finset.insert_union]

variable [Algebra ℝ R]

lemma mobiusSum_linear_product (U : Finset I) (L : R →ₗ[ℝ] ℝ) (X : I → R) (P : R) :
    mobiusSum U (fun A => L (P*∏i∈A, X i))=L (P*∏i∈U, (X i-1)) := by
  induction U using Finset.induction_on generalizing P with
  | empty => simp only [mobiusSum_empty,Finset.prod_empty,mul_one]
  | @insert i U hi ih =>
    rw [mobiusSum_insert _ _ hi,Finset.prod_insert hi]
    trans mobiusSum U (fun A => L ((P*(X i-1))*∏a∈A,X a))
    · apply mobiusSum_congr
      intro A hA
      have hiA : i∉A := fun ha => hi (hA ha)
      rw [Finset.prod_insert hiA,← map_sub]
      congr 1
      ring
    · rw [ih]
      congr 1
      ring

end BinaryCoordinateSweeps.Sparse

end

end OAI
