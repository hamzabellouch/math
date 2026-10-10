import OAI.NumberTheory.Ostmann.Construction.InitialEtaState

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta
open InitialCoordinatesTemplate

variable {giant bulk spectator : PrimeSource} {b s k : ℕ}
  {aux : AuxiliaryIndex k → PrimeSource}

theorem jointState_templateAt (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    (jointState x freq).TemplateAt 0 := by
  intro q hq j hj
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact initial_seed_types_pos (2*b) k ((Template.initial (2*b) k)[i])
    (List.getElem_mem i.isLt) j hj

theorem jointState_small_prod {M : Type*} [CommMonoid M] (f : ℕ → M)
    (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    ((jointState x freq).small.map fun q => f q.value).prod =
      ∏q : SmallShape b k, f (tupleValues x (smallPosition q)) := by
  change ((assignedSlots (initialSources bulk aux b) (Template.initial (2*b) k)
    (sourceEquiv giant bulk spectator aux x).2.2.2).map fun q => f q.value).prod = _
  simp only [assignedSlots,Template.sample,List.map_ofFn,List.prod_ofFn]
  rw [←(smallIndex b k).prod_comp]
  apply Finset.prod_congr rfl
  intro q hq
  exact congrArg f (sourceEquiv_small giant bulk spectator aux x q)

theorem jointOutside_prod {M : Type*} [CommMonoid M] (f : ℕ → M)
    (x : JointSample giant bulk spectator aux b s) :
    ((jointOutside x).map f).prod = ∏h,∏i,f ((halfAt x h).2.2.1 i) := by
  simp only [jointOutside,spectatorList,List.map_ofFn,List.prod_ofFn]
  rw [←(halfEquiv s).prod_comp]
  simp only [Function.comp_def,sourceEquiv_spectator,Fintype.prod_prod_type]

theorem jointState_values_prod {M : Type*} [CommMonoid M] (f : ℕ → M)
    (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    (((jointState x freq).values ++ jointOutside x).map f).prod =
      ∏i,f (tupleValues x i) := by
  simp only [State.values,List.map_append,List.map_cons,List.prod_append,List.prod_cons,
    List.map_map,Function.comp_def,jointState_plus,jointState_minus]
  rw [jointState_small_prod,jointOutside_prod]
  simp only [Fintype.prod_prod_type,Fintype.prod_bool,Fintype.prod_sum_type,Fintype.prod_unique,
    tupleValues,tupleSample,tupleSource,halfSource,halfSample,smallPosition,halfAt,
    Bool.false_eq_true,ite_false,ite_true,Finset.prod_mul_distrib]
  ac_rfl

theorem jointState_period (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    outsideProduct (jointOutside x) * (jointState x freq).product = tuplePeriod x := by
  have h := jointState_values_prod (fun n : ℕ => n) x freq
  change (List.map (id : ℕ → ℕ) ((jointState x freq).values ++ jointOutside x)).prod = _ at h
  rw [List.map_id,List.prod_append] at h
  exact (mul_comm _ _).trans h

def tupleList (x : JointSample giant bulk spectator aux b s) : List ℕ :=
  List.ofFn (fun i => tupleValues x ((Fintype.equivFin (Position b s (AuxiliaryIndex k))).symm i))

private theorem singleton_prod (l : List ℕ) :
    (l.map (fun n => Multiplicative.ofAdd ({n}:Multiset ℕ))).prod =
      Multiplicative.ofAdd (l:Multiset ℕ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    rfl

theorem jointState_values_perm (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    ((jointState x freq).values ++ jointOutside x).Perm (tupleList x) := by
  have h := jointState_values_prod (fun n => Multiplicative.ofAdd ({n}:Multiset ℕ)) x freq
  rw [singleton_prod] at h
  have ht : ((tupleList x).map (fun n => Multiplicative.ofAdd ({n}:Multiset ℕ))).prod =
      ∏i,Multiplicative.ofAdd ({tupleValues x i}:Multiset ℕ) := by
    simp only [tupleList,List.map_ofFn,List.prod_ofFn]
    exact (Fintype.equivFin (Position b s (AuxiliaryIndex k))).symm.prod_comp
      (fun i => Multiplicative.ofAdd ({tupleValues x i}:Multiset ℕ))
  rw [←ht,singleton_prod] at h
  exact Multiset.coe_eq_coe.mp (congrArg Multiplicative.toAdd h)

theorem jointState_nodup_iff (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    ((jointState x freq).values ++ jointOutside x).Nodup ↔ Function.Injective (tupleValues x) := by
  rw [(jointState_values_perm x freq).nodup_iff]
  simp only [tupleList,List.nodup_ofFn]
  constructor
  · intro h i j hij
    apply (Fintype.equivFin (Position b s (AuxiliaryIndex k))).injective
    apply h
    simpa only [Equiv.symm_apply_apply] using hij
  · intro h
    exact h.comp (Fintype.equivFin (Position b s (AuxiliaryIndex k))).symm.injective

end Ostmann.Construction.InitialEta

end

end OAI
