import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ProgramDemand

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

def checkMarkedTrace : List (Bool × ExposureTree K V (Bool × Bool × List R)) →
    ExposureTree K V (Bool × Bool × List R)
  | [] => .done (true,true,[])
  | a :: as => bind a.2 (fun z =>
      if z.1 then .done (false,((!a.1)||z.2.1) && !(as.any Prod.fst),z.2.2)
      else mapOutput (fun y => (y.1,((!a.1)||z.2.1) && y.2.1,z.2.2 ++ y.2.2))
        (checkMarkedTrace as))

lemma programDemand_marked_trace (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    programDemand (as.map (fun a => (a.1,mapOutput (fun z => (z.1,z.2.1)) a.2))) =
      as.any Prod.fst := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,programDemand,List.any_cons,ih]

lemma checkMarkedTrace_marked (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    mapOutput (fun z => (z.1,z.2.1)) (checkMarkedTrace as) =
      checkMarked (as.map (fun a => (a.1,mapOutput (fun z => (z.1,z.2.1)) a.2))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarkedTrace,mapOutput_bind,List.map_cons,checkMarked,bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,mapOutput_done,
      mapOutput_comp,programDemand_marked_trace]
    rw [← ih]
    rw [mapOutput_comp]
    rfl

lemma checkMarkedTrace_trace (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    mapOutput (fun z => (z.1,z.2.2)) (checkMarkedTrace as) =
      checkNoneTrace (as.map (fun a => mapOutput (fun z => (z.1,z.2.2)) a.2)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarkedTrace,mapOutput_bind,List.map_cons,checkNoneTrace,bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,mapOutput_done,mapOutput_comp]
    rw [← ih]
    rw [mapOutput_comp]
    rfl

lemma any_fst_false (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    as.any Prod.fst = false ↔ ∀ a ∈ as, a.1 = false := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.any_cons,Bool.or_eq_false_iff,ih,List.forall_mem_cons]

theorem checkMarkedTrace_no_demands (ν : K → PMF V)
    (as : List (Bool × ExposureTree K V (Bool × Bool × List R)))
    (ha : as.any Prod.fst = false)
    {z : Bool × Bool × List R} (hz : z ∈ (fresh ν (checkMarkedTrace as)).support) :
    z.2.1 = true := by
  induction as generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    subst z
    rfl
  | cons a as ih =>
    have haa := Bool.or_eq_false_iff.mp ha
    rw [checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    by_cases hx : x.1 = true
    · simp only [hx,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      simp only [haa.1,haa.2,Bool.not_false,Bool.true_or,Bool.and_self]
    · simp only [hx,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      simp only [haa.1,Bool.not_false,Bool.true_or,Bool.true_and]
      exact ih haa.2 hy

theorem checkMarkedTrace_one_hit (ν : K → PMF V) (P : R → Prop)
    (as : List (Bool × ExposureTree K V (Bool × Bool × List R)))
    (hunique : as.Pairwise (fun a b => a.1 = true → b.1 = false))
    (hchild : ∀ a ∈ as, ∀ z ∈ (fresh ν a.2).support,
      (∃ r ∈ z.2.2, P r) → a.1 = true ∧ z.2.1 = true)
    {z : Bool × Bool × List R} (hz : z ∈ (fresh ν (checkMarkedTrace as)).support)
    (hhit : ∃ r ∈ z.2.2, P r) : as.any Prod.fst = true ∧ z.2.1 = true := by
  induction as generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by simpa only [checkMarkedTrace,fresh,
      PMF.mem_support_pure_iff] using hz
    subst z
    simp only [List.not_mem_nil,false_and,exists_false] at hhit
  | cons a as ih =>
    obtain ⟨hun,hup⟩ := List.pairwise_cons.mp hunique
    rw [checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have haresult := hchild a (List.mem_cons_self) x hx
    have htail := fun a ha => hchild a (List.mem_cons_of_mem _ ha)
    have hnodemand (ha : a.1 = true) : as.any Prod.fst = false :=
      (any_fst_false as).mpr (fun b hb => hun b hb ha)
    by_cases hxv : x.1 = true
    · simp only [hxv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      obtain ⟨ha,hgood⟩ := haresult hhit
      simp only [List.any_cons,ha,hgood,hnodemand ha,Bool.true_or,Bool.not_false,
        Bool.or_true,Bool.and_self,and_self]
    · simp only [hxv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      obtain ⟨r,hr,hPr⟩ := hhit
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨ha,hgood⟩ := haresult ⟨r,hr,hPr⟩
        have hygood := checkMarkedTrace_no_demands ν as (hnodemand ha) hy
        simp only [List.any_cons,ha,hgood,hygood,Bool.true_or,Bool.or_true,
          Bool.and_self,and_self]
      · obtain ⟨hd,hgood⟩ := ih hup htail hy ⟨r,hr,hPr⟩
        have ha : a.1 = false := by
          cases hh : a.1
          · rfl
          · have hh' := hnodemand hh
            rw [hh'] at hd
            contradiction
        simp only [List.any_cons,ha,hgood,hd,Bool.false_or,Bool.not_false,
          Bool.true_or,Bool.and_self,and_self]

end SharpTerminalLeave.ExposureTree

end

end OAI
