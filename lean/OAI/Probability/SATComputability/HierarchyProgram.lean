import OAI.Probability.SATComputability.HierarchyEncoding
import OAI.MathematicalPhysics.RapidForcing.BoundsPrograms

namespace OAI

namespace FixedClauseThreshold.Computability

open Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal
local instance hierarchyProgramRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem branchEntry_computable : Computable branchEntry := by
  have h := Code.computable_recOn (c := id) Computable.id
    (z := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (s := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (l := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (r := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (pr := fun _ _ => ((0 : ℚ), Code.zero)) (by unfold Computable₂; fun_prop)
    (co := fun _ p => (decodedRational p.1, p.2.1)) (by unfold Computable₂; fun_prop)
    (pc := fun _ _ => ((0 : ℚ), Code.zero)) (by unfold Computable₂; fun_prop)
    (rf := fun _ _ => ((0 : ℚ), Code.zero)) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun c => by cases c <;> rfl)

@[fun_prop] theorem rawBranches_computable : Computable rawBranches := by
  have h := Code.computable_recOn (c := id) Computable.id
    (z := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (s := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (l := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (r := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (pr := fun _ p => branchEntry p.1 :: p.2.2.2) (by unfold Computable₂; fun_prop)
    (co := fun _ _ => ([] : List (ℚ × Code))) (by unfold Computable₂; fun_prop)
    (pc := fun _ _ => ([] : List (ℚ × Code))) (by unfold Computable₂; fun_prop)
    (rf := fun _ _ => ([] : List (ℚ × Code))) (by unfold Computable₂; fun_prop)
  apply h.of_eq
  intro c
  induction c <;> simp_all only [rawBranches, id_eq]

attribute [local irreducible] rawBranches

@[fun_prop] theorem normalizedBranches_computable : Computable normalizedBranches := by
  have hm : Computable (fun c => (rawBranches c).map (fun b => |b.1|)) :=
    computable_list_map rawBranches_computable (by unfold Computable₂; fun_prop)
  have hs : Computable (fun c => ((rawBranches c).map (fun b => |b.1|)).sum) :=
    (computable_list_sum computable_rat_add).comp hm
  have hz : CompPred (fun c => ((rawBranches c).map (fun b => |b.1|)).sum = 0) := by
    unfold CompPred
    have he : Computable (fun p : ℚ × ℚ => decide (p.1 = p.2)) := by fun_prop
    exact he.comp (hs.pair (Computable.const 0))
  have hf : Computable (fun c => (rawBranches c).map (fun b =>
      (|b.1| / ((rawBranches c).map (fun x => |x.1|)).sum, b.2))) := by
    apply computable_list_map rawBranches_computable
    unfold Computable₂
    have hd : Computable (fun p : Code × (ℚ × Code) =>
        ((rawBranches p.1).map (fun x => |x.1|)).sum) := hs.comp Computable.fst
    fun_prop
  exact computable_ite hz (Computable.const [(1, Code.zero)]) hf

theorem sum_flatMap_eq {A B : Type*} [AddMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons,
      List.sum_cons, ih]

noncomputable def chooseChildren (cs : List Code) : List (ℚ × List Code) :=
  cs.foldr (fun c rest => (normalizedBranches c).flatMap (fun b =>
    rest.map (fun r => (b.1*r.1, b.2::r.2)))) [(1, [])]

@[fun_prop] theorem chooseChildren_computable : Computable chooseChildren := by
  have hs : Computable (fun p : Code × List (ℚ × List Code) =>
      (normalizedBranches p.1).flatMap (fun b =>
        p.2.map (fun r => (b.1*r.1, b.2::r.2)))) := by
    apply computable_list_flatMap (normalizedBranches_computable.comp Computable.fst)
    unfold Computable₂
    apply computable_list_map (Computable.snd.comp Computable.fst)
    unfold Computable₂
    fun_prop
  exact computable_list_foldr Computable.id (Computable.const [(1, [])])
    (hs.comp Computable.snd).to₂

theorem chooseChildren_nonneg (cs : List Code) : ∀ b ∈ chooseChildren cs, 0 ≤ b.1 := by
  induction cs with
  | nil => simp [chooseChildren]
  | cons c cs ih =>
    intro b hb
    obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (normalizedBranches_nonneg c x hx) (ih y hy)

theorem chooseChildren_sum (cs : List Code) : ((chooseChildren cs).map Prod.fst).sum = 1 := by
  induction cs with
  | nil => simp [chooseChildren]
  | cons c cs ih =>
    change (((normalizedBranches c).flatMap (fun b =>
      (chooseChildren cs).map (fun r => (b.1*r.1, b.2::r.2)))).map Prod.fst).sum = 1
    simp only [List.map_flatMap, sum_flatMap_eq, List.map_map, Function.comp_def,
      List.sum_map_mul_left, ih, mul_one]
    exact normalizedBranches_sum c

theorem chooseChildren_length (cs : List Code) :
    ∀ b ∈ chooseChildren cs, b.2.length = cs.length := by
  induction cs with
  | nil => simp [chooseChildren]
  | cons c cs ih =>
    intro b hb
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simpa only [List.length_cons] using congrArg Nat.succ (ih y hy)

end FixedClauseThreshold.Computability

end OAI
