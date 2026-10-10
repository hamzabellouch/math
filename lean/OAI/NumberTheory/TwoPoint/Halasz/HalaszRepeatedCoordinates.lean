import OAI.NumberTheory.TwoPoint.Halasz.HalaszCrossMoment

namespace OAI

/-! A repeated coordinate in any two prescribed positions is counted
by the same doubled-variable system. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_equiv_two_points {α : Type*} [DecidableEq α]
    {a b i j : α} (hab : a≠b) (hij : i≠j) :
    ∃ e : Equiv.Perm α, e a=i ∧ e b=j := by
  let e := Equiv.swap a i
  have hea : e a=i := Equiv.swap_apply_left _ _
  have hne : a≠e.symm j := by
    intro h
    apply hij
    calc
      i = e a := hea.symm
      _ = e (e.symm j) := congrArg e h
      _ = j := e.apply_symm_apply j
  refine ⟨e.setValue b j,?_,Equiv.setValue_eq _ _ _⟩
  change e (Equiv.swap b (e.symm j) a)=i
  rw [Equiv.swap_apply_of_ne_of_ne hab hne,hea]

lemma halasz_frequency_permute {n k N : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n → Fin N) :
    halaszVinogradovFrequency k (x ∘ e)=halaszVinogradovFrequency k x := by
  funext j
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

def halaszRepeatTuple {n N : ℕ} (a : Fin N) (x : Fin n → Fin N) :
    Fin (n+2) → Fin N := Fin.cons a (Fin.cons a x)

lemma halasz_repeat_tuple_frequency {n k N : ℕ} (a : Fin N) (x : Fin n → Fin N) :
    halaszVinogradovFrequency k (halaszRepeatTuple a x)=
      halaszRepeatedFrequency n k N (a,x) := by
  funext j
  simp only [halaszVinogradovFrequency,halaszRepeatTuple,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,halaszRepeatedFrequency]
  ring

noncomputable def halaszPairCollision (n k N : ℕ) (i j : Fin (n+2)) :
    Finset ((Fin (n+2) → Fin N) × (Fin (n+2) → Fin N)) :=
  univ.filter (fun xy => xy.1 i=xy.1 j ∧
    halaszVinogradovFrequency k xy.1=halaszVinogradovFrequency k xy.2)

lemma halasz_repeat_recover {n N : ℕ} (x : Fin (n+2) → Fin N) (hx : x 0=x 1) :
    halaszRepeatTuple (x 0) (fun a : Fin n => x a.succ.succ)=x := by
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun c => ?_) b
    · exact hx
    · rfl

lemma halasz_canonical_collision_bound (n k N : ℕ) :
    (halaszPairCollision n k N 0 1).card ≤ halaszRepeatedCount n k N := by
  let f (xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N)) :=
    ((xy.1 0,fun a : Fin n => xy.1 a.succ.succ),xy.2)
  let T : Finset ((Fin N × (Fin n → Fin N)) × (Fin (n+2) → Fin N)) :=
    univ.filter (fun x => halaszRepeatedFrequency n k N x.1=halaszVinogradovFrequency k x.2)
  have hmap : Set.MapsTo f (halaszPairCollision n k N 0 1) T := by
    intro xy hxy
    obtain ⟨hc,hv⟩ := (mem_filter.mp hxy).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change halaszRepeatedFrequency n k N (xy.1 0,fun a => xy.1 a.succ.succ) = _
    rw [← halasz_repeat_tuple_frequency,halasz_repeat_recover xy.1 hc]
    exact hv
  have hinj : Set.InjOn f (halaszPairCollision n k N 0 1) := by
    intro xy hxy uv huv heq
    have hc := (mem_filter.mp hxy).2.1
    have hd := (mem_filter.mp huv).2.1
    have ha := congrArg (fun z => z.1.1) heq
    have ht := congrArg (fun z => z.1.2) heq
    have hy := congrArg Prod.snd heq
    change xy.1 0=uv.1 0 at ha
    change (fun a : Fin n => xy.1 a.succ.succ)=
      (fun a : Fin n => uv.1 a.succ.succ) at ht
    change xy.2=uv.2 at hy
    apply Prod.ext _ hy
    rw [← halasz_repeat_recover xy.1 hc,← halasz_repeat_recover uv.1 hd]
    exact congrArg₂ halaszRepeatTuple ha ht
  have h := card_le_card_of_injOn f hmap hinj
  simpa only [T,halaszRepeatedCount,halaszCrossCount,univ_product_univ] using h

theorem halasz_pair_collision_bound {n k N : ℕ} (i j : Fin (n+2)) (hij : i≠j) :
    (halaszPairCollision n k N i j).card ≤ halaszRepeatedCount n k N := by
  obtain ⟨e,he0,he1⟩ := halasz_equiv_two_points
    (show (0 : Fin (n+2))≠1 by
      intro h
      have h' : (0:ℕ)=1 := congrArg Fin.val h
      omega) hij
  let f (xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N)) := (xy.1 ∘ e,xy.2)
  apply le_trans (b := (halaszPairCollision n k N 0 1).card)
  · apply card_le_card_of_injOn f
    · intro xy hxy
      obtain ⟨hc,hv⟩ := (mem_filter.mp hxy).2
      change f xy ∈ halaszPairCollision n k N 0 1
      simp only [halaszPairCollision,mem_filter,mem_univ,true_and,f,
        Function.comp_apply,he0,he1]
      exact ⟨hc,(halasz_frequency_permute e xy.1).trans hv⟩
    · intro xy _ uv _ heq
      have hy := congrArg (fun z : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N) => z.2) heq
      change xy.2=uv.2 at hy
      apply Prod.ext _ hy
      funext a
      have ha := congrFun (congrArg Prod.fst heq) (e.symm a)
      simpa only [f,Function.comp_apply,e.apply_symm_apply] using ha
  · exact halasz_canonical_collision_bound n k N

end TwoPointCorrelations

end OAI
