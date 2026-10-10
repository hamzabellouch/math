import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMap

namespace OAI

                                      
section

noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEq : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem indicator_ne {J : Type*} (a b : J) : indicator a b=(if a≠b then (1:ℝ) else 0) := by
  by_cases he : a=b <;> simp [indicator,he]

def component (D : Data X N H) (ω : Tape D) (t : ℕ) (p : X) : Option (Fin H) → Option (Label D)
  | none => D.heavyKey ω t p
  | some i => D.tierKey ω t i p

theorem first_components (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p : X) :
    first (is.map some) (D.component ω t p)=first is (fun i => D.tierKey ω t i p) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons,first,component,ih]

theorem priority_bound (D : Data X N H) (is js : List (Fin H)) (ω : Tape D) (t : ℕ) (p q : X)
    (hc : ∃ i∈is, (D.tierKey ω t i p).isSome=true) :
    indicator (D.key (is++js) ω t p) (D.key (is++js) ω t q)≤
      indicator (D.heavyKey ω t p) (D.heavyKey ω t q)+
        (is.map (fun i => indicator (D.tierKey ω t i p) (D.tierKey ω t i q))).sum := by
  have hcov : ∃ i∈none::is.map some, ((D.component ω t p) i).isSome=true := by
    obtain ⟨i,hi,hf⟩ := hc
    exact ⟨some i,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩),hf⟩
  have hb := covered_prefix_bound (none::is.map some) (js.map some)
    (D.component ω t p) (D.component ω t q) (Sum.inr (Sum.inr p)) (Sum.inr (Sum.inr q)) hcov
  have hmap : (is.map some).map (fun i => indicator (D.component ω t p i) (D.component ω t q i))=
      is.map (fun i => indicator (D.tierKey ω t i p) (D.tierKey ω t i q)) := by
    simp only [List.map_map,Function.comp_def,component]
  simpa only [List.cons_append,←List.map_append,FirstStructure.key,first,component,
    first_components,List.map_cons,List.sum_cons,hmap,Data.key,List.map_map,Function.comp_def] using hb

theorem tier_coverage (D : Data X N H) (n : Fin N) (i : Fin H) (hi : D.qualify i n) (ω : Tape D) :
    (D.tierKey ω (n.val+1) i (D.center n)).isSome=true := by
  simpa only [tierKey,TierLabeledKeys.key,Option.isSome_map] using
    TierKeyProcess.coverage D.r D.positive (D.K i) (D.two i) (D.qualify i) D.center n hi
      (ω.2 i).1 (ω.2 i).2

theorem heavy_separation (D : Data X N H) (t : ℕ) (ht : t≤N) (p q : X) :
    D.law.expect (fun ω => indicator (D.heavyKey ω t p) (D.heavyKey ω t q))≤dist p q/D.r := by
  have hm := D.law.expect_mono _ _ (fun ω =>
    indicator_map (fun o => o.map (Sum.inl : HeavySlot X → Label D))
      (HeavyRecords.key (D.heavyState ω.1 t) p) (HeavyRecords.key (D.heavyState ω.1 t) q))
  change D.law.expect _≤D.law.expect (fun ω => indicator
    (HeavyRecords.key (D.heavyState ω.1 t) p) (HeavyRecords.key (D.heavyState ω.1 t) q)) at hm
  apply hm.trans
  rw [law,Law.expect_prod _ _ (fun a _ => indicator (HeavyRecords.key (D.heavyState a t) p) (HeavyRecords.key (D.heavyState a t) q))]
  simp only [Law.expect_const]
  have he := HeavyProcess.at_separation (Λ:=HeavySlot X) D.base D.positive (by simp [HeavySlot]) D.heavyFlag D.point N t ht p q
  convert he using 1
  apply Law.expect_congr
  intro ω
  by_cases hh : HeavyRecords.key (D.heavyState ω t) p=HeavyRecords.key (D.heavyState ω t) q
  · simp only [indicator,heavyState] at hh ⊢
    simp only [hh,ne_eq,not_true_eq_false,ite_false,ite_true]
  · simp only [indicator,heavyState] at hh ⊢
    simp only [hh,ne_eq,not_false_eq_true,ite_true,ite_false]

theorem tier_separation (D : Data X N H) (t : ℕ) (i : Fin H) (p q : X) (hpq : dist p q<D.r/4) :
    D.law.expect (fun ω => indicator (D.tierKey ω t i p) (D.tierKey ω t i q))≤
      2*Real.log (1+(D.K i:ℝ)^2)*dist p q/D.r := by
  have hm := D.law.expect_mono _ _ (fun ω =>
    (indicator_map (fun o => o.map (fun l => (Sum.inr (Sum.inl ⟨i,l⟩) : Label D)))
      (TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p)
      (TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 q)).trans
    (indicator_map (fun o => o.map (TierLabels.labels D.r (D.K i) (D.qualify i) D.center t).label)
      (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p)
      (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 q)))
  change D.law.expect _≤D.law.expect (fun ω => indicator
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p)
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 q)) at hm
  apply hm.trans
  rw [law,Law.expect_prod _ _ (fun (_ : HeavyTape D) (b : ∀ j, TierTape D j) => indicator (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (b i).1 (b i).2 p) (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t (b i).1 (b i).2 q))]
  simp only [Law.expect_const]
  rw [Law.expect_pi_coordinate D.tierLaw i (fun a => indicator
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 p)
    (TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 q))]
  have he := TierKeyProcess.separation D.r D.positive (D.K i) (D.two i) (D.quota i)
    (D.qualify i) D.center t p q hpq
  convert he using 1
  apply Law.expect_congr
  intro a
  by_cases hh : TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 p=
      TierKeyProcess.key D.r (D.K i) (D.qualify i) D.center t a.1 a.2 q
  · simp [indicator,hh]
  · simp [indicator,hh]

theorem expect_list_sum {Ω I : Type*} [Fintype Ω] (P : Law Ω) (is : List I) (f : I → Ω → ℝ) :
    P.expect (fun ω => (is.map (fun i => f i ω)).sum)=(is.map (fun i => P.expect (f i))).sum := by
  induction is with
  | nil => simp only [List.map_nil,List.sum_nil,Law.expect_const]
  | cons i is ih => simp only [List.map_cons,List.sum_cons,Law.expect_add,ih]

/-- Only the prefix through a qualifying tier is charged. In particular this
is not the number of levels times a worst-case tier coefficient. -/
theorem prefix_separation (D : Data X N H) (is js : List (Fin H)) (n : Fin N)
    (hq : ∃ i∈is, D.qualify i n) (p : X) (hp : dist (D.center n) p<D.r/4) :
    D.law.expect (fun ω => indicator (D.key (is++js) ω (n.val+1) (D.center n))
      (D.key (is++js) ω (n.val+1) p))≤dist (D.center n) p/D.r+
        (is.map (fun i => 2*Real.log (1+(D.K i:ℝ)^2)*dist (D.center n) p/D.r)).sum := by
  have hm := D.law.expect_mono _ _ (fun ω => priority_bound D is js ω (n.val+1) (D.center n) p (by
    obtain ⟨i,hi,hqual⟩ := hq
    exact ⟨i,hi,tier_coverage D n i hqual ω⟩))
  rw [Law.expect_add,expect_list_sum] at hm
  apply hm.trans
  apply add_le_add (heavy_separation D (n.val+1) (by omega) (D.center n) p)
  clear hm hq
  induction is with
  | nil => simp only [List.map_nil,List.sum_nil,le_refl]
  | cons i is ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (tier_separation D (n.val+1) i (D.center n) p hp) ih

end UniformKServer.LevelMap.Data

end


end

end OAI
