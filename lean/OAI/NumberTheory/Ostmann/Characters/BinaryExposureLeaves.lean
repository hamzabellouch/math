import OAI.NumberTheory.Ostmann.Characters.BinaryExposureTree

namespace OAI

noncomputable section
namespace Ostmann.Characters.BinaryExposure
attribute [local instance] Classical.propDecidable

theorem avg_equiv {α β:Type*} [Fintype α] [Fintype β] (e:α≃β) (f:β→ℝ) :
    avg (fun x=>f (e x))=avg f := by
  unfold avg
  rw [Fintype.card_congr e,Equiv.sum_comp e f]

variable {G H:Type*} [Group G] [Fintype G]

@[reducible] def leafAdmissible (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H)
    (k:ℕ) (h:H) (x:BinaryHaar.Leaves G k) : Prop :=
  admissible c left right k h (BinaryHaar.product (G:=G) x) ((BinaryHaar.expose (G:=G) k x).2)

theorem leaf_count_eq_average (c:ℕ→H→G→G→Prop)
    (left right:ℕ→H→G→G→H) (k:ℕ) (h:H) :
    (Nat.card {x:BinaryHaar.Leaves G k // leafAdmissible c left right k h x}:ℝ)/
      Nat.card (BinaryHaar.Leaves G k)=avg (fun t:G=>probability c left right k h t) := by
  calc
    _ = avg (fun x:BinaryHaar.Leaves G k=>
        if leafAdmissible c left right k h x then 1 else 0) := (avg_indicator _).symm
    _ = avg (fun z:G×BinaryHaar.Splits G k=>
        if admissible c left right k h z.1 z.2 then 1 else 0) := by
      convert avg_equiv (BinaryHaar.expose (G:=G) k)
        (fun z:G×BinaryHaar.Splits G k=>
          if admissible c left right k h z.1 z.2 then 1 else 0) using 1
      simp only [leafAdmissible,BinaryHaar.expose_first]
    _ = avg (fun t:G=>probability c left right k h t) := by
      rw [avg_prod]
      apply congrArg avg
      funext t
      exact (avg_indicator _).trans (probability_eq_count c left right k h t).symm

theorem leaf_count_le_tree (c:ℕ→H→G→G→Prop)
    (left right:ℕ→H→G→G→H) (k:ℕ) (h:H) (b:Budget k)
    (hc:∀t,Controlled c left right k h t b) :
    (Nat.card {x:BinaryHaar.Leaves G k // leafAdmissible c left right k h x}:ℝ)/
      Nat.card (BinaryHaar.Leaves G k)≤(b.value:ℝ) := by
  rw [leaf_count_eq_average]
  calc
    _ ≤ avg (fun _:G=>(b.value:ℝ)) :=
      avg_mono _ _ (fun t=>probability_le_tree c left right k h t b (hc t))
    _ = _ := avg_const _

end Ostmann.Characters.BinaryExposure

end

end OAI
