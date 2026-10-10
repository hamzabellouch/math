import OAI.Analysis.LipschitzEquivalence.BidualSeparation

namespace OAI

universe uA uB

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

structure RowFamily (A : Type uA) where
  accepts : ∀ {n : ℕ}, (Fin n → A) → Prop
  hereditary : ∀ {m n : ℕ} (e : Fin m ↪o Fin n) (v : Fin n → A),
    accepts v → accepts (v ∘ e)

namespace RowFamily
variable {A : Type uA} {B : Type uB}

def Rich (R : RowFamily A) : Prop := ∀ n, ∃ v : Fin n → A, R.accepts v

def restrict (R : RowFamily A) (P : A → Prop) : RowFamily A where
  accepts v := R.accepts v ∧ ∀ i, P (v i)
  hereditary e v h := ⟨R.hereditary e v h.1,fun i => h.2 (e i)⟩

theorem rich_monochromatic [Fintype B] [Nonempty B] (R : RowFamily A) (hR : R.Rich)
    (c : A → B) : ∃ b, (R.restrict (fun a => c a = b)).Rich := by
  classical
  by_contra! h
  have hh : ∀ b : B, ∃ n, ∀ v : Fin n → A, ¬ (R.accepts v ∧ ∀ i, c (v i) = b) := by
    intro b
    simpa only [Rich,restrict,not_forall,not_exists] using h b
  choose N hN using hh
  let k := Finset.univ.sup N
  let m := Fintype.card B*(k+1)
  obtain ⟨v,hv⟩ := hR m
  obtain ⟨b,_,hb⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := Finset.univ) (t := (Finset.univ : Finset B)) (f := fun i : Fin m => c (v i))
    (n := k+1) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by simp [m])
  let s : Finset (Fin m) := Finset.univ.filter (fun i => c (v i) = b)
  have hNb : N b ≤ k := Finset.le_sup (f := N) (Finset.mem_univ b)
  have hcard : N b ≤ s.card := by change N b ≤ (Finset.univ.filter _).card; omega
  let e : Fin (N b) ↪o Fin m :=
    (Fin.castLEOrderEmb hcard).trans (s.orderEmbOfFin rfl)
  apply hN b (v ∘ e)
  refine ⟨R.hereditary e v hv,?_⟩
  intro i
  have hi : e i ∈ s := by
    exact s.orderEmbOfFin_mem rfl _
  exact (Finset.mem_filter.mp hi).2

theorem rich_finite_cover [Fintype B] [Nonempty B] (R : RowFamily A) (hR : R.Rich)
    (P : B → A → Prop) (hP : ∀ a : A, ∃ b, P b a) :
    ∃ b, (R.restrict (P b)).Rich := by
  classical
  choose c hc using hP
  obtain ⟨b,hb⟩ := R.rich_monochromatic hR c
  refine ⟨b,fun n => ?_⟩
  obtain ⟨v,hv,hc'⟩ := hb n
  exact ⟨v,hv,fun i => by simpa only [hc' i] using hc (v i)⟩

end RowFamily
end LipschitzCounterexample.CompactWSC
end

end OAI
