import OAI.NumberTheory.TwoPoint.Halasz.HalaszZeroRepresentation
import Mathlib.Algebra.Order.Chebyshev

namespace OAI

/-! Finite energy under refinement of a partition. This is the counting
form of the Cauchy--Schwarz step that introduces the congruences on the
long variables in the complete-system mean-value argument. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszFiberEnergy {α β : Type*} (F : Finset α) (f : α → β) : ℕ := by
  exact ∑ t ∈ F.image f, (F.filter (fun x => f x=t)).card^2

lemma halasz_fiber_energy_rows {α β : Type*} (F : Finset α) (f : α → β) :
    halaszFiberEnergy F f = ∑ x ∈ F, (F.filter (fun y => f y=f x)).card := by
  unfold halaszFiberEnergy
  calc
    _ = ∑ t ∈ F.image f, ∑ x ∈ F.filter (fun x => f x=t),
        (F.filter (fun y => f y=f x)).card := by
      apply sum_congr rfl
      intro t _
      rw [show (∑ x ∈ F.filter (fun x => f x=t),
          (F.filter (fun y => f y=f x)).card) =
          ∑ _x ∈ F.filter (fun x => f x=t), (F.filter (fun y => f y=t)).card from
        sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])]
      simp [pow_two]
    _ = _ := sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem f hx) _

lemma halasz_fiber_energy_partition {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ) :
    halaszFiberEnergy F (fun x => (f x,g x)) =
      ∑ t ∈ F.image f, halaszFiberEnergy (F.filter (fun x => f x=t)) g := by
  rw [halasz_fiber_energy_rows]
  calc
    _ = ∑ t ∈ F.image f, ∑ x ∈ F.filter (fun x => f x=t),
        (F.filter (fun y => (f y,g y)=(f x,g x))).card := by
      convert (sum_fiberwise_of_maps_to (s := F) (t := F.image f) (g := f)
        (fun x hx => mem_image_of_mem f hx)
        (fun x => (F.filter (fun y => (f y,g y)=(f x,g x))).card)).symm using 1
      apply sum_congr rfl
      intro x _
      congr 1
      ext y
      simp only [mem_filter]
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [halasz_fiber_energy_rows]
      apply sum_congr rfl
      intro x hx
      have hxt := (mem_filter.mp hx).2
      congr 1
      ext y
      simp only [mem_filter,Prod.mk.injEq]
      rw [hxt]
      tauto

lemma halasz_card_sq_le_fiber_energy {α β : Type*} (F : Finset α) (f : α → β) :
    F.card^2 ≤ (F.image f).card * halaszFiberEnergy F f := by
  have h := sq_sum_le_card_mul_sum_sq (s := F.image f)
    (f := fun t => (F.filter (fun x => f x=t)).card)
  rw [← card_eq_sum_card_image f F] at h
  exact h

theorem halasz_fiber_energy_refine {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ) (B : ℕ)
    (hB : ∀ t ∈ F.image f, ((F.filter (fun x => f x=t)).image g).card ≤ B) :
    halaszFiberEnergy F f ≤ B * halaszFiberEnergy F (fun x => (f x,g x)) := by
  rw [halasz_fiber_energy_partition,mul_sum]
  change (∑ t ∈ F.image f, (F.filter (fun x => f x=t)).card^2) ≤ _
  apply sum_le_sum
  intro t ht
  exact (halasz_card_sq_le_fiber_energy _ g).trans
    (Nat.mul_le_mul_right _ (hB t ht))

lemma halasz_fiber_energy_congr {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ)
    (h : ∀ x∈F, ∀ y∈F, f y=f x ↔ g y=g x) :
    halaszFiberEnergy F f = halaszFiberEnergy F g := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows]
  apply sum_congr rfl
  intro x hx
  congr 1
  ext y
  simpa only [mem_filter] using and_congr_right (fun hy => h x hx y hy)

lemma halasz_fiber_energy_mono {α β : Type*} {F G : Finset α} (hFG : F⊆G)
    (f : α → β) : halaszFiberEnergy F f ≤ halaszFiberEnergy G f := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows]
  calc
    _ ≤ ∑ x∈F, (G.filter (fun y => f y=f x)).card := by
      apply sum_le_sum
      intro x _
      exact card_le_card (filter_subset_filter _ hFG)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => Nat.zero_le _)

lemma halasz_fiber_energy_product {α β γ : Type*} (F : Finset α) (G : Finset β)
    (g : β → γ) :
    halaszFiberEnergy (F×ˢG) (fun x => (x.1,g x.2)) = F.card * halaszFiberEnergy G g := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_product]
  have hf (a : α) (ha : a∈F) (b : β) :
      ((F×ˢG).filter (fun y => (y.1,g y.2)=(a,g b))).card =
        (G.filter (fun y => g y=g b)).card := by
    have he : (F×ˢG).filter (fun y => (y.1,g y.2)=(a,g b)) =
        {a}×ˢ(G.filter (fun y => g y=g b)) := by
      ext y
      simp only [mem_filter,mem_product,mem_singleton,Prod.mk.injEq]
      constructor
      · rintro ⟨⟨_,hG⟩,he,hg⟩
        exact ⟨he,hG,hg⟩
      · rintro ⟨he,hG,hg⟩
        exact ⟨⟨he ▸ ha,hG⟩,he,hg⟩
    rw [he,card_product,card_singleton,one_mul]
  calc
    _ = ∑ _a∈F, ∑ b∈G, (G.filter (fun y => g y=g b)).card := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b _
      simpa only [filter_congr_decidable] using hf a ha b
    _ = _ := by simp

lemma halasz_fiber_energy_representation {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) :
    halaszFiberEnergy univ f = halaszRepresentationCount f 0 := by
  rw [halasz_fiber_energy_rows]
  unfold halaszRepresentationCount
  rw [show (univ.filter (fun xy : ι × ι => f xy.1-f xy.2=0)) =
      univ.filter (fun xy : ι × ι => f xy.2=f xy.1) by
    ext xy
    simp only [mem_filter,mem_univ,true_and,sub_eq_zero]
    exact eq_comm]
  simp_rw [card_eq_sum_ones,sum_filter]
  rw [← Fintype.sum_prod_type']
  congr 1
  funext x
  by_cases h : f x.2=f x.1 <;> simp [h]

end TwoPointCorrelations

end OAI
