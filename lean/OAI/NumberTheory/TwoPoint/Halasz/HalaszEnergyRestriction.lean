import OAI.NumberTheory.TwoPoint.Halasz.HalaszCrossMoment

namespace OAI

/-! Removing a bad collection of tuples costs at most twice its
cross-count with all tuples. This keeps both sides of the system good. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical ComplexConjugate

lemma halasz_cross_count_self {α : Type*} {k : ℕ}
    (F : Finset α) (f : α → Fin k → ℤ) :
    halaszCrossCount F F f f=halaszFiberEnergy F f := by
  have h := halasz_cross_integral F F f f
  simp_rw [Complex.mul_conj'] at h
  simp_rw [← Complex.ofReal_pow] at h
  rw [integral_complex_ofReal,halasz_finite_phase_energy] at h
  exact_mod_cast h.symm

lemma halasz_cross_count_symm {α β : Type*} {k : ℕ}
    (F : Finset α) (G : Finset β) (f : α → Fin k → ℤ) (g : β → Fin k → ℤ) :
    halaszCrossCount F G f g=halaszCrossCount G F g f := by
  unfold halaszCrossCount
  simp only [card_eq_sum_ones,sum_filter,sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  simp only [eq_comm]

lemma halasz_cross_count_mono {α β : Type*} {k : ℕ}
    {F F' : Finset α} {G G' : Finset β} (hF : F⊆F') (hG : G⊆G')
    (f : α → Fin k → ℤ) (g : β → Fin k → ℤ) :
    halaszCrossCount F G f g≤halaszCrossCount F' G' f g := by
  apply card_le_card
  exact filter_subset_filter _ (product_subset_product hF hG)

theorem halasz_energy_restriction {α : Type*} {k : ℕ}
    (F G : Finset α) (f : α → Fin k → ℤ) :
    halaszFiberEnergy F f ≤ 2*halaszCrossCount (F\G) F f f + halaszFiberEnergy G f := by
  let A := (((F\G)×ˢF).filter (fun x => f x.1=f x.2))
  let B := ((F×ˢ(F\G)).filter (fun x => f x.1=f x.2))
  let C := ((G×ˢG).filter (fun x => f x.1=f x.2))
  have hc : ((F×ˢF).filter (fun x => f x.1=f x.2)) ⊆ A∪B∪C := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxF := mem_product.mp hx'.1
    by_cases h1 : x.1∈G
    · by_cases h2 : x.2∈G
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr ⟨h1,h2⟩,hx'.2⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr
          ⟨mem_product.mpr ⟨hxF.1,mem_sdiff.mpr ⟨hxF.2,h2⟩⟩,hx'.2⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_sdiff.mpr ⟨hxF.1,h1⟩,hxF.2⟩,hx'.2⟩))
  have hcard : halaszCrossCount F F f f ≤ A.card+B.card+C.card := by
    exact (card_le_card hc).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le A B) _))
  have hb : B.card=A.card := halasz_cross_count_symm F (F\G) f f
  have hC : C.card=halaszFiberEnergy G f := halasz_cross_count_self G f
  rw [halasz_cross_count_self,hb,hC] at hcard
  change _ ≤ 2*A.card+_
  omega

end TwoPointCorrelations

end OAI
