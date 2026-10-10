import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement

namespace OAI

/-! Exact scalar dyadic cell fibers for the porous grouping step. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def scalarGridFiber (η z : ℝ) (E : Finset ℝ) (k : ℤ) : Finset ℝ :=
  E.filter fun x => ⌊(x-z)/η⌋ = k

 theorem scalarGridFiber_mono (η z : ℝ) {E F : Finset ℝ} (hEF : E ⊆ F) (k : ℤ) :
    scalarGridFiber η z E k ⊆ scalarGridFiber η z F k :=
  Finset.filter_subset_filter _ hEF

 theorem scalarGridFiber_small {η μ z : ℝ} (hη : 0 < η) (hημ : η ≤ μ)
    (E : Finset ℝ) (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → μ ≤ |x-y|) (k : ℤ) :
    (scalarGridFiber η z E k).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hx,hxk⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy,hyk⟩ := Finset.mem_filter.mp hy
  by_contra hne
  have he := same_scalar_cell_dist_lt hη (hxk.trans hyk.symm)
  have hid : (x-z)-(y-z) = x-y := by ring
  rw [hid] at he
  exact (not_lt_of_ge ((hημ.trans (hsep x hx y hy hne)))) he

 theorem scalarGridFiber_double_subset (η z : ℝ) (E : Finset ℝ) (k : ℤ) :
    scalarGridFiber (2*η) z E k ⊆
      scalarGridFiber η z E (2*k) ∪ scalarGridFiber η z E (2*k+1) := by
  intro x hx
  obtain ⟨hx,hxk⟩ := Finset.mem_filter.mp hx
  have hid : (x-z)/(2*η) = ((x-z)/η)/2 := by ring
  rw [hid] at hxk
  have hf := Int.floor_div_natCast ((x-z)/η) 2
  norm_num only [Nat.cast_ofNat] at hf
  rw [hf] at hxk
  have he : ⌊(x-z)/η⌋ = 2*k ∨ ⌊(x-z)/η⌋ = 2*k+1 := by omega
  rcases he with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,h⟩)

 theorem scalarGridFiber_double_card (η z : ℝ) (E : Finset ℝ) (k : ℤ) :
    (scalarGridFiber (2*η) z E k).card ≤
      (scalarGridFiber η z E (2*k)).card+(scalarGridFiber η z E (2*k+1)).card :=
  (Finset.card_le_card (scalarGridFiber_double_subset η z E k)).trans (Finset.card_union_le _ _)

 theorem scalarGridFiber_wide {η z : ℝ} (hη : 2 < η) (E : Finset ℝ)
    (hE : ∀ x ∈ E, 0 ≤ x-z ∧ x-z ≤ 2) : scalarGridFiber η z E 0 = E := by
  apply Finset.filter_eq_self.mpr
  intro x hx
  have hη0 : 0 < η := by linarith
  apply Int.floor_eq_zero_iff.mpr
  exact ⟨div_nonneg (hE x hx).1 hη0.le,(div_lt_one hη0).2 ((hE x hx).2.trans_lt hη)⟩

 theorem scalar_grid_sum (η z : ℝ) (X : Finset ℝ) (f : ℤ → ℝ → ℝ) :
    (∑ k ∈ X.image (fun x => ⌊(x-z)/η⌋), ∑ x ∈ scalarGridFiber η z X k, f k x) =
      ∑ x ∈ X, f ⌊(x-z)/η⌋ x := by
  classical
  calc
    _ = ∑ k ∈ X.image (fun x => ⌊(x-z)/η⌋),
        ∑ x ∈ scalarGridFiber η z X k, f ⌊(x-z)/η⌋ x := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun x hx => Finset.mem_image_of_mem (fun x => ⌊(x-z)/η⌋) hx) _

end Falconer

end OAI
