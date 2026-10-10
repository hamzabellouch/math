import Mathlib
import OAI.Geometry.DoublingHilbert.Main

namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach
open DoublingHilbert

@[simp] theorem coordinate_eq_iff (j i m h : ℕ) :
    coordinate j i = coordinate m h ↔ j = m ∧ i = h := by
  constructor
  · intro hh
    exact Prod.mk.inj (coordinate_injective hh)
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem point_apply_zero (p : Base) (w : Tuple) : point p w 0 = p.1 := by
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector, lp.single_apply]
  simp

@[simp] theorem point_apply_one (p : Base) (w : Tuple) : point p w 1 = p.2 := by
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector, lp.single_apply]
  simp

theorem point_apply_coordinate (p : Base) (w : Tuple) (j i : ℕ) :
    point p w (coordinate j i) =
      if w j ≠ 0 ∧ w j - 1 = i then scale j else 0 := by
  classical
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector]
  simp only [lp.single_apply_ne _ _ _ (coordinate_ne_zero j i),
    lp.single_apply_ne _ _ _ (coordinate_ne_one j i), zero_add]
  simp [lp.single_apply, Pi.single_apply, coordinate_eq_iff, ite_and, eq_comm]

                                                                        
theorem exists_coordinate_difference {p q : Base} {w w' : Tuple} {j : ℕ}
    (hj : w j ≠ w' j) :
    ∃ i, |point p w i - point q w' i| = scale j := by
  by_cases hw : w j = 0
  · have hw' : w' j ≠ 0 := by omega
    refine ⟨coordinate j (w' j - 1), ?_⟩
    simp [point_apply_coordinate, hw, hw', abs_of_pos (scale_pos j)]
  · refine ⟨coordinate j (w j - 1), ?_⟩
    have hn : ¬ (w' j ≠ 0 ∧ w' j - 1 = w j - 1) := by omega
    simp [point_apply_coordinate, hw, hn, abs_of_pos (scale_pos j)]

noncomputable def pointSupport (w : Tuple) : Finset ℕ :=
  insert 0 (insert 1 (w.support.image fun j => coordinate j (w j - 1)))

theorem point_apply_of_not_mem_support (p : Base) (w : Tuple) {i : ℕ}
    (hi : i ∉ pointSupport w) : point p w i = 0 := by
  classical
  have h0 : i ≠ 0 := by intro h; subst i; simp [pointSupport] at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp [pointSupport] at hi
  have hj (j : ℕ) (hj : j ∈ w.support) : i ≠ coordinate j (w j - 1) := by
    intro he
    apply hi
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨j, hj, he.symm⟩
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector]
  simp only [lp.single_apply_ne _ _ _ h0, lp.single_apply_ne _ _ _ h1, zero_add]
  exact Finset.sum_eq_zero fun level hlevel => lp.single_apply_ne _ _ _ (hj level hlevel)

theorem finite_coordinate_support (X : Finset RealL2)
    (hX : ∀ z ∈ X, z ∈ constructedSet) :
    ∃ I : Finset ℕ, ∀ z ∈ X, ∀ i ∉ I, z i = 0 := by
  classical
  have h : ∀ z : X, ∃ I : Finset ℕ, ∀ i ∉ I, (z : RealL2) i = 0 := by
    intro z
    obtain ⟨p, w, _, he⟩ := hX z z.property
    refine ⟨pointSupport w, ?_⟩
    intro i hi
    rw [he]
    exact point_apply_of_not_mem_support p w hi
  choose I hI using h
  refine ⟨Finset.univ.biUnion I, ?_⟩
  intro z hz i hi
  apply hI ⟨z, hz⟩ i
  intro hmem
  exact hi (Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, hmem⟩)

end CompactBanach
end

end OAI
