import OAI.NumberTheory.CubicMoment.Estimates.CubeFrequencies

namespace OAI

/-!
# Three-to-one summation of cube frequencies

This is the exact multiplicity correction before estimating the cube
lattice. Summability is stated explicitly so that regrouping is valid.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma cube_fiber_sum (F : Eisenstein → ℂ) (h : Eisenstein) :
    (∑' j : {j : Eisenstein // j^3 = h},
      if (j : Eisenstein) = 0 then 0 else F ((j : Eisenstein)^3)) =
      if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then 3*F h else 0 := by
  by_cases hh : h = 0
  · subst h
    rw [ite_eq_right (by simp)]
    have hz : (fun j : {j : Eisenstein // j^3 = 0} =>
        if (j : Eisenstein) = 0 then (0:ℂ) else F ((j : Eisenstein)^3)) = fun _ => 0 := by
      funext j
      have hj : (j : Eisenstein) = 0 := (pow_eq_zero_iff (by norm_num : (3:ℕ) ≠ 0)).mp j.property
      simp [hj]
    rw [hz,tsum_zero]
  · by_cases hex : ∃ j : Eisenstein, j^3 = h
    · obtain ⟨y,hy⟩ := hex
      have hy0 : y ≠ 0 := by intro hy0; apply hh; rw [← hy,hy0]; simp
      have hfinite : {j : Eisenstein | j^3 = h}.Finite := by
        rw [← hy,cube_fiber_eq]
        exact Set.toFinite _
      let : Fintype {j : Eisenstein // j^3 = h} := hfinite.fintype
      have hcard : Fintype.card {j : Eisenstein // j^3 = h} = 3 := by
        rw [← Nat.card_eq_fintype_card]
        change {j : Eisenstein | j^3 = h}.ncard = 3
        rw [← hy]
        exact cube_fiber_card hy0
      rw [ite_eq_left ⟨hh,⟨y,hy⟩⟩]
      calc
        _ = ∑ j : {j : Eisenstein // j^3 = h}, F h := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro j hj
          have hj0 : (j : Eisenstein) ≠ 0 := by
            intro hz
            apply hh
            rw [← j.property,hz]
            simp
          rw [ite_eq_right hj0,j.property]
        _ = 3*F h := by simp [hcard]
    · rw [ite_eq_right (by simp [hex])]
      let : IsEmpty {j : Eisenstein // j^3 = h} := ⟨fun j => hex ⟨j,j.property⟩⟩
      exact tsum_empty

/-- Regrouping the nonzero cubes divides their lattice parametrization
by exactly three. No asymptotic estimate enters this identity. -/
theorem tsum_nonzero_cubes (F : Eisenstein → ℂ)
    (hF : Summable (fun j : Eisenstein => if j = 0 then 0 else F (j^3))) :
    (∑' j : Eisenstein, if j = 0 then 0 else F (j^3)) =
      3*(∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then F h else 0) := by
  calc
    _ = ∑' h : Eisenstein, ∑' j : {j : Eisenstein // j^3 = h},
        if (j : Eisenstein) = 0 then 0 else F ((j : Eisenstein)^3) :=
      (hF.hasSum.tsum_fiberwise (fun j : Eisenstein => j^3)).tsum_eq.symm
    _ = ∑' h : Eisenstein,
        if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then 3*F h else 0 :=
      tsum_congr (cube_fiber_sum F)
    _ = _ := by
      calc
        _ = ∑' h : Eisenstein, 3*(if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then F h else 0) := by
          apply tsum_congr
          intro h
          split_ifs <;> simp
        _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
