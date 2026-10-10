import OAI.Geometry.PeriodicTiling.EuclideanBasic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace PeriodicTilingThree

private theorem floor_abs_le_nat {m : ℕ} {x : ℝ} (hx : |x| ≤ (m : ℝ)) :
    |⌊x⌋| ≤ (m : ℤ) := by
  apply abs_le.mpr
  constructor
  · apply Int.le_floor.mpr
    exact_mod_cast (abs_le.mp hx).1
  · have hh : (⌊x⌋ : ℝ) ≤ (m : ℝ) := (Int.floor_le x).trans (abs_le.mp hx).2
    exact_mod_cast hh

private theorem floor_error_lt_one (x : ℝ) : |x - (⌊x⌋ : ℝ)| < 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
  have := Int.lt_floor_add_one x
  linarith

private theorem floor_successor_error_lt_one {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    |x - ((⌊x⌋ + 1 : ℤ) : ℝ)| < 1 := by
  have hlo : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) hx.symm
  have hhi := Int.lt_floor_add_one x
  simp only [Int.cast_add, Int.cast_one]
  apply abs_lt.mpr
  constructor <;> linarith

theorem closed_box_rounding_exists {n : ℕ} (m : ℕ) (hm : 2 ≤ m) (δ : Space n)
    (hδ : ∀ i, |δ i| ≤ (m : ℝ))
    (hnot : ¬ ∃ z : Lattice n, δ = (m : ℝ) • castLattice z) :
    ∃ z : Lattice n,
      (∀ i, |z i| ≤ (m : ℤ)) ∧
      (∃ i, ¬ (m : ℤ) ∣ z i) ∧
      (∀ i, |δ i - (z i : ℝ)| < 1) := by
  classical
  let a : Lattice n := fun i => ⌊δ i⌋
  have habs (i : Fin n) : |a i| ≤ (m : ℤ) := floor_abs_le_nat (hδ i)
  have herr (i : Fin n) : |δ i - (a i : ℝ)| < 1 := floor_error_lt_one (δ i)
  by_cases hdiv : ∀ i, (m : ℤ) ∣ a i
  · have hnonint : ∃ j, δ j ≠ (a j : ℝ) := by
      by_contra h
      have heq (i : Fin n) : δ i = (a i : ℝ) := by
        by_contra hi
        exact h ⟨i, hi⟩
      let z : Lattice n := fun i => Classical.choose (hdiv i)
      have hz (i : Fin n) : a i = (m : ℤ) * z i := Classical.choose_spec (hdiv i)
      apply hnot
      refine ⟨z, ?_⟩
      funext i
      change δ i = (m : ℝ) * (z i : ℝ)
      rw [heq i]
      exact_mod_cast hz i
    obtain ⟨j, hj⟩ := hnonint
    have hjstrict : (a j : ℝ) < δ j := lt_of_le_of_ne (Int.floor_le (δ j)) hj.symm
    have hjlt : a j < (m : ℤ) := by
      have hh : (a j : ℝ) < (m : ℝ) := hjstrict.trans_le (abs_le.mp (hδ j)).2
      exact_mod_cast hh
    let z : Lattice n := Function.update a j (a j + 1)
    refine ⟨z, ?_, ?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst i
        simp only [z, Function.update_self]
        apply abs_le.mpr
        have ha := (abs_le.mp (habs j)).1
        constructor <;> omega
      · simpa only [z, Function.update_of_ne hij] using habs i
    · refine ⟨j, ?_⟩
      simp only [z, Function.update_self]
      intro hsucc
      have hone : (m : ℤ) ∣ 1 := by
        simpa using dvd_sub hsucc (hdiv j)
      have hmle : (m : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hone
      have hmtwo : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      omega
    · intro i
      by_cases hij : i = j
      · subst i
        simp only [z, Function.update_self]
        exact floor_successor_error_lt_one hj
      · simpa only [z, Function.update_of_ne hij] using herr i
  · exact ⟨a, habs, not_forall.mp hdiv, herr⟩

theorem closed_box_rounding (m : ℕ) (hm : 2 ≤ m) (δ : Space 3)
    (hδ : ∀ i, |δ i| ≤ (m : ℝ)) (hnot : δ ∉ scaledGrid m) :
    ∃ z : Lattice 3,
      (∀ i, |z i| ≤ (m : ℤ)) ∧
      (∃ i, ¬ (m : ℤ) ∣ z i) ∧
      (∀ i, |δ i - (z i : ℝ)| < 1) := by
  apply closed_box_rounding_exists m hm δ hδ
  rintro ⟨z, hz⟩
  exact hnot (mem_scaledGrid.mpr ⟨z, hz.symm⟩)

theorem closed_box_rounding_norm (m : ℕ) (hm : 2 ≤ m) (δ : Space 3)
    (hδ : ∀ i, |δ i| ≤ (m : ℝ)) (hnot : δ ∉ scaledGrid m) :
    ∃ z : Lattice 3,
      (∀ i, |z i| ≤ (m : ℤ)) ∧
      (∃ i, ¬ (m : ℤ) ∣ z i) ∧
      ‖δ - castLattice z‖ < 1 := by
  obtain ⟨z, hz, hdiv, herr⟩ := closed_box_rounding m hm δ hδ hnot
  refine ⟨z, hz, hdiv, (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr ?_⟩
  intro i
  simpa only [Pi.sub_apply, castLattice_apply, Real.norm_eq_abs] using herr i

end PeriodicTilingThree

end

end OAI
