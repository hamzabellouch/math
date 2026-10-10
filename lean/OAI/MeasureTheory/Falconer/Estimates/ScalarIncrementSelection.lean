import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement
import Mathlib.Combinatorics.Pigeonhole

namespace OAI

/-! Selecting nearly equal scalar increments among finitely many copies.
 This is the scalar pigeonhole step in the nonporous sumset construction. -/
namespace Falconer

 theorem scalar_increment_selection {ι : Type*} {ε R : ℝ} (hε : 0 < ε)
    (I : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ I, |d i| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ I.card) :
    ∃ F ⊆ I, F.card = J ∧ ∃ a ∈ F, ∀ i ∈ F, |d i-d a| < ε := by
  classical
  let C := Finset.Icc (-(L:ℤ)) (L:ℤ)
  let c := fun i => ⌊d i/ε⌋
  have hC : C.card = 2*L+1 := by
    dsimp [C]
    rw [Int.card_Icc]
    omega
  have hCn : C.Nonempty := ⟨0,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  have hc : ∀ i ∈ I, c i ∈ C := by
    intro i hi
    have hiR := abs_le.mp (hd i hi)
    have hlu : -(L:ℝ) ≤ d i/ε := (le_div_iff₀ hε).2 (by nlinarith)
    have huu : d i/ε ≤ (L:ℝ) := (div_le_iff₀ hε).2 (by linarith)
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg,Int.cast_natCast] using hlu
    · have hh := (Int.floor_le (d i/ε)).trans huu
      exact_mod_cast hh
  have hsum : C.card • J ≤ ∑ _i ∈ I, (1:ℕ) := by
    simpa only [hC,nsmul_eq_mul,Finset.sum_const,smul_eq_mul,mul_one] using hsize
  obtain ⟨k,hk,hkJ⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hc hCn hsum
  have hj : J ≤ (I.filter fun i => c i = k).card := by simpa using hkJ
  obtain ⟨F,hF,hFc⟩ := Finset.exists_subset_card_eq hj
  have hFn : F.Nonempty := Finset.card_pos.mp (by rwa [hFc])
  obtain ⟨a,ha⟩ := hFn
  refine ⟨F,hF.trans (Finset.filter_subset _ _),hFc,a,ha,?_⟩
  intro i hi
  exact same_scalar_cell_dist_lt hε ((Finset.mem_filter.mp (hF hi)).2.trans
    (Finset.mem_filter.mp (hF ha)).2.symm)

end Falconer

end OAI
