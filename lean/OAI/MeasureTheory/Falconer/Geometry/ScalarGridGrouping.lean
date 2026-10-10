import OAI.MeasureTheory.Falconer.Geometry.ScalarGridFibers
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! A dyadic grid scale with controlled maximal occupancy. This selects
 the local groups used to treat arbitrary branching at a porous level. -/
namespace Falconer

 theorem scalar_grid_grouping_of_small_cells {h z : ℝ} (hh : 0 < h)
    (E : Finset ℝ) (hE : ∀ x ∈ E, 0 ≤ x-z ∧ x-z ≤ 2)
    (M : ℕ) (hcard : 2*M ≤ E.card)
    (hsmall : ∀ k : ℤ, (scalarGridFiber h z E k).card < 2*M) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ,
      2*M ≤ (scalarGridFiber ((2:ℝ)^n*h) z E k).card ∧
      ∀ j : ℤ, (scalarGridFiber ((2:ℝ)^n*h) z E j).card ≤ 4*M := by
  classical
  let P := fun n : ℕ => ∃ k : ℤ, 2*M ≤ (scalarGridFiber ((2:ℝ)^n*h) z E k).card
  have hex : ∃ n, P n := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 2 by norm_num)).eventually
      (Filter.eventually_gt_atTop (2/h))
    obtain ⟨n,hn⟩ := ht.exists
    have hw : 2 < (2:ℝ)^n*h := (div_lt_iff₀ hh).1 hn
    refine ⟨n,0,?_⟩
    rw [scalarGridFiber_wide hw E hE]
    exact hcard
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra hn0
    have hnz : n = 0 := by omega
    obtain ⟨k,hk⟩ := hn
    rw [hnz,pow_zero,one_mul] at hk
    exact (not_lt_of_ge hk) (hsmall k)
  obtain ⟨k,hk⟩ := hn
  refine ⟨n,hn0,k,hk,?_⟩
  intro j
  have hprev : ¬ P (n-1) := Nat.find_min hex (by dsimp [n]; omega)
  have hsmall (q : ℤ) : (scalarGridFiber ((2:ℝ)^(n-1)*h) z E q).card < 2*M := by
    by_contra hq
    exact hprev ⟨q,le_of_not_gt hq⟩
  have he : (2:ℝ)^n*h = 2*((2:ℝ)^(n-1)*h) := by
    have hn_eq : n = (n-1)+1 := by omega
    conv_lhs => rw [hn_eq,pow_succ]
    ring
  rw [he]
  have hd := scalarGridFiber_double_card ((2:ℝ)^(n-1)*h) z E j
  have h1 := hsmall (2*j)
  have h2 := hsmall (2*j+1)
  omega

 theorem scalar_grid_grouping {h μ z : ℝ} (hh : 0 < h) (hhμ : h ≤ μ)
    (E : Finset ℝ) (hE : ∀ x ∈ E, 0 ≤ x-z ∧ x-z ≤ 2)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → μ ≤ |x-y|)
    (M : ℕ) (hM : 0 < M) (hcard : 2*M ≤ E.card) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ,
      2*M ≤ (scalarGridFiber ((2:ℝ)^n*h) z E k).card ∧
      ∀ j : ℤ, (scalarGridFiber ((2:ℝ)^n*h) z E j).card ≤ 4*M := by
  apply scalar_grid_grouping_of_small_cells hh E hE M hcard
  intro k
  have hs := scalarGridFiber_small (z := z) hh hhμ E hsep k
  omega

end Falconer

end OAI
