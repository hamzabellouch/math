import OAI.NumberTheory.Jacobsthal.Primes.PrimeBinRationalList

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open ErdosInversePrimeBin

noncomputable def edgeFrequencyCap (U : ℝ) : ℕ := ⌈2*U⌉₊

theorem edgeFrequencyCap_le (U : ℝ) (hU : 1 ≤ U) : (edgeFrequencyCap U : ℝ) ≤ 3*U := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 2*U by linarith)
  change (⌈2*U⌉₊ : ℝ) ≤ 3*U
  linarith

theorem edge_prime_le_cap (U theta : ℝ) (hU : 0 ≤ U) (htheta : 0 ≤ theta)
    (htheta1 : theta ≤ 1) (u : ℕ) (hu : u ∈ primeBin U theta) : u ≤ edgeFrequencyCap U := by
  have htop := ((mem_primeBin hU htheta u).mp hu).2.2
  have huR : (u : ℝ) ≤ 2*U := htop.trans (by nlinarith)
  exact_mod_cast huR.trans (Nat.le_ceil (2*U))

theorem uniform_edge_bin_count (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ U theta : ℝ,w ≤ U → xi/4 ≤ theta → theta ≤ xi →
      xi*U/(16*Real.log U) ≤ ((primeBin U theta).card : ℝ) ∧ 0 < (primeBin U theta).card := by
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp (uniform_prime_bin_count (by positivity : 0 < xi/4))
  filter_upwards [eventually_ge_atTop (max 2 U0)] with w hw
  have hw2 : 2 ≤ w := (le_max_left _ _).trans hw
  refine ⟨hw2,?_⟩
  intro U theta hwU htlow hthigh
  have hU2 : 2 ≤ U := hw2.trans hwU
  have hUpos : 0 < U := by linarith
  have hlog : 0 < Real.log U := Real.log_pos (by linarith)
  have hc := ((hU0 U (((le_max_right _ _).trans hw).trans hwU)).2 theta htlow (hthigh.trans hxi1)).1
  have hlow : xi*U/(16*Real.log U) ≤ ((primeBin U theta).card : ℝ) := by
    calc
      _ = (xi/4)*U/(4*Real.log U) := by ring
      _ ≤ theta*U/(4*Real.log U) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htlow hUpos.le) (by positivity)
      _ ≤ _ := hc
  refine ⟨hlow,?_⟩
  have hh : (0 : ℝ) < (primeBin U theta).card := (by positivity : 0 < xi*U/(16*Real.log U)).trans_le hlow
  exact_mod_cast hh

end ErdosInverseSaving

end

end Erdos970

end OAI
