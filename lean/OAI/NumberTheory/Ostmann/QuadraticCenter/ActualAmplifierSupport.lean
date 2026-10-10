import OAI.NumberTheory.Ostmann.Preliminaries.Sizes
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionAuxiliary
import OAI.NumberTheory.Ostmann.Supply.Fourier

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem actual_positiveIntegerWindow_mem {S : Set ℕ} {X : ℕ} {a : ℤ}
    (ha : a ∈ positiveIntegerWindow S X) :
    ∃ n : ℕ, n ∈ S ∧ n ≤ X ∧ (X : ℝ) ^ (9 / 10 : ℝ) ≤ n ∧ (n : ℤ) = a := by
  obtain ⟨n, hn, hn'⟩ := Finset.mem_map.mp ha
  obtain ⟨hS, hX, hlarge⟩ := mem_upperWindow.mp hn
  exact ⟨n, hS, hX, hlarge, hn'⟩

theorem actual_positiveIntegerWindow_abs_le {S : Set ℕ} {X : ℕ} (hX : 0 < X)
    {a : ℤ} (ha : a ∈ positiveIntegerWindow S X) : |(a : ℝ) / X| ≤ 1 := by
  obtain ⟨n, hn, hnX, hlarge, rfl⟩ := actual_positiveIntegerWindow_mem ha
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hnXr : (n : ℝ) ≤ X := by exact_mod_cast hnX
  simp only [Int.cast_natCast, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) hXr.le)]
  exact (div_le_one hXr).mpr hnXr

theorem actual_crt_intCast {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (a : ℤ) (i : ι) :
    ZMod.prodEquivPi p hcop (a : ZMod (∏ j, p j)) i = (a : ZMod (p i)) := by
  simp only [map_intCast, Pi.intCast_apply]

theorem eventually_actual_positiveIntegerWindow_residues (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, ∀ hp : NeZero p,
      (p : ℝ) ≤ Real.sqrt X → ∀ a ∈ positiveIntegerWindow d.A X,
        letI : NeZero p := hp
        (a : ZMod p) ∈ d.residueSupport p := by
  filter_upwards [eventually_upperWindow_large d.cutoff] with X hlarge
  intro p hp hpX a ha
  let : NeZero p := hp
  obtain ⟨n, hn, hnX, hnlarge, rfl⟩ := actual_positiveIntegerWindow_mem ha
  have hpn : p + d.cutoff < n := by
    have hr : (p : ℝ) + d.cutoff < n := by linarith
    exact_mod_cast hr
  exact (d.mem_residueSupport p _).mpr ⟨n, hn, hpn, by simp⟩

theorem eventually_actual_amplifier_support (d : Decomposition)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) :
    ∀ᶠ X : ℕ in atTop, (∀ i, (p i : ℝ) ≤ Real.sqrt X) →
      (∀ a ∈ positiveIntegerWindow d.A X, |(a : ℝ) / X| ≤ 1) ∧
      (∀ a ∈ positiveIntegerWindow d.A X, ∀ i,
        ZMod.prodEquivPi p hcop (a : ZMod (∏ j, p j)) i ∈ d.residueSupport (p i)) := by
  filter_upwards [eventually_actual_positiveIntegerWindow_residues d,
    eventually_ge_atTop (1 : ℕ)] with X hres hX
  intro hp
  refine ⟨fun a ha => actual_positiveIntegerWindow_abs_le (by omega) ha, ?_⟩
  intro a ha i
  rw [actual_crt_intCast]
  exact hres (p i) inferInstance (hp i) a ha

theorem eventually_actual_amplifier_support_uniform (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop,
      (∀ a ∈ positiveIntegerWindow d.A X, |(a : ℝ) / X| ≤ 1) ∧
      ∀ (ι : Type*) [Fintype ι] (p : ι → ℕ)
        (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
        (hne : ∀ i, NeZero (p i)),
        (∀ i, (p i : ℝ) ≤ Real.sqrt X) →
        letI : ∀ i, NeZero (p i) := hne
        ∀ a ∈ positiveIntegerWindow d.A X, ∀ i,
          ZMod.prodEquivPi p hcop (a : ZMod (∏ j, p j)) i ∈ d.residueSupport (p i) := by
  filter_upwards [eventually_actual_positiveIntegerWindow_residues d,
    eventually_ge_atTop (1 : ℕ)] with X hres hX
  refine ⟨fun a ha => actual_positiveIntegerWindow_abs_le (by omega) ha, ?_⟩
  intro ι _ p hcop hne hp
  let : ∀ i, NeZero (p i) := hne
  intro a ha i
  rw [actual_crt_intCast]
  exact hres (p i) (hne i) (hp i) a ha

theorem actual_residue_density_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    Supply.density (d.residueSupport p) = d.residueDensity p := by
  simp only [Supply.density, ZMod.card, Decomposition.residueDensity]

theorem actual_balanced_density (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : BalancedResiduePrime d p) :
    1 / 3 ≤ Supply.density (d.residueSupport p) ∧
      Supply.density (d.residueSupport p) ≤ 2 / 3 := by
  rw [actual_residue_density_eq]
  obtain ⟨hprime, hbalance⟩ := hp
  exact hbalance

theorem actual_positiveIntegerWindow_card_lower (d : Decomposition) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ (positiveIntegerWindow d.A X).card ∧
      0 < (positiveIntegerWindow d.A X).card := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := summand_sqrt_bounds d
  have hcard := eventually_upperWindow_card_lower d.A hc hC
    (hbounds.mono fun X h => h.1) (hbounds.mono fun X h => h.2.2.1)
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hcard, eventually_ge_atTop (2 : ℕ)] with X hcard hX
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpos : (0 : ℝ) < (upperWindow d.A X).card :=
    (div_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr hXr)) (pow_pos hlog 3)).trans_le hcard
  simp only [positiveIntegerWindow, Finset.card_map]
  exact ⟨hcard, by exact_mod_cast hpos⟩

end Ostmann.QuadraticCenter

end

end OAI
