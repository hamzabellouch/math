import OAI.NumberTheory.TotientAsymptotic.TotientCountingEnvelope
import OAI.NumberTheory.TotientAsymptotic.PrimeNumberTheorem

namespace OAI

/-! Coarse unconditional bounds used before the sharp counting-scale bootstrap. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma V_nonneg (x : ℝ) : 0 ≤ V x := Nat.cast_nonneg _

lemma V_le_self {x : ℝ} (hx : 0 ≤ x) : V x ≤ x := by
  classical
  have hc : (totientValues x).card ≤ ⌊x⌋₊ := by
    have hh := Finset.card_le_card (Finset.filter_subset IsTotient (Finset.Icc 1 ⌊x⌋₊))
    simpa [totientValues] using hh
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hx)

lemma prime_counting_le_V (x : ℝ) : (Nat.primeCounting ⌊x⌋₊:ℝ) ≤ V x := by
  classical
  let P := Nat.primesLE ⌊x⌋₊
  have hi : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have hp2 := (Nat.mem_primesLE.mp hp).2.two_le
    have hq2 := (Nat.mem_primesLE.mp hq).2.two_le
    dsimp only at he
    omega
  have hs : P.image (fun p => p-1) ⊆ totientValues x := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hpx,hp⟩ := Nat.mem_primesLE.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by have := hp.two_le; omega,by omega⟩,?_⟩
    exact ⟨p,hp.pos,Nat.totient_prime hp⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn hi] at hc
  have he : P.card=Nat.primeCounting ⌊x⌋₊ := Nat.primesLE_card_eq_primeCounting _
  rw [he] at hc
  change (Nat.primeCounting ⌊x⌋₊:ℝ) ≤ ((totientValues x).card:ℝ)
  exact_mod_cast hc

theorem V_coarse_lower : ∀ᶠ x : ℝ in atTop, x/(2*Real.log x) ≤ V x := by
  filter_upwards [primeNumberTheoremInput (1/2) (by norm_num)] with x hx
  have hh := (abs_le.mp hx).1
  have hp := prime_counting_le_V x
  have he : x/(2*Real.log x)=(x/Real.log x)/2 := by ring
  rw [he]
  linarith

end TotientAsymptotic

end

end OAI
