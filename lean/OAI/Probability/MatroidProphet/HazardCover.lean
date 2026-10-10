import OAI.Probability.MatroidProphet.ExitNumerics
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Find

namespace OAI

namespace MatroidProphet
open Finset

noncomputable def inHazardBand (p : ℝ) (l : ℕ) : Prop :=
  ((2 : ℝ) ^ (l+1))⁻¹ ≤ p ∧ p < ((2 : ℝ) ^ l)⁻¹

lemma exists_hazard_band {p : ℝ} (hp : 0 < p) (hsmall : p < ((2 : ℝ)^12)⁻¹) :
    ∃ l : ℕ, 12 ≤ l ∧ inHazardBand p l := by
  have hex : ∃ n : ℕ, ((1/2 : ℝ)^n) ≤ p := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  let n := Nat.find hex
  have hn : (1/2 : ℝ)^n ≤ p := Nat.find_spec hex
  have hn12 : 12 < n := by
    by_contra h
    have hle : n ≤ 12 := by omega
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) hle
    have hsmall' : p < (1/2 : ℝ)^12 := by simpa [one_div, inv_pow] using hsmall
    linarith
  refine ⟨n-1, by omega, ?_⟩
  have hpred : p < (1/2 : ℝ)^(n-1) :=
    lt_of_not_ge (Nat.find_min hex (by dsimp only [n]; omega))
  unfold inHazardBand
  have hsucc : n-1+1 = n := by omega
  rw [hsucc]
  simpa only [one_div, inv_pow] using And.intro hn hpred

theorem finite_hazard_cover {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    ∃ length : ℕ, ∀ i, 0 < p i → p i < ((2 : ℝ)^12)⁻¹ →
      ∃ k ∈ range length, inHazardBand (p i) (12+k) := by
  classical
  let band : ι → ℕ := fun i => if h : 0 < p i ∧ p i < ((2 : ℝ)^12)⁻¹
    then (exists_hazard_band h.1 h.2).choose else 12
  let length := (univ : Finset ι).sup band + 1
  refine ⟨length, ?_⟩
  intro i hi hs
  have hband : 12 ≤ band i ∧ inHazardBand (p i) (band i) := by
    dsimp only [band]
    rw [dite_eq_left ⟨hi, hs⟩]
    exact (exists_hazard_band hi hs).choose_spec
  refine ⟨band i-12, mem_range.mpr ?_, ?_⟩
  · have hb := le_sup (f := band) (mem_univ i)
    dsimp only [length]
    omega
  · have heq : 12 + (band i-12) = band i := by omega
    rw [heq]
    exact hband.2

lemma hazard_band_disjoint {p : ℝ} {l k : ℕ}
    (hl : inHazardBand p l) (hk : inHazardBand p k) : l = k := by
  have impossible {a b : ℕ} (hab : a < b)
      (ha : inHazardBand p a) (hb : inHazardBand p b) : False := by
    have hpow : ((2 : ℝ)^b)⁻¹ ≤ ((2 : ℝ)^(a+1))⁻¹ := by
      rw [← inv_pow, ← inv_pow]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact (not_lt_of_ge (hpow.trans ha.1)) hb.2
  exact le_antisymm (le_of_not_gt (fun h => impossible h hk hl))
    (le_of_not_gt (fun h => impossible h hl hk))

end MatroidProphet

end OAI
