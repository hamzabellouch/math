import OAI.NumberTheory.Jacobsthal.Primes.ProgressionPrimeUpper

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.RealProgressionCoordinates

open AffinePrimeSieve

theorem exists_coordinates (x H : ℝ) (q : ℕ) (r : ℤ) (hq : 0 < q) (hH : 0 ≤ H) :
    ∃ (N : ℕ) (a : ℤ) (index : ℤ → ℕ),
      |(N:ℝ)-H/q| ≤ 1 ∧
      ∀ z : ℤ, x < (z:ℝ) → (z:ℝ) ≤ x+H → Int.ModEq (q:ℤ) z r →
        index z < N ∧ value a q (index z) = z := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  let low : ℝ := (x-r)/q
  let high : ℝ := (x+H-r)/q
  let L : ℤ := ⌊low⌋
  let U : ℤ := ⌊high⌋
  have hLH : low ≤ high := div_le_div_of_nonneg_right (by linarith) hqR.le
  have hLU : L ≤ U := Int.floor_mono hLH
  let N : ℕ := (U-L).toNat
  let a : ℤ := r+(q:ℤ)*(L+1)
  let index : ℤ → ℕ := fun z => ((z-r)/(q:ℤ)-(L+1)).toNat
  have hN : (N:ℤ)=U-L := Int.toNat_of_nonneg (sub_nonneg.mpr hLU)
  have hNR : (N:ℝ)=(U:ℝ)-(L:ℝ) := by
    have hh := congrArg (fun t : ℤ => (t:ℝ)) hN
    push_cast at hh
    exact hh
  have hlength : high-low=H/q := by dsimp [high,low]; ring
  have hcount : |(N:ℝ)-H/q| ≤ 1 := by
    have hL := Int.floor_le low
    have hL' := Int.lt_floor_add_one low
    have hU := Int.floor_le high
    have hU' := Int.lt_floor_add_one high
    change (L:ℝ) ≤ low at hL
    change low < (L:ℝ)+1 at hL'
    change (U:ℝ) ≤ high at hU
    change high < (U:ℝ)+1 at hU'
    rw [hNR,← hlength,abs_le]
    constructor <;> linarith
  refine ⟨N,a,index,hcount,?_⟩
  intro z hzlo hzhi hzmod
  let k : ℤ := (z-r)/(q:ℤ)
  have hdiv : (q:ℤ) ∣ z-r := Int.modEq_iff_dvd.mp hzmod.symm
  have hk : z=r+(q:ℤ)*k := by
    have hh := Int.ediv_mul_cancel hdiv
    change k*(q:ℤ)=z-r at hh
    nlinarith
  have hkR : (z:ℝ)=(r:ℝ)+(q:ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hlow : low < (k:ℝ) := by
    apply (div_lt_iff₀ hqR).mpr
    linarith
  have hhigh : (k:ℝ) ≤ high := by
    apply (le_div_iff₀ hqR).mpr
    linarith
  have hLk : L < k := Int.floor_lt.mpr hlow
  have hkU : k ≤ U := Int.le_floor.mpr hhigh
  have hnonneg : 0 ≤ k-(L+1) := by omega
  have hi : (index z : ℤ)=k-(L+1) := Int.toNat_of_nonneg hnonneg
  constructor
  · have hh : (index z : ℤ) < (N:ℤ) := by rw [hi,hN]; omega
    exact_mod_cast hh
  · calc
      value a q (index z) = r+(q:ℤ)*k := by
        dsimp [value,a]
        rw [hi]
        ring
      _ = z := hk.symm

end ErdosPrimeInputs.RealProgressionCoordinates

end

end Erdos970

end OAI
