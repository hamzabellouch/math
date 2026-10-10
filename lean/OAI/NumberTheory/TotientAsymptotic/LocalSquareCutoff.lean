import OAI.NumberTheory.TotientAsymptotic.LocalSquareCount
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace OAI

/-! A concrete logarithmic square cutoff for arbitrary selected preimages. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def localSquareCutoff (z : ℝ) : ℕ := ⌊(Real.log z)^6⌋₊

theorem linear_preimage_cutoff_bounds {C : ℝ} (hC : 0 < C) :
    ∀ᶠ z : ℝ in atTop,
      let N := ⌈C*z*(B z+2)⌉₊
      1 ≤ N ∧ (N:ℝ) ≤ 2*C*z*(B z+2) ∧ Real.log N ≤ 2*Real.log z ∧
      1 ≤ localSquareCutoff z ∧ (Real.log z)^6 ≤ 2*(localSquareCutoff z:ℝ) := by
  have hlog : Tendsto (fun z : ℝ => Real.log z/z) atTop (nhds 0) := by
    simpa only [pow_one,id_eq] using (Real.isLittleO_pow_log_id_atTop (n:=1)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun z : ℝ => 1/z) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hlim : Tendsto (fun z : ℝ => 2*C*(Real.log z+2)/z) atTop (nhds 0) := by
    convert (hlog.add (hinv.const_mul 2)).const_mul (2*C) using 1
    · funext z; ring
    · norm_num
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (1/C),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (0:ℝ)] with z hsmall hB hzC hlz hz0
  let N := ⌈C*z*(B z+2)⌉₊
  have hCz : 1 ≤ C*z := by
    have hh := mul_le_mul_of_nonneg_left hzC hC.le
    have he : C*(1/C)=1 := by field_simp
    rw [he] at hh
    exact hh
  have hM : 1 ≤ C*z*(B z+2) := by nlinarith only [hCz,hB]
  have hN1 : 1 ≤ N := by
    exact Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hM)
  have hN : (N:ℝ) ≤ 2*C*z*(B z+2) := by
    have hh := Nat.ceil_lt_add_one (zero_le_one.trans hM)
    change (N:ℝ) < C*z*(B z+2)+1 at hh
    nlinarith only [hh,hM]
  have hBLog : B z ≤ Real.log z := Real.log_le_self (by linarith only [hlz])
  have hline : 2*C*(B z+2) ≤ z := by
    have hh := (div_le_iff₀ hz0).mp hsmall.le
    have hh' := mul_le_mul_of_nonneg_left hBLog (show 0≤2*C by positivity)
    linarith only [hh,hh']
  have hNsquare : (N:ℝ) ≤ z^2 := by
    have hh := mul_le_mul_of_nonneg_right hline hz0.le
    nlinarith only [hN,hh]
  have hlogN : Real.log N ≤ 2*Real.log z := by
    have hh := Real.log_le_log (show (0:ℝ)<N by exact_mod_cast (show 0<N by omega)) hNsquare
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hL : 2 ≤ (Real.log z)^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hlz 6
    norm_num at hh
    linarith only [hh]
  have hfloor := Nat.sub_one_lt_floor ((Real.log z)^6)
  have hcut : (Real.log z)^6 ≤ 2*(localSquareCutoff z:ℝ) := by
    change (Real.log z)^6 ≤ 2*(⌊(Real.log z)^6⌋₊:ℝ)
    linarith only [hfloor,hL]
  have hcut1 : 1 ≤ localSquareCutoff z := by
    have hh : (1:ℝ) ≤ localSquareCutoff z := by linarith only [hL,hcut]
    exact_mod_cast hh
  exact ⟨hN1,hN,hlogN,hcut1,hcut⟩

theorem local_square_witness_count : ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,
    ∀ (S : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (S : Set ℕ) →
      (∀ n ∈ S,0 < F n ∧ ((F n).totient:ℝ) ≤ z) →
      (∀ n ∈ S,∃ p : ℕ,p.Prime ∧ localSquareCutoff z<p ∧
        (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) →
      (S.card:ℝ) ≤ C*z*(B z+2)/(Real.log z)^4 := by
  obtain ⟨C,hC,hpreimage⟩ := totient_preimage_linear_loglog
  refine ⟨224*C,by positivity,?_⟩
  filter_upwards [linear_preimage_cutoff_bounds hC,eventually_ge_atTop (Real.exp 2)]
    with z hbounds hz
  dsimp only at hbounds
  intro S F hinj hF hsq
  let N := ⌈C*z*(B z+2)⌉₊
  have hsize (n) (hn : n∈S) : 0<F n ∧ F n≤N := by
    have hh := hF n hn
    refine ⟨hh.1,?_⟩
    exact_mod_cast (hpreimage z hz (F n) hh.1 hh.2).trans (Nat.le_ceil _)
  have hh := square_witness_local_bound (C:=2*C) (by positivity) hz
    hbounds.1 hbounds.2.2.2.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.2 S F hinj hsize hsq
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
