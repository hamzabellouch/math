import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma high_integer_ranges {σ q D η c : ℝ} (hη : 0<η) (hσ : 1≤σ) (hq : 2≤q)
    (hc : 0<c) (hD : σ^beta η≤D)
    (hscale : D*σ^(3000*beta η)≤c*σ/4) (n : ℕ)
    (hlen : c*q*σ^(1+η)≤n) :
    let T:=⌊q*D*σ^(3000*beta η)⌋₊
    let rem:=n-T
    let h:=⌈q*σ^beta η⌉₊
    0<n ∧ 0<T ∧ 0<rem ∧ n≤2*rem ∧ rem+T≤n ∧
      q*D*σ^(3000*beta η)/2≤T ∧ q*σ^(1+η/2)/(2/c)≤rem ∧
      q*σ^beta η≤h ∧ (h:ℝ)≤2*q*σ^beta η := by
  dsimp only
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqpos : 0<q := by linarith
  have hb:=beta_pos hη
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hp : 1≤σ^(3000*beta η) := Real.one_le_rpow hσ (by positivity)
  let x:=q*D*σ^(3000*beta η)
  have hx : 2≤x := by
    calc
      2 ≤ q := hq
      _ = q*1*1 := by ring
      _ ≤ _ := by dsimp [x];gcongr
  have hσhi : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hT : (⌊x⌋₊:ℝ)≤x := Nat.floor_le (by linarith)
  have hTx := Nat.lt_floor_add_one x
  have hThalf : x/2≤(⌊x⌋₊:ℝ) := by linarith
  have hxn : x≤(n:ℝ)/4 := by
    calc
      _ = q*(D*σ^(3000*beta η)) := by dsimp [x];ring
      _ ≤ q*(c*σ/4) := mul_le_mul_of_nonneg_left hscale hqpos.le
      _ ≤ q*(c*σ^(1+η)/4) := by gcongr
      _ ≤ _ := by nlinarith [hlen]
  have hTn : 2*⌊x⌋₊≤n := by
    have hh : (2:ℝ)*⌊x⌋₊≤n := by linarith
    exact_mod_cast hh
  have hn0 : 0<n := by
    have : 0<(n:ℝ) := (by positivity : 0<c*q*σ^(1+η)).trans_le hlen
    exact_mod_cast this
  have hTpos : 0<⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hTle : ⌊x⌋₊≤n := by omega
  have hrem : (n:ℝ)/2≤((n-⌊x⌋₊:ℕ):ℝ) := by
    rw [Nat.cast_sub hTle]
    have hh : (2:ℝ)*⌊x⌋₊≤n := by exact_mod_cast hTn
    linarith
  have hlrem : q*σ^(1+η/2)/(2/c)≤((n-⌊x⌋₊:ℕ):ℝ) := by
    apply le_trans _ hrem
    have hpow : σ^(1+η/2)≤σ^(1+η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    calc
      _ = c*q*σ^(1+η/2)/2 := by field_simp
      _ ≤ c*q*σ^(1+η)/2 := by gcongr
      _ ≤ _ := by linarith
  have hsm : 1≤q*σ^beta η := by
    have := Real.one_le_rpow hσ hb.le
    nlinarith
  have hceil := Nat.le_ceil (q*σ^beta η)
  have hceilhi := Nat.ceil_lt_add_one (by linarith : 0≤q*σ^beta η)
  dsimp only [x] at hTn hTpos hTle hThalf hlrem
  exact ⟨hn0,hTpos,by omega,by omega,by omega,hThalf,hlrem,hceil,by linarith⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
