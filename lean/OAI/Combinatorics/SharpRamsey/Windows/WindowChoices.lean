import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.WindowPacking
import OAI.Combinatorics.SharpRamsey.Parameters.BookScales

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Real Filter SourceScales
open scoped Topology
noncomputable section

lemma rounded_window {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hyx : y ≤ x) :
    2 ≤ ⌈x⌉₊ ∧ 0 < ⌊y⌋₊ ∧ ⌊y⌋₊ ≤ ⌈x⌉₊ ∧
    y/2 ≤ (⌊y⌋₊:ℝ) ∧
    x ≤ (4*(⌈x⌉₊+⌊y⌋₊):ℕ) ∧ (4*(⌈x⌉₊+⌊y⌋₊):ℕ) ≤ 12*x := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hn := Nat.le_ceil x
  have hn' := Nat.ceil_lt_add_one hx0
  have hk := Nat.floor_le hy0
  have hk' := Nat.lt_floor_add_one y
  have hn2 : 2 ≤ ⌈x⌉₊ := by exact_mod_cast (show (2:ℝ) ≤ ⌈x⌉₊ by linarith)
  have hkpos : 0 < ⌊y⌋₊ := by exact_mod_cast (show (0:ℝ) < ⌊y⌋₊ by linarith)
  have hkn : ⌊y⌋₊ ≤ ⌈x⌉₊ := by exact_mod_cast (show (⌊y⌋₊:ℝ) ≤ ⌈x⌉₊ by linarith)
  refine ⟨hn2,hkpos,hkn,by linarith,?_,?_⟩ <;> push_cast <;> linarith

theorem eventually_reciprocal_windows (η c C : ℝ) (hη : 0 < η) (hηu : η ≤ 1)
    (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q D : ℝ) (m : ℕ) (integer : Bool),
      exp σ = q → σ^beta η ≤ D → D ≤ σ^(1-η/2) →
      c*q*σ^(1+η) ≤ (m:ℝ) → (m:ℝ) ≤ C*q*σ^(1+η) →
      let x := if integer then q*σ^(1+η/2) else q*D*σ^(η/2)
      let n := ⌈x⌉₊
      let k := ⌊q*D*σ^(3000*beta η)⌋₊
      let L := 4*(n+k)
      let w := m/L
      2 ≤ n ∧ 0 < k ∧ k ≤ n ∧ 1 ≤ w ∧ w*L ≤ m ∧ (m:ℝ)/2 ≤ (w*L:ℕ) ∧
      (1/2)*q*D*σ^(3000*beta η) ≤ (k:ℝ) ∧
      (w:ℝ)*D ≤ max C 12*σ^(1+η/2) ∧
      (w:ℝ) ≤ max C 12*σ^(1+η/2) ∧
      (if integer then q*σ^(1+η/2) ≤ (n:ℝ)
       else (c/(2*max C 12))*σ^(1+η/2) ≤ (w:ℝ)*D) ∧
      (L:ℝ) ≤ 12*q*σ^(1+η/2) := by
  have ht : Tendsto (fun σ : ℝ => σ^(η/2)) atTop atTop := tendsto_rpow_atTop (by positivity)
  filter_upwards [ht.eventually_ge_atTop (24/c), eventually_ge_atTop (1:ℝ)]
    with σ hlarge hσ q D m integer he hDl hDu hmlo hmhi
  have hσ0 : 0 < σ := lt_of_lt_of_le hη (hηu.trans hσ)
  have hb := beta_pos hη
  have hD : 1 ≤ D := (one_le_rpow hσ hb.le).trans hDl
  have hD0 : 0 < D := by linarith
  have hq0 : 0 < q := he ▸ exp_pos _
  have hq2 : 2 ≤ q := by
    have h := add_one_le_exp σ
    rw [he] at h
    linarith
  have h3000 : 0 ≤ 3000*beta η := by positivity
  have hpow3 : 1 ≤ σ^(3000*beta η) := one_le_rpow hσ h3000
  let x := if integer then q*σ^(1+η/2) else q*D*σ^(η/2)
  let y := q*D*σ^(3000*beta η)
  have hqD : 2 ≤ q*D := hq2.trans (le_mul_of_one_le_right hq0.le hD)
  have hy : 2 ≤ y := hqD.trans (le_mul_of_one_le_right (by positivity) hpow3)
  have hx : 2 ≤ x := by
    have ha := one_le_rpow hσ (show 0 ≤ η/2 by positivity)
    have hb := one_le_rpow hσ (show 0 ≤ 1+η/2 by positivity)
    cases integer
    · exact hqD.trans (le_mul_of_one_le_right (by positivity) ha)
    · exact hq2.trans (le_mul_of_one_le_right hq0.le hb)
  have hyx : y ≤ x := by
    have h3 : σ^(3000*beta η) ≤ σ^(η/2) := rpow_le_rpow_of_exponent_le hσ (by unfold beta; linarith)
    have h4 : σ^((1-η/2)+3000*beta η) ≤ σ^(1+η/2) :=
      rpow_le_rpow_of_exponent_le hσ (by unfold beta; linarith)
    cases integer
    · exact mul_le_mul_of_nonneg_left h3 (by positivity)
    · calc
        y ≤ q*(σ^(1-η/2))*σ^(3000*beta η) := by dsimp only [y]; gcongr
        _ = q*σ^((1-η/2)+3000*beta η) := by rw [mul_assoc, ←rpow_add hσ0]
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 hq0.le
  obtain ⟨hn,hk,hkn,hklo,hLlo,hLhi⟩ := rounded_window hx hy hyx
  let L := 4*(⌈x⌉₊+⌊y⌋₊)
  have hL : 0 < L := by dsimp only [L]; omega
  have hxup : x ≤ q*σ^(1+η/2) := by
    cases integer
    · change q*D*σ^(η/2) ≤ _
      calc
        _ ≤ q*σ^(1-η/2)*σ^(η/2) := by gcongr
        _ = q*σ := by rw [mul_assoc, ←rpow_add hσ0]; congr 1; convert rpow_one σ using 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          calc
            σ = σ^(1:ℝ) := (rpow_one _).symm
            _ ≤ _ := rpow_le_rpow_of_exponent_le hσ (by linarith)) hq0.le
    · exact le_rfl
  have hLup : (L:ℝ) ≤ 12*q*σ^(1+η/2) := by dsimp only [L]; nlinarith
  have hscale : 24*q*σ^(1+η/2) ≤ c*q*σ^(1+η) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hq0.le (rpow_nonneg hσ0.le (1+η/2)))
    have hp : σ^(η/2)*σ^(1+η/2) = σ^(1+η) := by rw [←rpow_add hσ0]; congr 1; ring
    nlinarith [show c*q*(σ^(η/2)*σ^(1+η/2))=c*q*σ^(1+η) by rw [hp]]
  have hpack : 2*L ≤ m := by exact_mod_cast (show (2:ℝ)*L ≤ m by linarith)
  obtain ⟨hw,hwm,hh⟩ := packing_bounds m L hL hpack
  have hbase : q*D*σ^(η/2) ≤ (L:ℝ) := by
    have hb : q*D*σ^(η/2) ≤ x := by
      cases integer
      · rfl
      · change q*D*σ^(η/2) ≤ q*σ^(1+η/2)
        calc
          _ ≤ q*σ^(1-η/2)*σ^(η/2) := by gcongr
          _ ≤ _ := by
            rw [mul_assoc, ←rpow_add hσ0]
            exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hσ (by linarith)) hq0.le
    exact hb.trans hLlo
  have hwd : ((m/L:ℕ):ℝ)*D ≤ max C 12*σ^(1+η/2) := by
    have hu : ((m/L:ℕ):ℝ)*(q*D*σ^(η/2)) ≤ C*q*σ^(1+η) :=
      (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)).trans
        ((by exact_mod_cast hwm : ((m/L:ℕ):ℝ)*(L:ℝ) ≤ m).trans hmhi)
    have hp : σ^(1+η)=σ^(1+η/2)*σ^(η/2) := by rw [←rpow_add hσ0]; congr 1; ring
    rw [hp] at hu
    have hwa : ((m/L:ℕ):ℝ)*D ≤ C*σ^(1+η/2) := by
      apply (mul_le_mul_iff_right₀ (mul_pos hq0 (rpow_pos_of_pos hσ0 (η/2)))).mp
      nlinarith only [hu]
    exact hwa.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg hσ0.le _))
  dsimp only
  change _ ∧ _ ∧ _ ∧ 1 ≤ m/L ∧ (m/L)*L ≤ m ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hn,hk,hkn,hw,hwm,hh,by dsimp only [y] at hklo; linarith,hwd,?_,?_,hLup⟩
  · have hw0 : (0:ℝ) ≤ (m/L:ℕ) := Nat.cast_nonneg _
    nlinarith
  · cases integer
    · simp only [Bool.false_eq_true,ite_false]
      have hA : 0 < max C 12 := lt_of_lt_of_le hC (le_max_left _ _)
      have hmA : (m:ℝ) ≤ max C 12*q*σ^(1+η) := hmhi.trans (by gcongr; exact le_max_left _ _)
      have hLA : (L:ℝ) ≤ max C 12*q*D*σ^(η/2) := by
        have hh : (L:ℝ) ≤ 12*(q*D*σ^(η/2)) := hLhi
        calc
          _ ≤ _ := hh
          _ ≤ _ := by
            have hp := mul_le_mul_of_nonneg_right (le_max_right C 12)
              (by positivity : 0 ≤ q*D*σ^(η/2))
            nlinarith only [hp]
      exact (packing_scales m L hq0 hσ0 hD0 hc hA hL hpack hmlo hmA hbase hLA).2.2.2.1
    · simpa only [ite_true] using Nat.le_ceil (q*σ^(1+η/2))
end
end SharpLogRamsey.Selection.Windows

end

end OAI
