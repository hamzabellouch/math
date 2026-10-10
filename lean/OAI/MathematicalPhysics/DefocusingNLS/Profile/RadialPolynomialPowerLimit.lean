import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialNeighborhood

namespace OAI

/-! Fixed coefficients of the odd power vanish for subunit polynomial limits. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem radialPolynomial_coefficients_eventually_bounded
    (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (nhds (Q.coeff k))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ k, k ≤ d → ‖(P n).coeff k‖ ≤ B := by
  let B : ℝ := 1+∑ k ∈ Finset.range (d+1), ‖Q.coeff k‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  have he : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (d+1),
      ‖(P n).coeff k‖ < ‖Q.coeff k‖+1 := by
    apply (eventually_all_finset _).mpr
    intro k hk
    exact (hP k (by have := Finset.mem_range.mp hk; omega)).norm.eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [he] with n hn k hk
  have hmem : k ∈ Finset.range (d+1) := Finset.mem_range.mpr (by omega)
  have hsum : ‖Q.coeff k‖ ≤ ∑ i ∈ Finset.range (d+1), ‖Q.coeff i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg _) hmem
  dsimp [B]
  linarith [hn k hmem]

theorem radialPolynomialPower_coefficient_limit (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d k : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ j, j ≤ d → Tendsto (fun n => (P n).coeff j) atTop (nhds (Q.coeff j)))
    (hzero : ‖Q.coeff 0‖ < 1) :
    Tendsto (fun n => (radialPolynomialPower n (P n)).coeff k) atTop (nhds 0) := by
  obtain ⟨B,hB,hbound⟩ := radialPolynomial_coefficients_eventually_bounded P Q d hP
  let ρ₀ : ℝ := (‖Q.coeff 0‖+1)/2
  let ρ₁ : ℝ := (ρ₀+1)/2
  have h01 : ρ₀ < ρ₁ := by dsimp [ρ₀,ρ₁]; linarith
  have h1 : ρ₁ < 1 := by dsimp [ρ₀,ρ₁]; linarith
  have hpos : 0 ≤ ρ₁ := by dsimp [ρ₀,ρ₁]; positivity
  have h0 : ‖Q.coeff 0‖ < ρ₀ := by dsimp [ρ₀]; linarith
  have he0 : ∀ᶠ n in atTop, ‖(P n).coeff 0‖ ≤ ρ₀ :=
    ((hP 0 (Nat.zero_le _)).norm.eventually (gt_mem_nhds h0)).mono (fun _ h => h.le)
  obtain ⟨ε,hε,_,hcircle⟩ := exists_radialPolynomial_subunit_circle d B ρ₀ ρ₁ hB h01
  apply radialPolynomialPower_coefficient_tendsto P k ε ρ₁ hε hpos h1
  filter_upwards [hdeg,hbound,he0] with n hn hb hz z he
  exact hcircle (P n) hn hz hb z he.le

end DefocusingNLS

end OAI
