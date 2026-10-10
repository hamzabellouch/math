import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OrdinarySum

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryTriangular

theorem partial_small_of_triangle_small (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤1)
    (hsmall : ∀ε : ℝ, 0<ε → ∃M : ℝ, ∀N : ℕ, M≤(N:ℝ) → ‖triangle a N‖≤ε*(N:ℝ)^2)
    (ε : ℝ) (hε : 0<ε) :
    ∃M : ℝ, ∀N : ℕ, M≤(N:ℝ) → ‖ordinarySum a N‖≤ε*(N:ℝ) := by
  let ρ : ℝ := min (ε/4) (1/2)
  have hρ : 0<ρ := lt_min (by positivity) (by norm_num)
  have hρε : ρ≤ε/4 := min_le_left _ _
  have hρ1 : ρ≤1/2 := min_le_right _ _
  let e : ℝ := ε*ρ/10
  have he : 0<e := by dsimp [e]; positivity
  obtain ⟨M₀,hsmall₀⟩ := hsmall e he
  let M : ℝ := max 1 (max M₀ (1/ρ))
  refine ⟨M,?_⟩
  intro N hMN
  have hN1 : 1≤(N:ℝ) := le_trans (le_max_left _ _) hMN
  have hN : 0<(N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hNM : M₀≤(N:ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMN
  have hNρ : 1/ρ≤(N:ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMN
  have hρN : 1≤ρ*(N:ℝ) := by have hh := (div_le_iff₀ hρ).1 hNρ; nlinarith
  let H : ℕ := ⌈ρ*(N:ℝ)⌉₊
  have hHlow : ρ*(N:ℝ)≤(H:ℝ) := Nat.le_ceil _
  have hHupper : (H:ℝ)≤2*ρ*(N:ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0≤ρ*(N:ℝ) by positivity)
    dsimp [H]
    linarith
  have hHpos : 0<(H:ℝ) := lt_of_lt_of_le (by positivity : 0<ρ*(N:ℝ)) hHlow
  have hHN : (H:ℝ)≤(N:ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hN.le]
  have hNadd : (N+H:ℕ)≥N := Nat.le_add_right _ _
  have hNMadd : M₀≤((N+H:ℕ):ℝ) := le_trans hNM (by exact_mod_cast hNadd)
  have hu := unsmoothing a ha N H
  have hsN := hsmall₀ N hNM
  have hsNH := hsmall₀ (N+H) hNMadd
  have hsq : (((N+H:ℕ):ℝ))^2≤4*(N:ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg ((N:ℝ)-(H:ℝ)),sq_nonneg (H:ℝ)]
  have hmain : ‖triangle a (N+H)‖+‖triangle a N‖≤5*e*(N:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq he.le
    nlinarith
  have hmain' : 5*e*(N:ℝ)^2≤(ε/2)*(H:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHlow (show 0≤ε/2 by positivity)) hN.le
    calc
      _ = (ε/2)*(ρ*(N:ℝ))*(N:ℝ) := by dsimp only [e]; ring
      _ ≤ _ := hh
  have hHε : (H:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hρε hN.le
    nlinarith
  have htail : (H:ℝ)^2≤(ε/2)*(H:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hHε hHpos.le
    nlinarith
  have htotal : (H:ℝ)*‖ordinarySum a N‖≤(H:ℝ)*(ε*(N:ℝ)) := by nlinarith
  exact (mul_le_mul_iff_right₀ hHpos).1 htotal

end OrdinaryTriangular

end

end OAI
