import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TriangleEqCutoff
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoundedLogSeriesCauchyDerivative

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

namespace OrdinaryCorrelations.PretentiousEuler
open OrdinaryRieszPerron OrdinaryTriangular Completion Filter

theorem moving_complete_partial_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)/2 →
      ‖∑n∈Finset.Icc 1 N, OrdinaryArchimedeanTwist.twist (complete f) τ n‖≤ε*(N:ℝ) := by
  let ρ : ℝ := min (ε/4) (1/2)
  have hρ : 0<ρ := lt_min (by positivity) (by norm_num)
  have hρε : ρ≤ε/4 := min_le_left _ _
  have hρ1 : ρ≤1/2 := min_le_right _ _
  let e : ℝ := ε*ρ/10
  have he : 0<e := by dsimp [e]; positivity
  have hte : ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)/2 →
      ‖triangle (OrdinaryArchimedeanTwist.twist (complete f) τ) N‖≤e*(N:ℝ)^2 := by
    filter_upwards [moving_cutoff_small hf hNP e he, eventually_ge_atTop (1:ℕ)] with N hs hN
    intro τ hτ
    rw [triangle_eq_cutoff _ (by omega),norm_mul,Complex.norm_natCast]
    have hh := mul_le_mul_of_nonneg_left (hs τ hτ) (Nat.cast_nonneg N)
    nlinarith
  obtain ⟨N₀,htri⟩ := eventually_atTop.1 hte
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop (1:ℕ),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1/ρ))] with N hNM hN1 hNρ
  intro τ hτ
  let a := OrdinaryArchimedeanTwist.twist (complete f) τ
  have ha (n : ℕ) : ‖a n‖≤1 := by
    simpa only [a,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded hf n
  have hN : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
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
  have hu := unsmoothing a ha N H
  have hNMadd : N₀≤N+H := hNM.trans hNadd
  have hsN := htri N hNM τ hτ
  have hτNH : |τ|≤((N+H:ℕ):ℝ)/2 := by
    push_cast
    linarith [show (0:ℝ)≤H from Nat.cast_nonneg H]
  have hsNH := htri (N+H) hNMadd τ hτNH
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

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
