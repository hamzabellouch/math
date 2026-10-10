import OAI.NumberTheory.TwoPoint.Halasz.HalaszModerateCutoff
import OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalCofactor
import OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalDecay

namespace OAI

/-! Actual cofactor decay on the moderate-frequency part of the
complement of the minimizing twist. -/
namespace TwoPointCorrelations

open Filter Finset
open scoped Classical

theorem halasz_moderate_cofactor :
    ∃ X₀ : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N:ℝ)/a⌋₊:ℝ) →
      n = ⌊(2*N:ℝ)/a⌋₊ → ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (ι : Type*) (J : Finset ι) (P : ι → Finset ℕ) (Q : Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) → (∀ p ∈ Q, p.Prime) →
      (2:ℝ)^J.card ≤ (Real.log n)^(1/1000:ℝ) →
      ∀ t τ : ℝ,
      (∀ v : ℝ, |v| ≤ X → squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X) →
      |t|+(Real.log n)^8 ≤ X →
      |t-τ|+(Real.log n)^8 ≤ (Real.log X)^20 →
      (Real.log n)^(1/16:ℝ)/2 ≤ |t-τ| →
      ‖mrtCofactorPolynomial Q (mrtTypicalCoefficient J P F) N a t‖ ≤
        (Real.log n)^(-1/40:ℝ) := by
  obtain ⟨C,K,X₀,hC,hK,hcofactor⟩ := halasz_exceptional_typical_window
  refine ⟨X₀,?_⟩
  have hlog : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [halasz_moderate_cutoff K,
    hlog.eventually (halasz_exceptional_decay C hC.le),
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with n hcut hdec hln
  intro N a ha hbase hn X hnX hX F hF1 hFm hFb ι J P Q hP hQ hJ t τ hmin ht hmoderate haway
  have hln0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hM : 0 ≤ (3/100:ℝ)*Real.log (Real.log n) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hln)
  have hd : ∀ v:ℝ, |v-t| ≤ (Real.log n)^8 → 1/2 ≤ |v-τ| →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
    intro v hv hunit
    have hvX : |v| ≤ X := by
      have hh := abs_add_le (v-t) t
      rw [sub_add_cancel] at hh
      linarith
    have hvτ : |v-τ| ≤ (Real.log X)^20 := by
      have hh := abs_add_le (v-t) (t-τ)
      have he : v-t+(t-τ)=v-τ := by ring
      rw [he] at hh
      linarith
    exact hcut X hnX hX F hFb v τ hunit hvτ (hmin v hvX)
  have hb := hcofactor N a ha hbase F hF1 hFm hFb ι J P Q hP hQ t τ
    ((3/100:ℝ)*Real.log (Real.log n)) hM (by simpa only [← hn] using hd)
  have hsave := hdec ((2:ℝ)^J.card) (τ-t) (by positivity) hJ
    (by simpa only [abs_sub_comm] using haway)
  apply hb.trans
  simpa only [← hn, mul_comm C] using hsave

end TwoPointCorrelations

end OAI
