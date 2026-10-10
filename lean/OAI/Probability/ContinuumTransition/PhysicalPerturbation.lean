import OAI.Probability.ContinuumTransition.GibbsBridge

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem attraction_add (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (r : ℝ) :
    attraction t (fun n => σ n+τ n) R r = attraction t σ R r+attraction t τ R r := by
  unfold attraction
  simp_rw [add_mul]
  rw [Summable.tsum_add (summable_attraction_terms hσ hR hs r) (summable_attraction_terms hτ hR hτs r)]
  ring

theorem physicalProfile_add_mono {t : ℝ} (ht : 0 ≤ t) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (r : ℝ) :
    physicalProfile t (fun n => σ n+τ n) R r ≤ physicalProfile t σ R r := by
  rw [physicalProfile, physicalProfile, attraction_add t hσ hτ hR hs hτs r]
  linarith only [attraction_nonneg ht hτ hR r]

theorem physicalProfile_add_diff (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (r : ℝ) :
    physicalProfile t σ R r-physicalProfile t (fun n => σ n+τ n) R r = attraction t τ R r := by
  simp only [physicalProfile, attraction_add t hσ hτ hR hs hτs r]
  ring

theorem measurable_physical_interaction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) :
    Measurable (fun p : Space × Space => physicalProfile t σ R ‖p.1-p.2‖) :=
  (measurable_physicalProfile t hσ hR hs).comp ((measurable_fst.sub measurable_snd).norm)

theorem physicalProfile_le_core {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    physicalProfile t σ R r ≤ coreProfile t r :=
  sub_le_self _ (attraction_nonneg ht hσ hR r)

end ContinuumTemperature
end

end OAI
