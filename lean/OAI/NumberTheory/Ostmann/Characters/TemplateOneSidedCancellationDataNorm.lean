import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationGatedData

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable

theorem data_weight_norm_le {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) {A B : τ → ℝ} {M : ℝ}
    (h : d.Ranges ρ A B M) (x : ℝ) : ‖d.weight ρ x‖ ≤ M^(Fintype.card τ) := by
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  split_ifs with hs
  · exact historyArchimedeanProduct_norm_le ρ d.profile _ B h.nonneg
      (fun i => (h.log_range x hs i).2) h.bound
  · simpa only [norm_zero] using pow_nonneg h.nonneg (Fintype.card τ)

theorem gated_cross_weight {σ τ κ : Type*} [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) {b₀ : ℝ} (hb : 0 < b₀) (E : ℝ)
    (b : κ → Bool) (d : κ → HistoryPolynomialData σ τ) (j h : κ) (Q a n : ℕ) :
    crossProgressionWeight (longProgressionMajorant E b₀ Q a)
      (fun n z => (gatedData (b z) (d z)).weight ρ ((Q*n+a:ℕ):ℝ)) j h n =
      (E/b₀:ℂ)*(crossHistoryData b₀ (gatedData (b j) (d j))
        (gatedData (b h) (d h))).weight ρ ((Q*n+a:ℕ):ℝ) := by
  exact crossHistoryData_weight ρ hb E _ _ Q a n

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
