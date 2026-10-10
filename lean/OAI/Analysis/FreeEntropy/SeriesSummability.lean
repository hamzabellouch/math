import OAI.Analysis.FreeEntropy.SignalCovariance

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [Fintype α]

def wordSigma : (Σ n : ℕ, List.Vector α n) ≃ List α where
  toFun v := v.2.val
  invFun w := ⟨w.length, ⟨w,rfl⟩⟩
  left_inv v := by rcases v with ⟨n,⟨w,hw⟩⟩; cases hw; rfl
  right_inv w := rfl

 theorem summable_words_iff (f : List α → ℝ) (hf : ∀ w, 0 ≤ f w) :
    Summable f ↔ Summable (fun n => ∑ v : List.Vector α n, f v.val) := by
  rw [← (wordSigma (α := α)).summable_iff]
  change Summable (fun v : Σ n : ℕ, List.Vector α n => f v.2.val) ↔ _
  have he := summable_sigma_of_nonneg
    (f := fun v : Σ n : ℕ, List.Vector α n => f v.2.val) (fun v => hf v.2.val)
  simpa only [tsum_fintype, and_iff_right (fun n => (hasSum_fintype (fun v : List.Vector α n => f v.val)).summable)] using he
 theorem tsum_words_degree (f : List α → ℝ) (hf : Summable f) :
    ∑' w, f w = ∑' n, ∑ v : List.Vector α n, f v.val := by
  have hs : Summable (fun v : Σ n : ℕ, List.Vector α n => f v.2.val) :=
    (wordSigma (α := α)).summable_iff.mpr hf
  calc
    ∑' w, f w = ∑' v : Σ n : ℕ, List.Vector α n, f v.2.val :=
      ((wordSigma (α := α)).tsum_eq f).symm
    _ = ∑' n, ∑' v : List.Vector α n, f v.val := hs.tsum_sigma
    _ = _ := by simp only [tsum_fintype]
 theorem summable_norm_sq_iff (f : Series α) :
    Summable (fun w => ‖f w‖ ^ 2) ↔ Summable (fun n => degreeNorm f n ^ 2) := by
  rw [summable_words_iff _ (fun w => sq_nonneg _)]
  simp only [degreeNorm_sq]
 theorem tsum_norm_sq_degree (f : Series α) (hf : Summable (fun w => ‖f w‖^2)) :
    ∑' w, ‖f w‖^2 = ∑' n, degreeNorm f n ^ 2 := by
  rw [tsum_words_degree _ hf]
  simp only [degreeNorm_sq]
end FiniteEntropySeparation.FreeSeries

end

end OAI
