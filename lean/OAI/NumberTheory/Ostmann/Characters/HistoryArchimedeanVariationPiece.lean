import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationChain
import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationWindow

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Set
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable

theorem historyArchimedeanProduct_piece_variation_le {ι : Type*} [Fintype ι]
    (ρ : 𝓢(ℝ,ℂ)) (profile : ι → HistoryProfile) (z : ι → ℝ → ℝ)
    (A B : ι → ℝ) (S : Set ℝ) (hS : Convex ℝ S) (Q a N : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hAB : ∀ i, A i ≤ B i)
    (hz : ∀ i t, t ∈ S → z i t ∈ Set.Icc (A i) (B i))
    (hmono : ∀ i, MonotoneOn (z i) S ∨ AntitoneOn (z i) S)
    (hbound : ∀ i, (profile i).bound ρ (B i) ≤ M) :
    progressionVariation (sampledSetWeight S Q a
      (fun n => historyArchimedeanProduct ρ profile (fun i => z i ((Q*n+a : ℕ) : ℝ)))) N ≤
        M ^ (Fintype.card ι) * (3 + (∑ i : ι, (B i - A i))) := by
  classical
  rcases sampled_convex_window S hS Q a N with hempty | ⟨lo,hi,hlh,hhN,hwin⟩
  · have heq := progressionVariation_congr N
      (sampledSetWeight S Q a
        (fun n => historyArchimedeanProduct ρ profile (fun i => z i ((Q*n+a : ℕ) : ℝ))))
      (fun _ => 0) (fun n hn => by simp only [sampledSetWeight,ite_eq_right (hempty n hn)])
    rw [heq]
    simp only [progressionVariation,sub_self,norm_zero,Finset.sum_const_zero,add_zero]
    exact mul_nonneg (pow_nonneg hM _) (add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hAB i))))
  · have heq := progressionVariation_congr N
      (sampledSetWeight S Q a
        (fun n => historyArchimedeanProduct ρ profile (fun i => z i ((Q*n+a : ℕ) : ℝ))))
      (intervalRestrictedWeight lo hi
        (fun n => historyArchimedeanProduct ρ profile (fun i => z i ((Q*n+a : ℕ) : ℝ))))
      (fun n hn => by simp only [sampledSetWeight,intervalRestrictedWeight,hwin n hn])
    rw [heq]
    apply historyArchimedeanProduct_interval_variation_le ρ profile _ A B hlh N hM
    · intro i n hn
      exact hz i _ ((hwin n (hn.2.trans hhN)).mpr hn)
    · intro i
      rcases hmono i with hm | hm
      · left
        intro n hn m hm' hnm
        exact hm ((hwin n (hn.2.trans hhN)).mpr hn)
          ((hwin m (hm'.2.trans hhN)).mpr hm')
          (by exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left Q hnm) a)
      · right
        intro n hn m hm' hnm
        exact hm ((hwin n (hn.2.trans hhN)).mpr hn)
          ((hwin m (hm'.2.trans hhN)).mpr hm')
          (by exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left Q hnm) a)
    · exact hbound

theorem log_ratio_monotone_on {S : Set ℝ} (P : ℝ → ℝ) {X : ℝ} (hX : 0 < X)
    (hP : ∀ t ∈ S, 0 < P t)
    (hm : MonotoneOn P S ∨ AntitoneOn P S) :
    MonotoneOn (fun t => Real.log (X/P t)) S ∨
      AntitoneOn (fun t => Real.log (X/P t)) S := by
  rcases hm with hm | hm
  · right
    intro x hx y hy hxy
    apply Real.log_le_log (div_pos hX (hP y hy))
    exact div_le_div_of_nonneg_left hX.le (hP x hx) (hm hx hy hxy)
  · left
    intro x hx y hy hxy
    apply Real.log_le_log (div_pos hX (hP x hx))
    exact div_le_div_of_nonneg_left hX.le (hP y hy) (hm hx hy hxy)

end Ostmann.Characters

end

end OAI
