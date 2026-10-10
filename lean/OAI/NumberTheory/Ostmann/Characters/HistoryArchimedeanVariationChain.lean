import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationBoundary
import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationProduct

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators SchwartzMap

theorem monotone_log_chain_variation_le (z : ℕ → ℝ) {a b : ℕ} {A B : ℝ}
    (hab : a ≤ b) (hz : ∀ n ∈ Set.Icc a b, z n ∈ Set.Icc A B)
    (hmono : MonotoneOn z (Set.Icc a b) ∨ AntitoneOn z (Set.Icc a b)) :
    (∑ n ∈ Finset.Ico a b, |z (n+1)-z n|) ≤ B-A := by
  have ha := hz a ⟨le_refl _,hab⟩
  have hb := hz b ⟨hab,le_refl _⟩
  rcases hmono with hmono | hanti
  · have he : (∑ n ∈ Finset.Ico a b, |z (n+1)-z n|) = z b-z a := by
      calc
        _ = ∑ n ∈ Finset.Ico a b, (z (n+1)-z n) := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn1,hn2⟩ := Finset.mem_Ico.mp hn
          exact abs_of_nonneg (sub_nonneg.mpr (hmono ⟨hn1,by omega⟩ ⟨by omega,by omega⟩ (by omega)))
        _ = _ := Finset.sum_Ico_sub z hab
    rw [he]
    linarith [ha.1,hb.2]
  · have he : (∑ n ∈ Finset.Ico a b, |z (n+1)-z n|) = -(z b-z a) := by
      calc
        _ = ∑ n ∈ Finset.Ico a b, -(z (n+1)-z n) := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn1,hn2⟩ := Finset.mem_Ico.mp hn
          exact abs_of_nonpos (sub_nonpos.mpr (hanti ⟨hn1,by omega⟩ ⟨by omega,by omega⟩ (by omega)))
        _ = _ := by rw [Finset.sum_neg_distrib,Finset.sum_Ico_sub z hab]
    rw [he]
    linarith [ha.2,hb.1]

theorem historyArchimedeanProduct_interval_variation_le {ι : Type*} [Fintype ι]
    (ρ : 𝓢(ℝ,ℂ)) (profile : ι → HistoryProfile) (z : ι → ℕ → ℝ)
    (A B : ι → ℝ) {a b : ℕ} (hab : a ≤ b) (N : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hz : ∀ i n, n ∈ Set.Icc a b → z i n ∈ Set.Icc (A i) (B i))
    (hmono : ∀ i, MonotoneOn (z i) (Set.Icc a b) ∨ AntitoneOn (z i) (Set.Icc a b))
    (hbound : ∀ i, (profile i).bound ρ (B i) ≤ M) :
    progressionVariation (intervalRestrictedWeight a b
      (fun n => historyArchimedeanProduct ρ profile (fun i => z i n))) N ≤
        M ^ (Fintype.card ι) * (3 + (∑ i : ι, (B i - A i))) := by
  classical
  have hnorm (n : ℕ) (hn1 : a ≤ n) (hn2 : n ≤ b) :
      ‖historyArchimedeanProduct ρ profile (fun i => z i n)‖ ≤ M^(Fintype.card ι) :=
    historyArchimedeanProduct_norm_le ρ profile _ B hM
      (fun i => (hz i n ⟨hn1,hn2⟩).2) hbound
  have hboundary := progressionVariation_interval_restriction_le a b N
    (fun n => historyArchimedeanProduct ρ profile (fun i => z i n))
    (pow_nonneg hM _) hnorm
  have hsum : (∑ n ∈ Finset.Ico a b,
      ‖historyArchimedeanProduct ρ profile (fun i => z i (n+1))-
        historyArchimedeanProduct ρ profile (fun i => z i n)‖) ≤
      M ^ (Fintype.card ι) * (∑ i : ι, (B i - A i)) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico a b,
          M^(Fintype.card ι)*(∑ i : ι, |z i (n+1)-z i n|) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1,hn2⟩ := Finset.mem_Ico.mp hn
        exact historyArchimedeanProduct_difference_le ρ profile _ _ A B hM
          (fun i => hz i n ⟨hn1,by omega⟩)
          (fun i => hz i (n+1) ⟨by omega,by omega⟩) hbound
      _ = M^(Fintype.card ι)*(∑ i : ι, ∑ n ∈ Finset.Ico a b, |z i (n+1)-z i n|) := by
        rw [← Finset.mul_sum,Finset.sum_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => monotone_log_chain_variation_le (z i) hab (hz i) (hmono i)))
        (pow_nonneg hM _)
  nlinarith only [hboundary,hsum]

end Ostmann.Characters

end

end OAI
