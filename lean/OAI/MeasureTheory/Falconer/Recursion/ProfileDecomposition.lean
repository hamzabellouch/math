import OAI.MeasureTheory.Falconer.Recursion.ProfileMerging
import OAI.MeasureTheory.Falconer.Estimates.QuantitativeDifferentiation

namespace OAI

/-! Quantitative slope decomposition of the profile, with a uniform minimum
interval length and explicit uncovered-length bound. -/
namespace Falconer
open Set

private theorem equal_width_sum (H : ℝ) (S : List (ℝ × ℝ))
    (hw : ∀ c ∈ S, c.2 = H) : (S.map Prod.snd).sum = H*(S.length : ℝ) := by
  induction S with
  | nil => simp
  | cons c S ih =>
    have ht := ih (fun d hd => hw d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [hw c (by simp),ht]
    ring

theorem quantitative_profile_slope_decomposition {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (f : ℝ → ℝ), LipschitzWith 2 f →
      ∀ (m ε s t : ℝ), 0 < m → 0 ≤ ε → s < t → f 0 = 0 →
      (∀ x ∈ Icc 0 m, t*x-ε*m ≤ f x) →
      ∃ R : List (ℝ × ℝ), StructuredProfilePieces f (τ*m) (2*η) s m R ∧
        m*(1-η^2-η-ε/(t-s)) ≤ (R.map Prod.snd).sum := by
  obtain ⟨τ,hτ,ht⟩ := quantitative_uniform_linear_decomposition (sq_pos_of_pos hη)
  refine ⟨η*τ,mul_pos hη hτ,?_⟩
  intro f hf m ε s t hm hε hst hf0 hlower
  obtain ⟨S,⟨H,hH,hHm,hHlow,hwidth⟩,hord,hcover,hcells⟩ := ht f hf 0 m hm
  have hF : ProfileCellFamily f H (η*H) η m m S := by
    constructor
    · apply hord.imp_of_mem
      intro c d hc _ hcd
      simpa only [hwidth c hc] using hcd
    · intro c hc
      have hb := hcells c hc
      have he := hwidth c hc
      refine ⟨hb.1,?_,?_,he.le,?_⟩
      · simpa only [zero_add,he] using hb.2.1
      · rw [he]
        nlinarith [mul_le_mul_of_nonneg_right hη1 hH.le]
      · simpa only [zero_add] using hb.2.1
    · intro c hc x hx
      have he := hwidth c hc
      simpa only [he] using (hcells c hc).2.2.2 x (by simpa only [he] using hx)
  obtain ⟨R,hR,hlen⟩ := merge_profile_cells hf hH hη hm hε hst hf0 hlower S m hm.le le_rfl hF
  have hsum := equal_width_sum H S hwidth
  have hsumBound : (S.map Prod.snd).sum ≤ m := by
    simpa only [sub_zero] using ordered_interval_length_le hm.le hord (by
      intro c hc
      have hb := hcells c hc
      exact ⟨hb.1,by simpa only [zero_add] using hb.2.1,by rw [hwidth c hc]; exact hH.le⟩)
  have hcost : η*H*(S.length : ℝ) ≤ η*m := by
    calc
      _ = η*(S.map Prod.snd).sum := by rw [hsum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumBound hη.le
  refine ⟨R,⟨hR.ordered,?_,hR.alternatives⟩,?_⟩
  · intro c hc
    have hb := hR.bounds c hc
    refine ⟨hb.1,hb.2.1,?_⟩
    have he := mul_le_mul_of_nonneg_left hHlow hη.le
    nlinarith [hb.2.2]
  · have he : m*(1-η^2-η-ε/(t-s)) = m*(1-η^2)-η*m-ε*m/(t-s) := by ring
    rw [he]
    linarith

end Falconer

end OAI
