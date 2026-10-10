import OAI.MeasureTheory.Falconer.Incidence.CoarsePencilWeights

namespace OAI

/-! Extract many original points that retain many fine tubes in one coarse
packet. Both losses follow from the actual incidence count. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_large_weight_subset (P : Finset (Space 2)) (w : Space 2 → ℝ)
    {H B : ℝ} (hP : P.Nonempty) (hH : 0 < H) (hB : 0 < B)
    (hcap : ∀ x ∈ P, w x ≤ B) (hsum : H ≤ ∑ x ∈ P, w x) :
    ∃ A ⊆ P, A.Nonempty ∧ H/(2*B) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A, H/(2*(P.card:ℝ)) ≤ w x := by
  let c := H/(2*(P.card:ℝ))
  let A := P.filter fun x => c ≤ w x
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound (x : Space 2) (hx : x ∈ P) :
      w x ≤ (if c ≤ w x then B else 0)+c := by
    by_cases h : c ≤ w x
    · rw [ite_eq_left h]
      exact (hcap x hx).trans (le_add_of_nonneg_right hc.le)
    · rw [ite_eq_right h,zero_add]
      exact (lt_of_not_ge h).le
  have htotal : H ≤ B*(A.card:ℝ)+H/2 := by
    calc
      _ ≤ ∑ x ∈ P, w x := hsum
      _ ≤ ∑ x ∈ P, ((if c ≤ w x then B else 0)+c) := Finset.sum_le_sum hbound
      _ = B*(A.card:ℝ)+H/2 := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
        dsimp [A,c]
        field_simp
  have hsize : H/(2*B) ≤ (A.card:ℝ) := (div_le_iff₀ (by positivity)).2 (by linarith only [htotal])
  have hAc : 0 < (A.card:ℝ) := (div_pos hH (by positivity)).trans_le hsize
  exact ⟨A,Finset.filter_subset _ _,Finset.card_pos.mp (Nat.cast_pos.mp hAc),hsize,
    fun x hx => (Finset.mem_filter.mp hx).2⟩

theorem coarse_packet_points {δ Δ s K M H : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hM : 0 < M) (hH : 0 < H)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (q : Space 2 → Space 2) (a : Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x))
    (hcard : ∀ x ∈ P, ((T x).card:ℝ) ≤ M)
    (hweight : H ≤ (coarsePencilWeight P T q a:ℝ)) :
    ∃ A ⊆ P, A.Nonempty ∧ H/(2*(K*Δ^s*M)) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A, H/(2*(P.card:ℝ)) ≤ (((T x).filter fun l => q l = a).card:ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  apply finite_large_weight_subset P (fun x => (((T x).filter fun l => q l = a).card:ℝ))
    hP hH (by positivity)
  · intro x hx
    have hsub : (T x).filter (fun l => q l = a) ⊆ (T x).filter (fun l => dist l a ≤ Δ) := by
      intro l hl
      obtain ⟨hlT,hla⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,by simpa only [hla] using hnear x hx l hlT⟩
    calc
      _ ≤ (((T x).filter fun l => dist l a ≤ Δ).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ K*Δ^s*((T x).card:ℝ) := normalized_ball_bound_all_radii hs hK (hball x hx) a Δ hδΔ
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcard x hx) (by positivity)
  · simpa only [coarsePencilWeight,Nat.cast_sum] using hweight

end Falconer

end OAI
