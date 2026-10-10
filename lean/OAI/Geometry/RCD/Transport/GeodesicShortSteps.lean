import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! # Finite short-step estimates along an actual geodesic -/

open Set Metric

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- A uniform estimate for short pairs on one geodesic controls its endpoints
with the same constant. The proof uses a finite equal-time subdivision. -/
theorem IsGeodesic.short_step_bound {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (f : X → ℝ) {L δ : ℝ} (hδ : 0 < δ)
    (hshort : ∀ s t : Time, dist (γ s) (γ t) ≤ δ →
      |f (γ s)-f (γ t)| ≤ L*dist (γ s) (γ t)) :
    |f (γ 0)-f (γ 1)| ≤ L*dist (γ 0) (γ 1) := by
  let d := dist (γ 0) (γ 1)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (d/δ) 0)
  have hN0 : (0:ℝ) < N := (le_max_right _ _).trans_lt hN
  have hNd : d/(N:ℝ) ≤ δ := by
    have hh : d/δ < N := (le_max_left _ _).trans_lt hN
    apply (div_le_iff₀ hN0).mpr
    have hh' := (div_lt_iff₀ hδ).mp hh
    nlinarith
  let τ (i : ℕ) : Time := ⟨min ((i:ℝ)/N) 1,
    le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hτ (i : ℕ) (hi : i ≤ N) : (τ i : ℝ) = (i:ℝ)/N := by
    apply min_eq_left
    exact (div_le_one hN0).mpr (by exact_mod_cast hi)
  have hτ0 : τ 0 = 0 := by apply Subtype.ext; simp [τ]
  have hτN : τ N = 1 := by
    apply Subtype.ext
    rw [hτ N le_rfl,div_self hN0.ne']
    rfl
  have hstep (i : ℕ) (hi : i < N) : dist (γ (τ i)) (γ (τ (i+1))) = d/N := by
    rw [hγ,hτ i hi.le,hτ (i+1) (by omega)]
    have he : (i:ℝ)/(N:ℝ)-((i+1:ℕ):ℝ)/N = -(N:ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [he,abs_neg,abs_of_pos (inv_pos.mpr hN0)]
    dsimp only [d]
    ring
  have hb := dist_le_range_sum_dist (fun i => f (γ (τ i))) N
  rw [hτ0,hτN] at hb
  have hs : (∑ i ∈ Finset.range N, dist (f (γ (τ i))) (f (γ (τ (i+1))))) ≤ L*d := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N, L*(d/N) := by
        apply Finset.sum_le_sum
        intro i hi
        have his : i < N := Finset.mem_range.mp hi
        rw [Real.dist_eq]
        exact (hshort (τ i) (τ (i+1)) (by rw [hstep i his]; exact hNd)).trans_eq
          (by rw [hstep i his])
      _ = L*d := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        field_simp
  exact (show |f (γ 0)-f (γ 1)| ≤ _ by simpa only [Real.dist_eq] using hb).trans hs

end RegularPointCoordinates

end

end OAI
