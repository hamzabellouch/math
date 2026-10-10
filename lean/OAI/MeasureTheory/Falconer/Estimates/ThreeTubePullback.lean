import OAI.MeasureTheory.Falconer.Radial.ThreeTubeMass

namespace OAI

/-! # Three transverse tube counting on the original point measure -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem three_tube_pullback_mass_sq (μ : Measure X) (f : X → Space 3)
    (v : Fin 3 → Space 3) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)))
    (E : Set X) (A : Fin 3 → Finset X) (R : ℝ)
    (hE : ∀ x ∈ E, ‖f x‖ ≤ R) {δ C H s : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space 3, μ (f ⁻¹' ball p (6*δ)) ≤ ENNReal.ofReal (H*(6*δ)^s))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (f x-f a)‖ ≤ C*δ) :
    (μ E).toReal^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*
      ((6*C+35)/Δ)^6*(H*(6*δ)^s)^2 := by
  classical
  let A' (i : Fin 3) := (A i).image f
  have hE' : ∀ y ∈ f '' E, ‖y‖ ≤ R := by
    rintro y ⟨x,hx,rfl⟩
    exact hE x hx
  have hc : ∀ i : Fin 3, ∀ y ∈ f '' E, ∃ a ∈ A' i,
      ‖perpendicularPart (v i) (y-a)‖ ≤ C*δ := by
    rintro i y ⟨x,hx,rfl⟩
    obtain ⟨a,ha,ht⟩ := hcover i x hx
    exact ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,ht⟩
  obtain ⟨P,hP,hcard⟩ := three_transverse_tube_cover v hv hΔ hΔ1 hgram (f '' E) A' R hE' hδ hC hc
  have hB : 0 ≤ H*(6*δ)^s := by positivity
  have hmass : μ E ≤ ENNReal.ofReal ((P.card:ℝ)*(H*(6*δ)^s)) := by
    calc
      _ ≤ μ (⋃ p ∈ P, f ⁻¹' ball p (6*δ)) := by
        apply measure_mono
        intro x hx
        obtain ⟨p,hp,hd⟩ := hP (f x) ⟨x,hx,rfl⟩
        exact mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,by change dist (f x) p < 6*δ; linarith⟩⟩
      _ ≤ ∑ p ∈ P, μ (f ⁻¹' ball p (6*δ)) := measure_biUnion_finset_le P _
      _ ≤ ∑ _p ∈ P, ENNReal.ofReal (H*(6*δ)^s) := Finset.sum_le_sum (fun p _ => hball p)
      _ = (P.card:ℝ≥0∞)*ENNReal.ofReal (H*(6*δ)^s) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ = _ := by rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hB)] at hreal
  calc
    _ ≤ ((P.card:ℝ)*(H*(6*δ)^s))^2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
    _ = (P.card:ℝ)^2*(H*(6*δ)^s)^2 := by ring
    _ ≤ ((A' 0).card:ℝ)*((A' 1).card:ℝ)*((A' 2).card:ℝ)*
        ((6*C+35)/Δ)^6*(H*(6*δ)^s)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ ≤ _ := by gcongr <;> exact Finset.card_image_le

end Falconer

end OAI
