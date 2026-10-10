import OAI.MeasureTheory.Falconer.Radial.HeavyProjectedCover
import OAI.MeasureTheory.Falconer.Radial.RadialFreezing

namespace OAI

/-! # Actual parallel tube covers of troublesome original source fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem perpendicularPart_idempotent (v z : Space (n+1)) (hv : ‖v‖ = 1) :
    perpendicularPart v (perpendicularPart v z) = perpendicularPart v z := by
  simp [perpendicularPart,inner_sub_right,inner_smul_right,hv]

theorem frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P,
        ‖perpendicularPart (normalize (c-x)) (z-p)‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  let v := normalize (c-x)
  have hv : ‖v‖ = 1 := norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))
  let f : Space (n+1) → Space (n+1) := perpendicularPart v
  have hf : Measurable f := by unfold f perpendicularPart; fun_prop
  have hbd : ∀ z ∈ T, ‖f z‖ ≤ B := fun z hz =>
    (norm_perpendicularPart_le hv z).trans (hT z hz).2.2
  have hmass : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ (C+1)*δ} := by
    intro z hz
    apply (hheavy z hz).trans
    apply measure_mono_ae
    filter_upwards [hsource] with y hy
    intro ht
    have hh := frozen_radial_tube_error x c z y hr hcx (hT z hz).1 (hT z hz).2.1 hy ht
    change ‖perpendicularPart v y-perpendicularPart v z‖ ≤ _
    rw [← perpendicularPart_sub]
    exact hh.trans (by nlinarith)
  obtain ⟨P,hP,hcard⟩ := heavy_projected_grid_cover μ f hf T hδ hbd F hmass L hL
  refine ⟨P,?_,hcard⟩
  intro z hz
  obtain ⟨p,hp,hclose⟩ := hP z hz
  refine ⟨p,hp,?_⟩
  have he : perpendicularPart v (z-p) = perpendicularPart v (f z-p) := by
    rw [perpendicularPart_sub,perpendicularPart_sub]
    dsimp [f]
    rw [perpendicularPart_idempotent v z hv]
  rw [he]
  exact (norm_perpendicularPart_le hv _).trans hclose

end Falconer

end OAI
