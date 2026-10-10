import OAI.MeasureTheory.Falconer.Incidence.BoundedFrozenHeavyCover
import OAI.MeasureTheory.Falconer.Angular.GoodDirectionMass
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass

namespace OAI

/-! # A good witness controls the full conditional heavy radial fiber -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem radial_collision_le_tube_mass (μ : Measure (Space (n+1)))
    (x z : Space (n+1)) (hz : z ≠ x) {H δ W : ℝ}
    (hsource : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) (hwidth : H*δ ≤ W) :
    radialCollisionMass μ δ (z,x) ≤
      μ {y | ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W} := by
  apply measure_mono_ae
  filter_upwards [hsource] with y hy
  intro hclose
  have hv : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hv (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hv]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have he : perpendicularPart (normalize (z-x)) (y-x) =
      ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact (mul_le_mul hy hperp (norm_nonneg _) ((norm_nonneg _).trans hy)).trans hwidth

theorem middle_heavy_radial_mass_lt (μ : Measure (Space (n+1)))
    (x c : Space (n+1)) {r D δ θ C B H η R : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B) (hpin : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (Bad : Set (Sphere (n+1))) (v : Sphere (n+1)) (hv : v ∉ Bad)
    (hdir : ‖normalize (c-x)-(v:Space (n+1))‖ ≤ η ∨
      ‖normalize (c-x)+(v:Space (n+1))‖ ≤ η)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*η*(B+B) ≤ R)
    (F a : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B ∧
      F < radialCollisionMass μ θ (z,x)) : μ T < a := by
  obtain ⟨J,hJ,hcover,hcard⟩ := bounded_frozen_heavy_tube_cover μ x c hr hcx hδ
    hfreeze hsource T (fun z hz => ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1⟩)
    F (fun z hz => (hT z hz).2.2.2.le.trans
      (radial_collision_le_tube_mass μ x z (hT z hz).1 hpin hwidth)) L hL
  exact mass_lt_of_good_direction_cover μ Bad v hv _
    (norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))) hdir hrobust hbounded J hJ
    J.card le_rfl a (fun S hS => henvelope S
      ((mul_le_mul' (by exact_mod_cast hS) le_rfl).trans hcard)) T hcover

end Falconer

end OAI
