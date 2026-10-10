import OAI.MeasureTheory.Falconer.Angular.SphereInverse
import OAI.MeasureTheory.Falconer.Angular.NorthRotation

namespace OAI

/-! # Transporting the inverse amplitude in the angular variable

The endpoint laws and their dyadic cells are not changed. Only the sphere
integration variable and the directional derivatives of its amplitude rotate.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem sphereOscillation_isometry {d : ℕ} (T : Space d ≃ₗᵢ[ℝ] Space d)
    (Λ : ℝ) (e : Sphere d) (B : Sphere d → ℂ) :
    sphereOscillation Λ (sphereMap T e) B =
      sphereOscillation Λ e (fun w => B (sphereMap T w)) := by
  rw [sphereOscillation,← sphere_integral_rotation T]
  unfold sphereOscillation
  apply integral_congr_ae
  filter_upwards with w
  change Complex.exp (Complex.I*(Λ:ℂ)*(inner ℝ (T (w:Space d)) (T (e:Space d)):ℝ))*_ = _
  rw [T.inner_map_map]

noncomputable def rotatedInverseAmplitude (m : ℕ) (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3))
    (B : Space (m+3) → ℂ) (j : ℕ) (w : Space (m+3)) : ℂ :=
  localInverseAmplitude m (B ∘ T.symm) j (T w)

theorem rotatedInverseAmplitude_contDiff (m : ℕ) (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3))
    {B : Space (m+3) → ℂ} (hB : ContDiff ℝ ∞ B) (j : ℕ) :
    ContDiff ℝ ∞ (rotatedInverseAmplitude m T B j) :=
  (localInverseAmplitude_contDiff m (hB.comp T.symm.contDiff) j).comp T.contDiff

theorem rotatedInverseAmplitude_scaled_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3))
      (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (rotatedInverseAmplitude m T B j) w‖ ≤ A*C*D^(k+2*j) := by
  obtain ⟨A,hA,hbound⟩ := localInverseAmplitude_scaled_budget m j r
  refine ⟨A,hA,?_⟩
  intro T B hB C D hC hD hb k hk w
  have hb' : ∀ l ≤ r+2*j, ∀ u : Sphere (m+3),
      ‖iteratedFDeriv ℝ l (B ∘ T.symm) u‖ ≤ C*D^l := by
    intro l hl u
    rw [T.symm.norm_iteratedFDeriv_comp_right]
    exact hb l hl (sphereMap T.symm u)
  change ‖iteratedFDeriv ℝ k ((localInverseAmplitude m (B ∘ T.symm) j) ∘ T) w‖ ≤ _
  rw [T.norm_iteratedFDeriv_comp_right]
  exact hbound (B ∘ T.symm) (hB.comp T.symm.contDiff) C D hC hD hb' k hk (sphereMap T w)

theorem rotated_inverse_sphere_sum (m J : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    (∑ j ∈ Finset.range (J+1), ((Λ^(-(j:ℝ)):ℝ):ℂ)*
      sphereOscillation Λ e (fun w => rotatedInverseAmplitude m T B j w)) =
      inverseSphereSum m J Λ (B ∘ T.symm) (sphereMap T e) := by
  unfold inverseSphereSum
  apply Finset.sum_congr rfl
  intro j _
  rw [sphereOscillation_isometry]
  rfl

theorem rotated_sphere_inverse_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (e : Sphere (m+3)),
      ‖T (e:Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ^(((m+2:ℕ):ℝ)/2):ℝ):ℂ)*
          (∑ j ∈ Finset.range (J+1), ((Λ^(-(j:ℝ)):ℝ):ℂ)*
            sphereOscillation Λ e (fun w => rotatedInverseAmplitude m T B j w)) -
        Complex.exp (Complex.I*(Λ:ℂ))*B e‖ ≤
      A*Λ^(-((J+1:ℕ):ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
  obtain ⟨A,hA,hbound⟩ := sphere_inverse_expansion hgnomonic hquadratic m J
  refine ⟨A,hA,?_⟩
  intro T e he B hB C D hC hD hb Λ hΛ
  have hb' : ∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ j (B ∘ T.symm) w‖ ≤ C*D^j := by
    intro j hj w
    rw [T.symm.norm_iteratedFDeriv_comp_right]
    exact hb j hj (sphereMap T.symm w)
  have hh := hbound (sphereMap T e) he (B ∘ T.symm) (hB.comp T.symm.contDiff)
    C D hC hD hb' Λ hΛ
  rw [rotated_inverse_sphere_sum]
  simpa only [Function.comp_apply,sphereMap,T.symm_apply_apply] using hh

end Falconer

end OAI
