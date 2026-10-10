import OAI.MeasureTheory.Falconer.Fourier.JetStateFarExpansion
import OAI.MeasureTheory.Falconer.Fourier.StationaryScales
import OAI.MeasureTheory.Falconer.Angular.SphereFrequency
import OAI.MeasureTheory.Falconer.Angular.AngularStationaryRadialError

namespace OAI

/-! # Power-saving remainders for the exact far-state amplitudes -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem stationary_sphere_remainder_scale (m J : ℕ) {R D Λ κ : ℝ}
    (hR : 1 ≤ R) (hD : 0 ≤ D) (hΛ : 1 ≤ Λ) (hupper : D ≤ R^2)
    (hratio : D^2/Λ ≤ R^(-κ)) :
    Λ^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*D^(2*J+(m+2)+1) ≤
      R^(-κ*(J:ℝ)+2*(m+3)) := by
  have hp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hs := stationary_remainder_scale J (m+1) hR hD hp hupper hratio
  have hd : Λ^(-((m+2:ℕ):ℝ)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))
  have hJpow : Λ^(-(J:ℝ)) = (Λ⁻¹)^J := by
    rw [Real.rpow_neg hp.le, Real.rpow_natCast, inv_pow]
  have he : Λ^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*D^(2*J+(m+2)+1) =
      Λ^(-((m+2:ℕ):ℝ)/2)*((Λ⁻¹)^J*D^(2*J+(m+1)+2)) := by
    rw [show -(J:ℝ)-((m+2:ℕ):ℝ)/2 = -(J:ℝ)+(-((m+2:ℕ):ℝ)/2) by ring,
      Real.rpow_add hp, hJpow,
      show 2*J+(m+2)+1 = 2*J+(m+1)+2 by omega]
    ring
  rw [he]
  have hexp : -κ*(J:ℝ)+2*(((m+1:ℕ):ℝ)+2) = -κ*(J:ℝ)+2*((m:ℝ)+3) := by
    push_cast
    ring
  rw [hexp] at hs
  exact (mul_le_mul_of_nonneg_right hd (by positivity)).trans (by simpa only [one_mul] using hs)

theorem exists_jetState_far_sphere_power
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J K L : ℕ) (hJ : 1 ≤ J) (hL : 2*J+(m+2)+1 ≤ L) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J₀ i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (x y : Space (m+3))
        (e : Sphere (m+3)) (R Λ κ : ℝ), 1 ≤ R → 1 ≤ Λ →
      2*(E+Dq) ≤ R^2 → (2*(E+Dq))^2/Λ ≤ R^(-κ) →
      ‖sphereOscillation Λ e (fun w => f.value Q ρ profile N σ J₀ i S A x w*
            star (f.value Q ρ profile N σ J₀ i S A y w))-
          stationarySphereApprox m J Λ (f.pairAmbient Q ρ profile N σ J₀ i S A x y) e‖ ≤
        C*(B^K*A⁻¹)^2*R^(-κ*(J:ℝ)+2*(m+3)) := by
  obtain ⟨B,C,hB,hC,h⟩ := exists_jetState_far_sphere_expansion hgnomonic hquadratic m J K L hJ hL
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f x y e R Λ κ hR hΛ hupper hratio
  have hraw := h F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f x y e Λ hΛ
  have hsmall := stationary_sphere_remainder_scale m J hR (zero_le_one.trans hD)
    hΛ hupper hratio
  apply hraw.trans
  calc
    _ = C*(B^K*A⁻¹)^2*(Λ^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*(2*(E+Dq))^(2*J+(m+2)+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC (sq_nonneg _))

end Falconer

end OAI
