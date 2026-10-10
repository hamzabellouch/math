import OAI.MeasureTheory.Falconer.Fourier.MaskedFourier
import OAI.MeasureTheory.Falconer.Measures.AmbientProduct
import OAI.MeasureTheory.Falconer.Estimates.ScaledInverseRemainder

namespace OAI

/-! # The actual masked distance law as a cell-scaled stationary target

The unit profile is evaluated at depth divided by N in the descriptor
amplitude. Both masks and the original pair law remain in this identity.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def descriptorPairAmplitude {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (x y w : Space d) : ℂ :=
  (descriptorAmbientProduct Q ρ f N σ J i B S x w : ℂ)*
    (descriptorAmbientProduct Q ρ f N σ J i B S y w : ℂ)

theorem descriptorPairAmplitude_measurable {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (fun p : (Space d × Space d) × Space d =>
      descriptorPairAmplitude Q ρ f N σ J i B S p.1.1 p.1.2 p.2) := by
  have hm := descriptorAmbientProduct_measurable Q ρ f N σ J i B S
  exact (Complex.measurable_ofReal.comp (hm.comp (measurable_fst.fst.prodMk measurable_snd))).mul
    (Complex.measurable_ofReal.comp (hm.comp (measurable_fst.snd.prodMk measurable_snd)))

theorem maskedCellDistance_fourier_scaled_kernel (n : ℕ) (w₀ : Sphere (n+3))
    (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i a : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
    (hcover : ∀ b ∈ B, ∀ w : Sphere (n+3),
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (X Y : DyadicCube (n+3))
    (hne : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z.1-z.2 ≠ 0)
    (r : ℝ) :
    charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r =
      ((profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹) •
        ∫ z, scaledDistanceKernel n ((2:ℝ)^a)⁻¹ r
          (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S) z
          ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier) := by
  rw [maskedCellDistance_fourier w₀ Q ρ m N σ J i a B S hcover X Y r,← integral_smul]
  apply integral_congr_ae
  filter_upwards [hne] with z hz
  have hw : NormedSpace.normalize (z.1-z.2) =
      (normalizeToSphere w₀ (z.1-z.2) : Space (n+3)) :=
    (normalizeToSphere_coe_of_ne w₀ hz).symm
  have hexp : -((((n+3:ℕ):ℝ)-1)/2) = -(((n+2:ℕ):ℝ)/2) := by
    push_cast
    ring
  simp only [scaledDistanceKernel,descriptorPairAmplitude,descriptorPairWeight,hw,
    descriptorAmbientProduct_sphere,div_inv_eq_mul,hexp,Complex.real_smul,
    Complex.ofReal_mul]
  push_cast
  ring

end Falconer

end OAI
