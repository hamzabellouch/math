import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.SpatialInnerBump
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePlaneWaveSub3

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped ComplexConjugate
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

lemma spatial_angular_kernel_measurableND (σ : Measure V) [SFinite σ] (r : ℝ)
    {ψ : V → ℂ} {b c : V → V → ℂ} (hψ : Measurable ψ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c)) :
    Measurable (fun z : V × V => ∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
      b z.1 w*conj (c z.2 w) ∂σ) := by
  have hm : Measurable (fun z : (V × V) × V => ψ z.2*spherePlaneWaveND r (z.1.1-z.1.2) z.2*
      b z.1.1 z.2*conj (c z.1.2 z.2)) := by
    exact (((hψ.comp measurable_snd).mul
      (by unfold spherePlaneWaveND; fun_prop)).mul
        (hb.comp (measurable_fst.fst.prodMk measurable_snd))).mul
          (Complex.continuous_conj.measurable.comp
            (hc.comp (measurable_fst.snd.prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma spatial_angular_kernel_boundND (σ : Measure V) [IsFiniteMeasure σ] (r : ℝ)
    (ψ : V → ℂ) (b c : V → V → ℂ) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) (z : V × V) :
    ‖∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w) ∂σ‖ ≤
      P*B*C*σ.real univ := by
  have hP₀ : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hB₀ : 0 ≤ B := (norm_nonneg (b 0 0)).trans (hB 0 0)
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  simp only [norm_mul,spherePlaneWaveND_norm,Complex.norm_conj,mul_one]
  exact mul_le_mul (mul_le_mul (hP w) (hB z.1 w) (norm_nonneg _) hP₀)
    (hC z.2 w) (norm_nonneg _) (mul_nonneg hP₀ hB₀)

theorem spatial_angular_factorizationND (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (scale : ℝ) (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set V) (M N r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) :
    ((M*N)⁻¹:ℝ) • (∫ z : V × V,
      SpatialFourierND.spatialAnnulusKernel d δ L hδ hL j (scale⁻¹ • (z.1-z.2)) *
        (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w) ∂σ)
          ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ∫ ξ, SpatialFourierND.spatialFourierCoeff d δ L hδ hL j ξ *
        ∫ w, ψ w*sourceAngularTransformND ρ X M
          (fun x w => SpatialFourierND.spatialFourierPhase d scale ξ x*b x w) r w *
          conj (sourceAngularTransformND ν Y N
            (fun y w => SpatialFourierND.spatialFourierPhase d scale ξ y*c y w) r w) ∂σ := by
  rw [SpatialFourierND.spatialFourier_integral_swap d δ L hδ hL j scale _ _
    (spatial_angular_kernel_measurableND σ r hψ hb hc)
    (spatial_angular_kernel_boundND σ r ψ b c hP hB hC)]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  let p := SpatialFourierND.spatialFourierPhase d scale ξ
  have hp : Measurable p := by
    dsimp [p,SpatialFourierND.spatialFourierPhase]
    fun_prop
  have hpn (x : V) : ‖p x‖=1 := SpatialFourierND.spatialFourierPhase_norm d scale ξ x
  have hf := angular_pair_factorizationND σ ρ ν X Y M N r
    (b := fun x w => p x*b x w) (c := fun y w => p y*c y w) hψ
    ((hp.comp measurable_fst).mul hb) ((hp.comp measurable_fst).mul hc)
    hP (fun x w => by simpa only [norm_mul,hpn,one_mul] using hB x w)
      (fun y w => by simpa only [norm_mul,hpn,one_mul] using hC y w)
  have he : (∫ z : V × V, SpatialFourierND.spatialPairPhase d scale ξ z *
      (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w) ∂σ)
      ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ∫ z : V × V, (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
        (p z.1*b z.1 w)*conj (p z.2*c z.2 w) ∂σ)
      ∂(ρ.restrict X).prod (ν.restrict Y) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    simp only [SpatialFourierND.spatialPairPhase,p,map_mul]
    ring
  rw [he]
  simp only [Complex.real_smul] at hf ⊢
  rw [mul_left_comm, hf]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
