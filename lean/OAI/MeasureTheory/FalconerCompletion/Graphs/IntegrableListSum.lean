import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.SpatialAngularKernelMeasurable
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped ComplexConjugate

lemma integrable_list_sumND {Q Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (L : List Q) (F : Q → Z → ℂ)
    (hi : ∀ i ∈ L, Integrable (F i) μ) :
    Integrable (fun z => (L.map (fun i => F i z)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.mem_cons,forall_eq_or_imp] at hi
    simp only [List.map_cons,List.sum_cons]
    exact hi.1.add (ih hi.2)

lemma integral_list_sumND {Q Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (L : List Q) (F : Q → Z → ℂ)
    (hi : ∀ i ∈ L, Integrable (F i) μ) :
    (∫ z, (L.map (fun i => F i z)).sum ∂μ) = (L.map (fun i => ∫ z, F i z ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.mem_cons,forall_eq_or_imp] at hi
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add hi.1 (integrable_list_sumND μ L F hi.2), ih hi.2]

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

lemma spatial_annulus_pair_boundND (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (j : ℕ) (scale : ℝ) (z : V × V) :
    ‖SpatialFourierND.spatialAnnulusKernel d δ K hδ hK j (scale⁻¹ • (z.1-z.2))‖ ≤
      SpatialFourierND.spatialFourierCost d δ K hδ hK j := by
  rw [← SpatialFourierND.spatialFourierSeparation d δ K hδ hK j scale z.1 z.2]
  apply le_trans (norm_integral_le_integral_norm _)
  simp only [norm_mul,SpatialFourierND.spatialFourierPhase_norm,Complex.norm_conj,mul_one]
  exact le_rfl

lemma spatial_angular_term_integrableND (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (j : ℕ) (scale : ℝ) (σ : Measure V) (ν : Measure (V × V))
    [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) :
    Integrable (fun z : V × V =>
      SpatialFourierND.spatialAnnulusKernel d δ K hδ hK j (scale⁻¹ • (z.1-z.2)) *
        (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w) ∂σ)) ν := by
  have hk : Measurable (fun z : V × V =>
      SpatialFourierND.spatialAnnulusKernel d δ K hδ hK j (scale⁻¹ • (z.1-z.2))) :=
    (SpatialFourierND.spatialAnnulusKernel_smooth d δ K hδ hK j).continuous.measurable.comp
      (by fun_prop)
  apply Integrable.of_bound (hk.mul (spatial_angular_kernel_measurableND σ r hψ hb hc)).aestronglyMeasurable
    (SpatialFourierND.spatialFourierCost d δ K hδ hK j*(P*B*C*σ.real univ))
  filter_upwards with z
  simp only [Pi.mul_apply,norm_mul]
  exact mul_le_mul (spatial_annulus_pair_boundND δ K hδ hK j scale z)
    (spatial_angular_kernel_boundND σ r ψ b c hP hB hC z) (norm_nonneg _)
      (SpatialFourierND.spatialFourierCost_nonneg d δ K hδ hK j)

theorem finite_spatial_angular_factorizationND {Q : Type*} (L : List Q)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) (j : ℕ) (scale : ℝ)
    (σ ρ ν : Measure V) [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set V) (M N r : ℝ) (a : Q → ℂ) {ψ : V → ℂ}
    {b c : Q → V → V → ℂ} (hψ : Measurable ψ)
    (hb : ∀ i ∈ L, Measurable (Function.uncurry (b i)))
    (hc : ∀ i ∈ L, Measurable (Function.uncurry (c i))) {P : ℝ} {B C : Q → ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ i ∈ L, ∀ x w, ‖b i x w‖ ≤ B i)
    (hC : ∀ i ∈ L, ∀ y w, ‖c i y w‖ ≤ C i) :
    ((M*N)⁻¹:ℝ) • (∫ z : V × V,
      (L.map (fun i => a i*(SpatialFourierND.spatialAnnulusKernel d δ K hδ hK j
        (scale⁻¹ • (z.1-z.2)) * (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
          b i z.1 w*conj (c i z.2 w) ∂σ)))).sum ∂(ρ.restrict X).prod (ν.restrict Y)) =
      (L.map (fun i => a i*(∫ ξ, SpatialFourierND.spatialFourierCoeff d δ K hδ hK j ξ *
        ∫ w, ψ w*sourceAngularTransformND ρ X M
          (fun x w => SpatialFourierND.spatialFourierPhase d scale ξ x*b i x w) r w *
          conj (sourceAngularTransformND ν Y N
            (fun y w => SpatialFourierND.spatialFourierPhase d scale ξ y*c i y w) r w) ∂σ))).sum := by
  rw [integral_list_sumND _ L _ (fun i hi =>
    (spatial_angular_term_integrableND δ K hδ hK j scale σ _ r hψ (hb i hi) (hc i hi)
      hP (hB i hi) (hC i hi)).const_mul (a i))]
  simp only [integral_const_mul,Complex.real_smul,← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [mul_left_comm]
  congr 1
  exact spatial_angular_factorizationND δ K hδ hK j scale σ ρ ν X Y M N r
    hψ (hb i hi) (hc i hi) hP (hB i hi) (hC i hi)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
