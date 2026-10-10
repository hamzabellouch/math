import OAI.Geometry.RCD.Heat.CompactKernelFactor
import OAI.Geometry.RCD.Coordinates.KernelBridgeNormalization

namespace OAI

/-! # Continuous intermediate densities from compact endpoint factors

The only composition identity is the actual integral of the two kernels.
For the heat kernel it is the already proved semigroup identity.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {A B X : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  [MetricSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure A) (ν : Measure B) (σ : Measure X)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite σ]

theorem continuous_kernel_bridge_probability (L : C(X × A, ℝ)) (R : C(X × B, ℝ))
    (K : C(A × B, ℝ)) (F : C(A, ℝ)) (G : C(B, ℝ))
    (hL : ∀ x a, 0 ≤ L (x,a)) (hR : ∀ x b, 0 ≤ R (x,b))
    (hF : ∀ a, 0 ≤ F a) (hG : ∀ b, 0 ≤ G b)
    (hint : ∀ a b, Integrable (fun x => L (x,a)*R (x,b)) σ)
    (hconv : ∀ a b, (∫ x, L (x,a)*R (x,b) ∂σ)=K (a,b))
    (hrow : ∀ a, F a*(∫ b, K (a,b)*G b ∂ν)=1) :
    IsProbabilityMeasure (σ.withDensity
      (fun x => ENNReal.ofReal (compactKernelFactor μ L F x * compactKernelFactor ν R G x))) := by
  have hK : ∀ a b, 0 ≤ K (a,b) := fun a b => by
    rw [← hconv a b]
    exact integral_nonneg fun x => mul_nonneg (hL x a) (hR x b)
  have hc : ∀ a b,
      (∫⁻ x, ENNReal.ofReal (L (x,a))*ENNReal.ofReal (R (x,b)) ∂σ)=
        ENNReal.ofReal (K (a,b)) := by
    intro a b
    rw [← hconv a b,ofReal_integral_eq_lintegral_ofReal (hint a b)
      (Eventually.of_forall fun x => mul_nonneg (hL x a) (hR x b))]
    exact lintegral_congr fun x => (ENNReal.ofReal_mul (hL x a)).symm
  have hr : ∀ a, ENNReal.ofReal (F a) *
      (∫⁻ b, ENNReal.ofReal (K (a,b))*ENNReal.ofReal (G b) ∂ν)=1 := by
    intro a
    have hi : Integrable (fun b => K (a,b)*G b) ν :=
      ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul G.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun b => mul_nonneg (hK a b) (hG b))
    simp_rw [ENNReal.ofReal_mul (hK a _)] at he
    rw [← he,← ENNReal.ofReal_mul (hF a),hrow,ENNReal.ofReal_one]
  have hp := kernel_bridge_probability μ ν σ
    (F := fun a => ENNReal.ofReal (F a)) (G := fun b => ENNReal.ofReal (G b))
    (L := fun z => ENNReal.ofReal (L (z.2,z.1)))
    (R := fun z => ENNReal.ofReal (R z)) (K := fun z => ENNReal.ofReal (K z))
    F.continuous.measurable.ennreal_ofReal
    G.continuous.measurable.ennreal_ofReal
    (L.continuous.measurable.comp measurable_swap).ennreal_ofReal
    R.continuous.measurable.ennreal_ofReal hc hr
  have heq : (fun x => ENNReal.ofReal (compactKernelFactor μ L F x * compactKernelFactor ν R G x)) =
      (fun x => (∫⁻ a, ENNReal.ofReal (F a)*ENNReal.ofReal (L (x,a)) ∂μ)*
        (∫⁻ b, ENNReal.ofReal (R (x,b))*ENNReal.ofReal (G b) ∂ν)) := by
    funext x
    have ha : 0 ≤ compactKernelFactor μ L F x :=
      integral_nonneg fun a => mul_nonneg (hL x a) (hF a)
    rw [ENNReal.ofReal_mul ha,compactKernelFactor_ofReal μ L F hL hF,
      compactKernelFactor_ofReal ν R G hR hG]
    congr 1
    exact lintegral_congr fun a => mul_comm _ _
  rw [heq]
  exact hp

end RegularPointCoordinates

end

end OAI
