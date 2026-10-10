import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarKernelRegionPartition
import OAI.MeasureTheory.FalconerCompletion.Measures.EuclideanFarNoncomparableIntegrated
import OAI.MeasureTheory.FalconerCompletion.Recursion.FarDepthRegimeEventually

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real
open scoped ContDiff ComplexConjugate Topology

theorem euclidean_source_noncomparable_regionND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (err T D : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
          (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))))
        (a v ma : ℝ) (L k : ℕ)
        (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ),
      let η := ((ρ.prod ρ).prod (κ.prod κ)).restrict (((X×ˢX)×ˢ(Y×ˢY))∩S)
      let A := shellEffectiveScaleND L R σ
      v-a≤N → a≤k → (k:ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
      (ρ X).toReal≤R^(-ma+err) → (κ Y).toReal≤R^(-ma+err) →
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      (∀ᵐ z ∂η,
        (2:ℝ)^(-(k:ℝ))/4≤ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
        2*min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)≤ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
        ContDiff ℝ ∞ (b z.1) ∧ ContDiff ℝ ∞ (c z.2) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z.1) w‖≤C*A^j) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c z.2) w‖≤C*A^j)) →
      Integrable (euclideanFarKernelND Ψ v b c) η ∧
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*‖∫ z, euclideanFarKernelND Ψ v b c z ∂η‖≤R^(-T) := by
  obtain ⟨J,hJ⟩ := euclidean_far_noncomparable_integratedND (n := n) hΨ hs C hC hσ hσ 0 (T+(n+1:ℝ)+4*err)
  refine ⟨J,?_⟩
  filter_upwards [hJ,far_source_point_regime_eventuallyND hσ hσ₁ D,eventually_gt_atTop (0:ℝ)] with R hJ hpoint hR
  intro N hN hRN ρ κ _ _ X Y S a v ma L k b c η A hav hak hdepth hu₁ hu₂ hmb hmc hdata
  have hreg := hpoint N L k a v ((2:ℝ)^(-(k:ℝ))/4) hRN hak hav hdepth le_rfl
  have hdata' : ∀ᵐ z ∂η,
      R^σ≤(2:ℝ)^v*max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
      A^2/((2:ℝ)^v*max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2))≤R^(-σ) ∧
      2*min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)≤ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
      ContDiff ℝ ∞ (b z.1) ∧ ContDiff ℝ ∞ (c z.2) ∧
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z.1) w‖≤C*A^j) ∧
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c z.2) w‖≤C*A^j) := by
    filter_upwards [hdata] with z hz
    have hr := hpoint N L k a v (max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)) hRN hak hav hdepth hz.1
    exact ⟨hr.2.2.1,hr.2.2.2,hz.2⟩
  have hi : Integrable (euclideanFarKernelND Ψ v b c) η := by
    apply euclideanFarKernelND_integrable hΨ.continuous hs v b c hmb hmc _ hC
    filter_upwards [hdata] with z hz
    constructor
    · intro w hw
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hz.2.2.2.2.1 0 (by omega) w hw
    · intro w hw
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hz.2.2.2.2.2 0 (by omega) w hw
  refine ⟨hi,?_⟩
  have ht := hJ η b c A v hreg.1 hreg.2.1 hdata'
  simp only [Real.rpow_zero,one_mul] at ht
  change ‖∫ z, euclideanFarKernelND Ψ v b c z ∂η‖≤η.real univ*R^(-(T+(n+1:ℝ)+4*err)) at ht
  have hm : η.real univ≤(ρ X).toReal^2*(κ Y).toReal^2 := by
    change ((((ρ.prod ρ).prod (κ.prod κ)).restrict _ Set.univ).toReal)≤_
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ (((ρ.prod ρ).prod (κ.prod κ)) ((X×ˢX)×ˢ(Y×ˢY))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
      _ = _ := by simp only [Measure.prod_prod,ENNReal.toReal_mul]; ring
  have hmass := far_actual_error_normalizationND N hN hav ρ κ X Y
    (by simpa only [← hRN] using hu₁) (by simpa only [← hRN] using hu₂)
  simp only [← hRN,Nat.cast_add,Nat.cast_one] at hmass
  let F := (2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4
  have hF : 0≤F := by dsimp [F]; positivity
  calc
    _ ≤ F*(η.real univ*R^(-(T+(n+1:ℝ)+4*err))) := mul_le_mul_of_nonneg_left ht hF
    _ ≤ F*(((ρ X).toReal^2*(κ Y).toReal^2)*R^(-(T+(n+1:ℝ)+4*err))) := by gcongr
    _ = (F*(ρ X).toReal^2*(κ Y).toReal^2)*R^(-(T+(n+1:ℝ)+4*err)) := by ring
    _ ≤ R^((n+1:ℝ)+4*err)*R^(-(T+(n+1:ℝ)+4*err)) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology

section Metric
variable {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

theorem positiveDistance_supported_restrictND (μ ν : Measure (V×V))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : Set (V×V))
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (S : Set ((V×V)×(V×V))) (hS : MeasurableSet S)
    (d : ℕ) (v a M C ε : ℝ) (hM : 0<M) (hC : 0≤C) (hε : 0≤ε)
    (F : (V×V)×(V×V) → ℂ)
    (hF : ∀ᵐ z ∂(μ.prod ν).restrict S,
      ‖F z‖≤(P×ˢQ).indicator (fun z => C*distanceCollisionKernelND v z) z+ε) :
    ‖∫ z, F z ∂(μ.prod ν).restrict S‖ ≤
      C*(binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
        max (positiveDistanceCountND (μ.restrict P) d v a M).toReal
          (positiveDistanceCountND (ν.restrict Q) d v a M).toReal)+
      (μ.prod ν).real univ*ε := by
  classical
  have hh := positiveDistance_supported_integralND μ ν P Q hP hQ d v a M C ε
    hM hC (S.indicator F) (by
      filter_upwards [(ae_restrict_iff' hS).mp hF] with z hz
      by_cases hzS : z∈S
      · simpa only [Set.indicator_of_mem hzS] using hz hzS
      · rw [Set.indicator_of_notMem hzS,norm_zero]
        exact add_nonneg (Set.indicator_nonneg (fun z _ =>
          mul_nonneg hC (distanceCollisionKernelND_nonneg v z)) z) hε)
  rwa [integral_indicator hS] at hh

end Metric
end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology
attribute [local instance] Classical.propDecidable

theorem euclidean_far_restrictedND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      ∀ [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (v a M A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → 0<M → 1≤A → A≤R^2 →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ᵐ x ∂μ, (2:ℝ)^(-a)/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ᵐ x ∂ν, (2:ℝ)^(-a)/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      R^B*‖∫ x, (∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2))) ∂(μ.prod ν).restrict S‖ ≤
        (R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a)))*
          (binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
            max (positiveDistanceCountND (μ.restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M).toReal
              (positiveDistanceCountND (ν.restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M).toReal)+
        (μ.prod ν).real univ*R^(-T) := by
  obtain ⟨J,H,hH,hkernel⟩ := sphere_supported_rapid_euclideanND (n := n) hΨ hs C hC hθ B T
  refine ⟨J,H*4^n,by positivity,?_⟩
  filter_upwards [hkernel,eventually_ge_atTop (1:ℝ)] with R hkernel hR
  intro μ ν _ _ v a M A b c U W S hS hM hA hAup hP hQ hb hc
  have hRp : 0<R := by linarith
  let P := {x | euclideanPairDirectionND x∈U x}
  let Q := {x | euclideanPairDirectionND x∈W x}
  let G := fun x : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) × (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) =>
    ∫ u : ℝ, (Ψ u:ℂ)*
      sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
        conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2))
  have hpoint : ∀ᵐ x ∂μ.prod ν, ‖R^B • G x‖≤
      (P×ˢQ).indicator (fun x => (R^B*(H*4^n)*(2:ℝ)^(-(n:ℝ)*(v-a)))*distanceCollisionKernelND v x) x+R^(-T) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,Measure.quasiMeasurePreserving_snd.ae hc] with x hx hy
    obtain ⟨hd₁,hb₁,hU,hbs,hr₁,hbd⟩ := hx
    obtain ⟨hd₂,hc₂,hW,hcs,hr₂,hcd⟩ := hy
    have hp : 0<(2:ℝ)^(-a)/4 := by positivity
    have hp₁ : 0<dist x.1.1 x.1.2 := hp.trans_le hd₁
    have hp₂ : 0<dist x.2.1 x.2.2 := hp.trans_le hd₂
    have hh := hkernel (U x.1) (W x.2) (b x.1) (c x.2)
      (euclideanPairDirectionND x.1) (euclideanPairDirectionND x.2) A
      ((2:ℝ)^v*dist x.1.1 x.1.2) ((2:ℝ)^v*dist x.2.1 x.2.2)
      hb₁ hc₂ hU hW hbs hcs (euclideanPairDirectionND_norm _ hp₁) (euclideanPairDirectionND_norm _ hp₂)
      hA hAup (by positivity) (by positivity) hr₁ hr₂ hbd hcd
    rw [norm_smul_of_nonneg (Real.rpow_nonneg hRp.le B)]
    apply hh.trans
    apply add_le_add _ le_rfl
    by_cases hg : x∈P×ˢQ
    · have hg' : euclideanPairDirectionND x.1∈U x.1 ∧ euclideanPairDirectionND x.2∈W x.2 := hg
      rw [ite_eq_left hg',Set.indicator_of_mem hg]
      have hl := mul_le_mul_of_nonneg_left
        (far_original_length_kernelND n v a (dist x.1.1 x.1.2) (dist x.2.1 x.2.2) H hH hd₁ hd₂)
        (Real.rpow_nonneg hRp.le B)
      simpa only [distanceCollisionKernelND,div_eq_mul_inv,mul_one,one_mul,mul_assoc] using hl
    · have hg' : ¬(euclideanPairDirectionND x.1∈U x.1 ∧ euclideanPairDirectionND x.2∈W x.2) := hg
      rw [ite_eq_right hg',Set.indicator_of_notMem hg,mul_zero]
  have hh := positiveDistance_supported_restrictND μ ν P Q hP hQ S hS (n+1) v a M
    (R^B*(H*4^n)*(2:ℝ)^(-(n:ℝ)*(v-a))) (R^(-T)) hM (by positivity) (by positivity)
    (fun x => R^B • G x) (ae_restrict_of_ae hpoint)
  rw [integral_smul,norm_smul_of_nonneg (Real.rpow_nonneg hRp.le B)] at hh
  exact hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem euclidean_far_restricted_sumND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v M A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → 0<M → 1≤A → A≤R^2 →
      (∀ p∈P, ambientGridCell a p.1⊆X ∧ ambientGridCell a p.2⊆X) →
      (∀ q∈Q, ambientGridCell a q.1⊆Y ∧ ambientGridCell a q.2⊆Y) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ a p,
        (2:ℝ)^(-(a:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ a q,
        (2:ℝ)^(-(a:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      R^B*‖∑ pq∈P.product Q, ∫ x, (∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2)))
        ∂((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).restrict S‖ ≤
        (R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a)))*
          (binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
            ((P.product Q).card:ℝ)*(farChildMaximumND ρ κ a P Q v M U W).toReal)+
        (ρ X).toReal^2*(κ Y).toReal^2*R^(-T) := by
  obtain ⟨J,H,hH,hint⟩ := euclidean_far_restrictedND (n := n) hΨ hs C hC hθ B T
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hint,eventually_gt_atTop (0:ℝ)] with R hint hR
  intro ρ κ _ _ a P Q X Y v M A b c U W S hS hM hA hAup hPx hQy hU hW hb hc
  let D := (farChildMaximumND ρ κ a P Q v M U W).toReal
  have hD := farChildMaximumND_ne_top ρ κ a P Q v M U W
  let L := R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a))*(binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a))))
  have hL : 0≤L := by dsimp [L]; positivity
  let G := fun x : ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) =>
    ∫ u : ℝ, (Ψ u:ℂ)*
      sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
        conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2))
  have hpq (p) (hp : p∈P) (q) (hq : q∈Q) :
      R^B*‖∫ x, G x ∂((gridPairMeasureND ρ a p).prod (gridPairMeasureND κ a q)).restrict S‖ ≤
      L*D+((gridPairMeasureND ρ a p).prod (gridPairMeasureND κ a q)).real univ*R^(-T) := by
    have hh := hint (gridPairMeasureND ρ a p) (gridPairMeasureND κ a q)
      v a M A b c U W S hS hM hA hAup hU hW (hb p hp) (hc q hq)
    apply hh.trans
    apply add_le_add _ le_rfl
    have hm : max
        (positiveDistanceCountND ((gridPairMeasureND ρ a p).restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M).toReal
        (positiveDistanceCountND ((gridPairMeasureND κ a q).restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M).toReal ≤ D := by
      apply max_le
      · apply ENNReal.toReal_mono hD
        unfold farChildMaximumND
        apply le_sup_of_le_left
        exact Finset.le_sup (f := fun p => positiveDistanceCountND
          ((gridPairMeasureND ρ a p).restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M) hp
      · apply ENNReal.toReal_mono hD
        unfold farChildMaximumND
        apply le_sup_of_le_right
        exact Finset.le_sup (f := fun q => positiveDistanceCountND
          ((gridPairMeasureND κ a q).restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M) hq
    simpa only [L,mul_assoc] using mul_le_mul_of_nonneg_left hm hL
  calc
    _ ≤ R^B*∑ pq∈P.product Q, ‖∫ x, G x ∂((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).restrict S‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hR.le _)
    _ = ∑ pq∈P.product Q, R^B*‖∫ x, G x ∂((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).restrict S‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ pq∈P.product Q, (L*D+((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).real univ*R^(-T)) := by
      apply Finset.sum_le_sum
      intro pq hpq'
      exact hpq pq.1 (Finset.mem_product.mp hpq').1 pq.2 (Finset.mem_product.mp hpq').2
    _ = ((P.product Q).card:ℝ)*(L*D)+
        (∑ pq∈P.product Q, ((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).real univ)*R^(-T) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_mul]
    _ ≤ ((P.product Q).card:ℝ)*(L*D)+(ρ X).toReal^2*(κ Y).toReal^2*R^(-T) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (gridPairMeasureND_quadruple_mass ρ κ a P Q X Y hPx hQy) (show 0≤R^(-T) by positivity))
    _ = _ := by dsimp [L,D]; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
