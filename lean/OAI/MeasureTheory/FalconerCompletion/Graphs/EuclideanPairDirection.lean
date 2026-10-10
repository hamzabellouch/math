import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.DistanceCollisionKernel
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasureTransport

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology
attribute [local instance] Classical.propDecidable

noncomputable def euclideanPairDirectionND {n : ℕ} (x : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) :
    EuclideanSpace ℝ (Fin (n+1)) := ‖x.1-x.2‖⁻¹ • (x.1-x.2)

lemma euclideanPairDirectionND_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))
    (hx : 0<dist x.1 x.2) : ‖euclideanPairDirectionND x‖=1 := by
  rw [dist_eq_norm] at hx
  simp [euclideanPairDirectionND,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hx.ne']

theorem euclidean_far_integratedND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      ∀ [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (v a M A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      0<M → 1≤A → A≤R^2 →
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
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2))) ∂μ.prod ν‖ ≤
        (R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a)))*
          (binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
            max (positiveDistanceCountND (μ.restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M).toReal
              (positiveDistanceCountND (ν.restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M).toReal)+
        (μ.prod ν).real univ*R^(-T) := by
  obtain ⟨J,H,hH,hkernel⟩ := sphere_supported_rapid_euclideanND (n := n) hΨ hs C hC hθ B T
  refine ⟨J,H*4^n,by positivity,?_⟩
  filter_upwards [hkernel,eventually_ge_atTop (1:ℝ)] with R hkernel hR
  intro μ ν _ _ v a M A b c U W hM hA hAup hP hQ hb hc
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
  have hh := positiveDistance_supported_integralND μ ν P Q hP hQ (n+1) v a M
    (R^B*(H*4^n)*(2:ℝ)^(-(n:ℝ)*(v-a))) (R^(-T)) hM (by positivity)
    (fun x => R^B • G x) hpoint
  rw [integral_smul,norm_smul_of_nonneg (Real.rpow_nonneg hRp.le B)] at hh
  exact hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
