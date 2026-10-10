import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.BinKernel
import OAI.MeasureTheory.FalconerCompletion.Estimates.FarScaledLength
import OAI.MeasureTheory.FalconerCompletion.Graphs.DiagonalBinMassLe
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereSupportedRapid

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Attempt4FarGrid
open scoped ENNReal
section Metric
variable {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

noncomputable def distanceCollisionKernelND (v : ℝ) (z : (V×V)×(V×V)) : ℝ :=
  1/(1+(2:ℝ)^v*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
lemma distanceCollisionKernelND_nonneg (v : ℝ) (z : (V×V)×(V×V)) :
    0≤distanceCollisionKernelND v z := by unfold distanceCollisionKernelND; positivity

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
lemma distanceCollisionKernelND_le_one (v : ℝ) (z : (V×V)×(V×V)) :
    distanceCollisionKernelND v z≤1 := by
  have hp : 0≤(2:ℝ)^v*|dist z.1.1 z.1.2-dist z.2.1 z.2.2| := by positivity
  unfold distanceCollisionKernelND
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma distanceCollisionKernelND_measurable (v : ℝ) :
    Measurable (distanceCollisionKernelND (V := V) v) := by
  unfold distanceCollisionKernelND
  fun_prop

lemma distanceCollisionKernelND_integrable (v : ℝ) (μ : Measure ((V×V)×(V×V)))
    [IsFiniteMeasure μ] : Integrable (distanceCollisionKernelND v) μ := by
  apply (integrable_const (1:ℝ)).mono' (distanceCollisionKernelND_measurable v).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (distanceCollisionKernelND_nonneg v z)]
  exact distanceCollisionKernelND_le_one v z

theorem positiveDistance_kernel_realND (μ ν : Measure (V×V))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (d : ℕ) (v a M : ℝ) (hM : 0<M) :
    (∫ z, distanceCollisionKernelND v z ∂μ.prod ν) ≤
      binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
        max (positiveDistanceCountND μ d v a M).toReal (positiveDistanceCountND ν d v a M).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (distanceCollisionKernelND_nonneg v))
    (distanceCollisionKernelND_measurable v).aestronglyMeasurable]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top binKernelConstant_ne_top ENNReal.ofReal_ne_top)
      (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (positiveDistanceCountND_ne_top μ d v a M))
        (lt_top_iff_ne_top.mpr (positiveDistanceCountND_ne_top ν d v a M)))))
    (positiveDistance_kernel_maxND μ ν d v a M hM)
  simpa only [distanceCollisionKernelND,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0≤M^4*(2:ℝ)^(-(v-a)) by positivity),
    ENNReal.toReal_max (positiveDistanceCountND_ne_top μ d v a M)
      (positiveDistanceCountND_ne_top ν d v a M)] using h

theorem positiveDistance_supported_integralND (μ ν : Measure (V×V))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : Set (V×V))
    (hP : MeasurableSet P) (hQ : MeasurableSet Q) (d : ℕ) (v a M C ε : ℝ) (hM : 0<M) (hC : 0≤C)
    (F : (V×V)×(V×V) → ℂ)
    (hF : ∀ᵐ z ∂μ.prod ν, ‖F z‖≤(P×ˢQ).indicator (fun z => C*distanceCollisionKernelND v z) z+ε) :
    ‖∫ z, F z ∂μ.prod ν‖ ≤
      C*(binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
        max (positiveDistanceCountND (μ.restrict P) d v a M).toReal
          (positiveDistanceCountND (ν.restrict Q) d v a M).toReal)+
      (μ.prod ν).real univ*ε := by
  have hi := ((distanceCollisionKernelND_integrable v (μ.prod ν)).const_mul C).indicator (hP.prod hQ)
  apply (norm_integral_le_of_norm_le (hi.add (integrable_const ε))
    hF).trans
  simp only [Pi.add_apply]
  rw [integral_add hi (integrable_const ε),integral_indicator (hP.prod hQ),
    ← Measure.prod_restrict,integral_const_mul,integral_const,smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (positiveDistance_kernel_realND (μ.restrict P) (ν.restrict Q) d v a M hM) hC) le_rfl

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

noncomputable def farUnitDirectionND {n : ℕ} (x : SphereAmbientND n × SphereAmbientND n) :
    SphereAmbientND n := ‖x.1-x.2‖⁻¹ • (x.1-x.2)

lemma farUnitDirectionND_norm {n : ℕ} (x : SphereAmbientND n × SphereAmbientND n)
    (hx : 0<dist x.1 x.2) : ‖farUnitDirectionND x‖=1 := by
  rw [dist_eq_norm] at hx
  simp [farUnitDirectionND,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hx.ne']

theorem original_far_integratedND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (μ ν : Measure (SphereAmbientND n × SphereAmbientND n)),
      ∀ [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (v a M A : ℝ) (b c : (SphereAmbientND n × SphereAmbientND n) → SphereAmbientND n → ℂ)
        (U W : (SphereAmbientND n × SphereAmbientND n) → Set (SphereAmbientND n)),
      0<M → 1≤A → A≤R^2 →
      MeasurableSet {x | farUnitDirectionND x∈U x} →
      MeasurableSet {x | farUnitDirectionND x∈W x} →
      (∀ᵐ x ∂μ, (2:ℝ)^(-a)/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ᵐ x ∂ν, (2:ℝ)^(-a)/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      R^B*‖∫ x, (∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (farUnitDirectionND x.1) (b x.1)*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (farUnitDirectionND x.2) (c x.2))) ∂μ.prod ν‖ ≤
        (R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a)))*
          (binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
            max (positiveDistanceCountND (μ.restrict {x | farUnitDirectionND x∈U x}) (n+1) v a M).toReal
              (positiveDistanceCountND (ν.restrict {x | farUnitDirectionND x∈W x}) (n+1) v a M).toReal)+
        (μ.prod ν).real univ*R^(-T) := by
  obtain ⟨J,H,hH,hkernel⟩ := sphere_supported_rapidND (n := n) hΨ hs C hC hθ B T
  refine ⟨J,H*4^n,by positivity,?_⟩
  filter_upwards [hkernel,eventually_ge_atTop (1:ℝ)] with R hkernel hR
  intro μ ν _ _ v a M A b c U W hM hA hAup hP hQ hb hc
  have hRp : 0<R := by linarith
  let P := {x | farUnitDirectionND x∈U x}
  let Q := {x | farUnitDirectionND x∈W x}
  let G := fun x : (SphereAmbientND n × SphereAmbientND n) × (SphereAmbientND n × SphereAmbientND n) =>
    ∫ u : ℝ, (Ψ u:ℂ)*
      sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (farUnitDirectionND x.1) (b x.1)*
        conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (farUnitDirectionND x.2) (c x.2))
  have hpoint : ∀ᵐ x ∂μ.prod ν, ‖R^B • G x‖≤
      (P×ˢQ).indicator (fun x => (R^B*(H*4^n)*(2:ℝ)^(-(n:ℝ)*(v-a)))*distanceCollisionKernelND v x) x+R^(-T) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,Measure.quasiMeasurePreserving_snd.ae hc] with x hx hy
    obtain ⟨hd₁,hb₁,hU,hbs,hr₁,hbd⟩ := hx
    obtain ⟨hd₂,hc₂,hW,hcs,hr₂,hcd⟩ := hy
    have hp : 0<(2:ℝ)^(-a)/4 := by positivity
    have hp₁ : 0<dist x.1.1 x.1.2 := hp.trans_le hd₁
    have hp₂ : 0<dist x.2.1 x.2.2 := hp.trans_le hd₂
    have hh := hkernel (U x.1) (W x.2) (b x.1) (c x.2)
      (farUnitDirectionND x.1) (farUnitDirectionND x.2) A
      ((2:ℝ)^v*dist x.1.1 x.1.2) ((2:ℝ)^v*dist x.2.1 x.2.2)
      hb₁ hc₂ hU hW hbs hcs (farUnitDirectionND_norm _ hp₁) (farUnitDirectionND_norm _ hp₂)
      hA hAup (by positivity) (by positivity) hr₁ hr₂ hbd hcd
    rw [norm_smul_of_nonneg (Real.rpow_nonneg hRp.le B)]
    apply hh.trans
    apply add_le_add _ le_rfl
    by_cases hg : x∈P×ˢQ
    · have hg' : farUnitDirectionND x.1∈U x.1 ∧ farUnitDirectionND x.2∈W x.2 := hg
      rw [ite_eq_left hg',Set.indicator_of_mem hg]
      have hl := mul_le_mul_of_nonneg_left
        (far_original_length_kernelND n v a (dist x.1.1 x.1.2) (dist x.2.1 x.2.2) H hH hd₁ hd₂)
        (Real.rpow_nonneg hRp.le B)
      simpa only [distanceCollisionKernelND,div_eq_mul_inv,mul_one,one_mul,mul_assoc] using hl
    · have hg' : ¬(farUnitDirectionND x.1∈U x.1 ∧ farUnitDirectionND x.2∈W x.2) := hg
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
