import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularTransform
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePlaneWaveSub2

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_sub (r : ℝ) (x y w : V) :
    spherePlaneWaveND r (x-y) w = spherePlaneWaveND r x w * conj (spherePlaneWaveND r y w) := by
  unfold spherePlaneWaveND
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [inner_sub_right,Complex.ofReal_sub,map_mul,Complex.conj_I,Complex.conj_ofReal]
  ring

lemma angular_pair_joint_integrableND (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) :
    Integrable (fun z : V × (V × V) => ψ z.1 * spherePlaneWaveND r (z.2.1-z.2.2) z.1 *
      b z.2.1 z.1 * conj (c z.2.2 z.1)) (σ.prod (ρ.prod ν)) := by
  have hB₀ : 0 ≤ B := (norm_nonneg (b 0 0)).trans (hB 0 0)
  have hP₀ : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hm : Measurable (fun z : V × (V × V) => ψ z.1 * spherePlaneWaveND r (z.2.1-z.2.2) z.1 *
      b z.2.1 z.1 * conj (c z.2.2 z.1)) := by
    exact (((hψ.comp measurable_fst).mul
      (by unfold spherePlaneWaveND; fun_prop)).mul
        (hb.comp (measurable_snd.fst.prodMk measurable_fst))).mul
          (Complex.continuous_conj.measurable.comp
            (hc.comp (measurable_snd.snd.prodMk measurable_fst)))
  apply Integrable.of_bound hm.aestronglyMeasurable (P*B*C)
  filter_upwards with z
  simp only [norm_mul,spherePlaneWaveND_norm,Complex.norm_conj,mul_one]
  exact mul_le_mul (mul_le_mul (hP z.1) (hB z.2.1 z.1) (norm_nonneg _) hP₀)
    (hC z.2.2 z.1) (norm_nonneg _) (mul_nonneg hP₀ hB₀)

theorem angular_pair_factorizationND (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set V) (M N r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) :
    ((M*N)⁻¹:ℝ) •
      (∫ z : V × V, (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
        b z.1 w*conj (c z.2 w) ∂σ) ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ∫ w, ψ w*sourceAngularTransformND ρ X M b r w *
        conj (sourceAngularTransformND ν Y N c r w) ∂σ := by
  have hs := integral_integral_swap (f := fun w (z : V × V) =>
    ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w))
    (angular_pair_joint_integrableND σ (ρ.restrict X) (ν.restrict Y) r hψ hb hc hP hB hC)
  have hi (w : V) :
      (∫ z : V × V, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w)
        ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ψ w*(∫ x in X, spherePlaneWaveND r x w*b x w ∂ρ) *
        conj (∫ y in Y, spherePlaneWaveND r y w*c y w ∂ν) := by
    simp_rw [spherePlaneWaveND_sub]
    have he : (fun z : V × V => ψ w*(spherePlaneWaveND r z.1 w*conj (spherePlaneWaveND r z.2 w))*
        b z.1 w*conj (c z.2 w)) =
        fun z => ψ w*((spherePlaneWaveND r z.1 w*b z.1 w)*
          conj (spherePlaneWaveND r z.2 w*c z.2 w)) := by
      funext z
      simp only [map_mul]
      ring
    rw [he,integral_const_mul,
      integral_prod_mul (fun x => spherePlaneWaveND r x w*b x w)
        (fun y => conj (spherePlaneWaveND r y w*c y w)),integral_conj]
    ring
  rw [← hs]
  simp_rw [hi]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  simp only [sourceAngularTransformND,Complex.real_smul,map_mul,Complex.conj_ofReal,
    mul_inv_rev,Complex.ofReal_mul]
  ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
