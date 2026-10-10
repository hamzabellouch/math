import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.CubeGradient
import OAI.Analysis.CoulombRadii.FieldAnalysis.SpinConfigurationIntegral

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma determinant_one_body_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b, Integrable (fun x => (w x : ℂ)*(star (v a x)*v b x)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i))*‖determinantWave v x‖^2 ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℝ)*(∑ a, ∫ x, w x*‖v a x‖^2 ∂μ) := by
  have H := determinant_one_body_integral v (fun x => (w x : ℂ)) hv ho hw
  simp_rw [complex_star_mul_self] at H
  apply Complex.ofReal_injective
  push_cast
  simpa only [← Complex.ofReal_sum, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_natCast] using H

lemma slaterWave_one_body_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b, Integrable (fun x => (w x : ℂ)*(star (v a x)*v b x)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i))*‖slaterWave v x‖^2 ∂(Measure.pi fun _ => μ)) =
      ∑ a, ∫ x, w x*‖v a x‖^2 ∂μ := by
  have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have he (x : Fin n → A) : (∑ i, w (x i))*‖slaterWave v x‖^2 =
      (n.factorial : ℝ)⁻¹*((∑ i, w (x i))*‖determinantWave v x‖^2) := by
    simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le]
    ring
  simp_rw [he]
  rw [integral_const_mul, determinant_one_body_real v w hv ho hw,
    ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

lemma compact_coulomb_onebody_integrable (f u : Space → ℂ)
    (hf : Continuous f) (hu : Continuous u) (hC : HasCompactSupport f) (R : Space) :
    Integrable (fun x => (coulombKernel (x-R) : ℂ)*(star (f x)*u x)) := by
  have hF := hf.norm.mul hu.norm
  have hFC : HasCompactSupport (fun x => ‖f x‖*‖u x‖) := hC.norm.mul_right
  obtain ⟨M,hM⟩ := hFC.exists_bound_of_continuous hF
  have hI := coulomb_convolution_integrable (hF.integrable_of_hasCompactSupport hFC)
    hF.measurable (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun x => (le_abs_self _).trans (hM x)) (by norm_num : (0:ℝ)<1) R
  apply hI.mono' ?_ (ae_of_all _ (fun x => ?_))
  · exact (((coulombKernel_measurable.comp (measurable_id.sub_const R)).complex_ofReal).mul
      (hf.star.mul hu).measurable).aestronglyMeasurable
  · simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (coulombKernel_nonneg _)]
    exact le_of_eq (by rw [coulombKernel, coulombKernel, norm_sub_rev]; rfl)

lemma compact_attraction_cross_integrable {M : ℕ} (S : Nuclei M) (f u : Space → ℂ)
    (hf : Continuous f) (hu : Continuous u) (hC : HasCompactSupport f) :
    Integrable (fun x => (attraction S x : ℂ)*(star (f x)*u x)) := by
  have H := integrable_finsetSum Finset.univ (fun j _ =>
    (compact_coulomb_onebody_integrable f u hf hu hC (S.position j)).const_mul (S.charge j : ℂ))
  apply H.congr
  filter_upwards [] with x
  simp only [attraction, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]

lemma slaterState_nuclear {M n : ℕ} (S : Nuclei M) (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) :
    nuclearEnergy S (slaterState v hv hC) = ∫ x, attraction S x*slaterDensity v x := by
  have hV (a : Fin n) (s : Fin 2) : MemLp (fun x => v a x s) 2 volume :=
    (hv a s).continuous.memLp_of_hasCompactSupport (hC a s)
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  have hi (a b : Fin n) (s : Fin 2) := compact_attraction_cross_integrable S
    (fun x => v a x s) (fun x => v b x s) (hv a s).continuous (hv b s).continuous (hC a s)
  have hO (a b : Fin n) : (∫ x, star (flatSpinOrbital (v a) x)*flatSpinOrbital (v b) x
      ∂spinSpaceMeasure) = if a = b then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v a) (v b) (hV a) (hV b)]
    exact ho a b
  have hW (a b : Fin n) : Integrable (fun x => (attraction S (WithLp.toLp 2 x.2) : ℂ)*
      (star (flatSpinOrbital (v a) x)*flatSpinOrbital (v b) x)) spinSpaceMeasure :=
    integrable_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hi a b s))
  have H := slaterWave_one_body_real (fun a => flatSpinOrbital (v a))
    (fun x => attraction S (WithLp.toLp 2 x.2))
    (fun a => flatSpinOrbital_memLp (v a) (hV a)) hO hW
  rw [← slaterState_cubeState v hv hC] at H
  have he := spinConfiguration_integral
    (fun s x => (∑ i, attraction S (position x i))*‖(slaterState v hv hC).value s x‖^2)
    ((slaterState v hv hC).nuclear_integrable S)
  change (∫ x, (∑ i, attraction S (WithLp.toLp 2 (x i).2))*
    ‖cubeState (slaterState v hv hC) x‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) =
      nuclearEnergy S (slaterState v hv hC) at he
  rw [he] at H
  rw [H]
  have hr (a : Fin n) (s : Fin 2) : Integrable (fun x => attraction S x*‖v a x s‖^2) := by
    have ht := hi a a s
    simp_rw [complex_star_mul_self, ← Complex.ofReal_mul] at ht
    exact ht.re
  have he1 (a : Fin n) : (∫ x, attraction S (WithLp.toLp 2 x.2)*‖flatSpinOrbital (v a) x‖^2
      ∂spinSpaceMeasure) = ∑ s, ∫ x : Space, attraction S x*‖v a x s‖^2 := by
    unfold spinSpaceMeasure flatSpinOrbital
    rw [integral_finite_count_prod (μ := volume)
      (fun x : Fin 2 × (Fin 3 → ℝ) => attraction S (WithLp.toLp 2 x.2)*‖v a (WithLp.toLp 2 x.2) x.1‖^2)
      (fun s => hm.integrable_comp_of_integrable (hr a s))]
    apply Finset.sum_congr rfl
    intro s _
    exact hm.integral_comp' (fun x : Space => attraction S x*‖v a x s‖^2)
  simp_rw [he1]
  simp only [slaterDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun s _ => hr a s))]
  apply Finset.sum_congr rfl
  intro a _
  exact (integral_finsetSum _ (fun s _ => hr a s)).symm
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma slaterState_form_upper {M n : ℕ} (S : Nuclei M) (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) :
    form S (slaterState v hv hC) ≤
      (1/2:ℝ)*(∑ a, ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*slaterDensity v x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (slaterDensity v xy.1*slaterDensity v xy.2)) := by
  unfold form
  rw [slaterState_kinetic v hv hC ho, slaterState_nuclear S v hv hC ho]
  exact add_le_add_right (slaterState_pair_upper v hv hC ho) _

lemma energy_le_slater_trial {M n : ℕ} (S : Nuclei M) (hn : n ≠ 0)
    (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) :
    energy S n ≤ (1/2:ℝ)*(∑ a, ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*slaterDensity v x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (slaterDensity v xy.1*slaterDensity v xy.2)) :=
  (energy_le_form S hn (slaterState v hv hC)
    (slaterState_antisymmetric v hv hC) (slaterState_normalized v hv hC ho)).trans
      (slaterState_form_upper S v hv hC ho)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
