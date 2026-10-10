import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Differentiability
import OAI.Geometry.IntegralFillings.Charts.Scalar

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma exists_jacobian_bound {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∃ B : ℝ, ∀ᵐ z ∂volume.restrict C.domain, ‖C.jacobian π z‖ ≤ B := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  choose K hK using hπ
  let R : ℝ := ∑ i, (K i * L : ℝ≥0)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact
    (Icc (fun (_ _ : Fin k) => -R) (fun _ _ => R))).exists_bound_of_continuousOn
      continuous_id.matrix_det.continuousOn
  refine ⟨B, ?_⟩
  have hae : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ ≤ (K i * L : ℝ≥0) :=
    ae_all_iff.mpr fun i => ae_norm_fderivWithin_le volume C.borel
      (C.scalar_lipschitzOn hφ (hK i))
  filter_upwards [hae] with z hz
  apply hB
  have hentry (i j : Fin k) :
      |(fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1)| ≤ R := by
    calc |(fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1)| ≤
        ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ := by
          simpa using (fderivWithin ℝ (C.scalar (π i)) C.domain z).le_opNorm
            (EuclideanSpace.single j 1)
      _ ≤ (K i * L : ℝ≥0) := hz i
      _ ≤ R := Finset.single_le_sum (fun i _ => NNReal.coe_nonneg (K i * L)) (Finset.mem_univ i)
  exact ⟨fun i j => (abs_le.mp (hentry i j)).1,
    fun i j => (abs_le.mp (hentry i j)).2⟩

lemma integrable_action_integrand {b : X → ℝ} {π : Fin k → X → ℝ}
    (hb : BoundedLip b) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z * C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨K, hK⟩ := hb.1
  obtain ⟨M, hM⟩ := hb.2
  have hbint : Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
      (volume.restrict C.domain) := by
    apply C.integrable.mul_bdd (C.measurable_scalar hK).aestronglyMeasurable
    filter_upwards [ae_restrict_mem C.borel] with z hz
    simpa [C.scalar_eq hz, Real.norm_eq_abs] using hM (C.param ⟨z, hz⟩)
  obtain ⟨B, hB⟩ := C.exists_jacobian_bound hπ
  exact hbint.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

lemma jacobian_update (π : Fin k → X → ℝ) (i : Fin k) (f : X → ℝ) (z : Euc k) :
    C.jacobian (Function.update π i f) z =
      (Matrix.updateRow
        (Matrix.of fun a j => fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1)) i
        (fun j => fderivWithin ℝ (C.scalar f) C.domain z (EuclideanSpace.single j 1))).det := by
  unfold jacobian
  congr 1
  funext a j
  by_cases ha : a = i
  · subst a
    simp
  · simp [ha]

lemma ae_jacobian_update_mul (π : Fin k → X → ℝ) (i : Fin k)
    {f g : X → ℝ} {K J : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith J g) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => f x * g x)) z =
        C.scalar f z * C.jacobian (Function.update π i g) z +
        C.scalar g z * C.jacobian (Function.update π i f) z := by
  filter_upwards [C.ae_fderivWithin_scalar_mul hf hg] with z hz
  rw [C.jacobian_update, C.jacobian_update, C.jacobian_update, hz]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  have heq : (fun j => C.scalar f z * fderivWithin ℝ (C.scalar g) C.domain z
        (EuclideanSpace.single j 1) + C.scalar g z * fderivWithin ℝ (C.scalar f) C.domain z
        (EuclideanSpace.single j 1)) =
      C.scalar f z • (fun j => fderivWithin ℝ (C.scalar g) C.domain z
        (EuclideanSpace.single j 1)) +
      C.scalar g z • (fun j => fderivWithin ℝ (C.scalar f) C.domain z
        (EuclideanSpace.single j 1)) := rfl
  rw [heq, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]

lemma action_update_mul {b f g : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (hg : BoundedLip g) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k) :
    C.action b (Function.update π i (fun x => f x * g x)) =
      C.action (fun x => b x * f x) (Function.update π i g) +
      C.action (fun x => b x * g x) (Function.update π i f) := by
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  have hadm₁ : Admissible b (Function.update π i (fun x => f x * g x)) :=
    ⟨hb, hup (BoundedLip.mul hf hg)⟩
  have hadm₂ : Admissible (fun x => b x * f x) (Function.update π i g) :=
    ⟨BoundedLip.mul hb hf, hup hg⟩
  have hadm₃ : Admissible (fun x => b x * g x) (Function.update π i f) :=
    ⟨BoundedLip.mul hb hg, hup hf⟩
  simp only [action, ite_eq_left hadm₁, ite_eq_left hadm₂, ite_eq_left hadm₃]
  rw [← integral_add (C.integrable_action_integrand hadm₂.1 hadm₂.2)
    (C.integrable_action_integrand hadm₃.1 hadm₃.2)]
  apply integral_congr_ae
  filter_upwards [C.ae_jacobian_update_mul π i hf.1.choose_spec hg.1.choose_spec] with z hz
  rw [hz, C.scalar_mul, C.scalar_mul]
  simp only [Pi.mul_apply]
  ring

end IntegerChart
end SharpIntegralFillings
end

end OAI
