import Mathlib
import OAI.Probability.GaussianInformation.Kernel.GramVolume

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Support
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gramSchmidt_castSucc {q : ℕ} (f : Fin (q+1) → E) (j : Fin q) :
    gramSchmidt ℝ f j.castSucc = gramSchmidt ℝ (fun i => f i.castSucc) j := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    rw [gramSchmidt_real_def, gramSchmidt_real_def, Fin.sum_Iio_castSucc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih i (Finset.mem_Iio.mp hi)]

noncomputable def replicaPlane {q : ℕ} (b : E) (f : Fin q → E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' b (Submodule.span ℝ (range f))

lemma replicaPlane_nonempty {q : ℕ} (b : E) (f : Fin q → E) :
    (replicaPlane b f : Set E).Nonempty := by
  exact ⟨b, AffineSubspace.self_mem_mk' _ _⟩

lemma replicaPlane_finrank_le {q : ℕ} (b : E) (f : Fin q → E) :
    Module.finrank ℝ (replicaPlane b f).direction ≤ q := by
  unfold replicaPlane
  rw [AffineSubspace.direction_mk']
  simpa [Set.finrank] using (finrank_range_le_card (R := ℝ) f)

lemma lastPlane_infDist_le {q : ℕ} (b : E) (f : Fin (q+1) → E) :
    infDist (f (Fin.last q) + b) (replicaPlane b (fun i => f i.castSucc) : Set E) ≤
      ‖gramSchmidt ℝ f (Fin.last q)‖ := by
  have hset : f '' Iio (Fin.last q) = range (fun i : Fin q => f i.castSucc) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, i.isLt, rfl⟩
  have hm := gramSchmidt_residual_mem_span f (Fin.last q)
  rw [hset] at hm
  have hpoint : f (Fin.last q) - gramSchmidt ℝ f (Fin.last q) + b ∈
      replicaPlane b (fun i => f i.castSucc) := by
    apply AffineSubspace.mem_mk'.mpr
    simpa using hm
  convert infDist_le_dist_of_mem (x := f (Fin.last q)+b) hpoint using 1
  rw [dist_eq_norm]
  congr 1
  abel

noncomputable def gramInverseProduct {q : ℕ} (k : ℕ) (f : Fin q → E) : ℝ≥0∞ :=
  ∏ i, (ENNReal.ofReal ‖gramSchmidt ℝ f i‖)⁻¹ ^ k

lemma gramInverseProduct_succ {q : ℕ} (k : ℕ) (f : Fin (q+1) → E) :
    gramInverseProduct k f = gramInverseProduct k (fun i => f i.castSucc) *
      (ENNReal.ofReal ‖gramSchmidt ℝ f (Fin.last q)‖)⁻¹ ^ k := by
  unfold gramInverseProduct
  rw [Fin.prod_univ_castSucc]
  simp_rw [gramSchmidt_castSucc]

lemma measurable_gramInverseProduct {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (k : ℕ) :
    Measurable (gramInverseProduct (E := E) (q := q) k) := by
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gramSchmidt i).norm.ennreal_ofReal.inv.pow_const _

lemma lintegral_gramInverseProduct_le {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SigmaFinite μ] (a : α → E) (ha : Measurable a)
    (k p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ E, (V : Set E).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set E)))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (b : E) :
    (∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b)
      ∂Measure.pi (fun _ => μ)) ≤ M^q := by
  induction q with
  | zero => simp [gramInverseProduct]
  | succ q ih =>
    have hq' : q ≤ p := by omega
    have hmeas : Measurable (fun z : Fin (q+1) → α =>
        gramInverseProduct k (fun i => a (z i)-b)) :=
      (measurable_gramInverseProduct k).comp
        (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i)).sub measurable_const)
    rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (q+1) => μ) (Fin.last q)).symm).lintegral_map_equiv]
    rw [lintegral_prod_symm _ (by
      exact (hmeas.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => α)
        (Fin.last q)).symm.measurable).aemeasurable)]
    have hlast : ∀ (z : Fin q → α),
        (∫⁻ x, gramInverseProduct k (fun i => a (Fin.snoc (α := fun _ : Fin (q+1) => α) z x i)-b) ∂μ) ≤
          gramInverseProduct k (fun i => a (z i)-b) * M := by
      intro z
      let V := replicaPlane b (fun i => a (z i)-b)
      have hV := replicaPlane_nonempty b (fun i => a (z i)-b)
      have hr := (replicaPlane_finrank_le b (fun i => a (z i)-b)).trans hq'
      calc
        _ ≤ ∫⁻ x, gramInverseProduct k (fun i => a (z i)-b) *
            (ENNReal.ofReal (infDist (a x) (V : Set E)))⁻¹ ^ k ∂μ := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [gramInverseProduct_succ]
          simp only [Fin.snoc_castSucc]
          apply mul_le_mul_right
          apply pow_le_pow_left'
          apply ENNReal.inv_le_inv.mpr
          apply ENNReal.ofReal_le_ofReal
          simpa only [V, Fin.snoc_last, Fin.snoc_castSucc, sub_add_cancel] using
            (lastPlane_infDist_le b (fun i => a (Fin.snoc (α := fun _ : Fin (q+1) => α) z x i)-b))
        _ = gramInverseProduct k (fun i => a (z i)-b) *
            ∫⁻ x, (ENNReal.ofReal (infDist (a x) (V : Set E)))⁻¹ ^ k ∂μ := by
          exact lintegral_const_mul _ (by
            exact ((((continuous_infDist_pt (V : Set E)).measurable.comp ha).ennreal_ofReal.inv).pow_const k))
        _ ≤ gramInverseProduct k (fun i => a (z i)-b) * M := mul_le_mul_right (hcond V hV hr) _
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_last]
    calc
      _ ≤ ∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b) * M
          ∂Measure.pi (fun _ => μ) := lintegral_mono hlast
      _ = (∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b)
          ∂Measure.pi (fun _ => μ)) * M := by
        exact lintegral_mul_const _ ((measurable_gramInverseProduct k).comp
          (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i)).sub measurable_const))
      _ ≤ M^q * M := mul_le_mul_left (ih (by omega)) M
      _ = M^(q+1) := (pow_succ _ _).symm

lemma gramInverseProduct_eq_inverseVolume {q : ℕ} (k : ℕ) (f : Fin q → E) :
    gramInverseProduct k f = (ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ f).det))⁻¹ ^ k := by
  rw [sqrt_gram_det_eq_prod_gramSchmidt,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr ENNReal.ofReal_ne_top),
    ← Finset.prod_pow]
  rfl

lemma lintegral_replicaInverse_le {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SigmaFinite μ] (hμ : μ univ ≤ 1) (a : α → E) (ha : Measurable a)
    (k p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ E, (V : Set E).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set E)))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) :
    (∫⁻ z : Fin (q+1) → α, gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))
      ∂Measure.pi (fun _ => μ)) ≤ M^q := by
  have hmeas : Measurable (fun z : Fin (q+1) → α =>
      gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))) :=
    (measurable_gramInverseProduct k).comp
      (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i.succ)).sub
        (ha.comp (measurable_pi_apply 0)))
  rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (q+1) => μ) 0).symm).lintegral_map_equiv]
  rw [lintegral_prod _ (by
    exact (hmeas.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => α) 0).symm.measurable).aemeasurable)]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove]
  calc
    _ ≤ ∫⁻ x, M^q ∂μ := lintegral_mono fun x =>
      lintegral_gramInverseProduct_le μ a ha k p M hcond q hq (a x)
    _ = M^q * μ univ := lintegral_const _
    _ ≤ M^q * 1 := mul_le_mul_right hμ _
    _ = M^q := mul_one _

end Support

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

end Projection
end KernelPotential

end OAI
