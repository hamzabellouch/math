import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ProjectionMoments

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
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open Support _root_.OAI.KernelPotential.Geometry

lemma fixed_center_replicas {k q d : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (v : Fin q → EuclideanSpace ℝ (Fin d)) :
    (∫⁻ X, ∏ i, boxKernel η (projectVector X (v i)) 0 ∂gaussianRows k d) ≤
      gramInverseProduct k v := by
  classical
  let D := {X : Fin k → Fin d → ℝ | ∀ r i, |(rowMatrix v *ᵥ X r) i| ≤ η}
  have hD : MeasurableSet D := by
    dsimp only [D]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  have hpoint : ∀ X, (∏ i, boxKernel η (projectVector X (v i)) 0) ≤
      D.indicator (fun _ => boxScale k η ^ q) X := by
    intro X
    by_cases hX : X ∈ D
    · rw [indicator_of_mem hX]
      calc
        _ ≤ ∏ _i : Fin q, boxScale k η := Finset.prod_le_prod
          (fun _ _ => boxKernel_le η _ _)
        _ = _ := by simp
    · rw [indicator_of_notMem hX]
      change ¬ ∀ r i, |(rowMatrix v *ᵥ X r) i| ≤ η at hX
      push Not at hX
      obtain ⟨r,i,hi⟩ := hX
      apply le_of_eq
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_contra hh
      have hm := boxKernel_ne_zero_mem hh
      have hx := hm r
      simp only [Pi.zero_apply, zero_sub, abs_neg] at hx
      rw [projectVector_rowMatrix] at hx
      exact (not_le.mpr hi) hx
  calc
    _ ≤ ∫⁻ X, D.indicator (fun _ => boxScale k η ^ q) X ∂gaussianRows k d := lintegral_mono hpoint
    _ = boxScale k η ^ q * gaussianRows k d D := by rw [lintegral_indicator hD,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ boxScale k η ^ q * ((ENNReal.ofReal (Real.sqrt (rowMatrix v * (rowMatrix v)ᵀ).det))⁻¹^k *
        ENNReal.ofReal ((2*η)^(q*k))) := by
      apply mul_le_mul_right
      simpa only [gaussianRows,Fintype.card_fin] using
        gaussian_multirow_box_le_extended (ρ := Fin k) (by simpa using hk) (rowMatrix v) η hη
    _ = gramInverseProduct k v := by
      rw [rowMatrix_gram, ← gramInverseProduct_eq_inverseVolume]
      have hc : boxScale k η ^ q * ENNReal.ofReal ((2*η)^(q*k)) = 1 := by
        rw [Nat.mul_comm q k,pow_mul,ENNReal.ofReal_pow (by positivity),boxScale,
          ← mul_pow, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top,one_pow]
      calc
        _ = gramInverseProduct k v * (boxScale k η ^ q * ENNReal.ofReal ((2*η)^(q*k))) := by ac_rfl
        _ = _ := by rw [hc,mul_one]

lemma fixed_center_moment {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) [SigmaFinite μ] (a : α → EuclideanSpace ℝ (Fin d))
    (ha : Measurable a) (hk : 0 < k) (p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z,(ENNReal.ofReal (infDist (a z) (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (η : ℝ) (hη : 0 < η) :
    (∫⁻ X, (∫⁻ z,boxKernel η (projectVector X (a z)) 0 ∂μ)^q ∂gaussianRows k d) ≤ M^q := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun x : (Fin k → Fin d → ℝ) × α =>
      boxKernel η (projectVector x.1 (a x.2)) 0) :=
    (measurable_zero_kernel (k := k) (d := d) η).comp
      (f := fun x : (Fin k → Fin d → ℝ) × α => (x.1,a x.2))
      (measurable_fst.prodMk (ha.comp measurable_snd))
  have hrep := measurable_replicated (m := q) _ hm
  calc
    _ = ∫⁻ X, ∫⁻ z : Fin q → α, ∏ i,boxKernel η (projectVector X (a (z i))) 0
        ∂Measure.pi (fun _ => μ) ∂gaussianRows k d := by
      apply lintegral_congr
      intro X
      exact (lintegral_pi_product μ _ (hm.comp (measurable_const.prodMk measurable_id)) q).symm
    _ = ∫⁻ z : Fin q → α, ∫⁻ X, ∏ i,boxKernel η (projectVector X (a (z i))) 0
        ∂gaussianRows k d ∂Measure.pi (fun _ => μ) := lintegral_lintegral_swap hrep.aemeasurable
    _ ≤ ∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)) ∂Measure.pi (fun _ => μ) :=
      lintegral_mono (fun z => fixed_center_replicas hk η hη _)
    _ ≤ M^q := by
      simpa only [sub_zero] using lintegral_gramInverseProduct_le μ a ha k p M hcond q hq 0

lemma fresh_rows_kernel_le {k d : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ Z, boxKernel η (projectVector Z x) 0 ∂gaussianRows k d) ≤
      (ENNReal.ofReal ‖x‖)⁻¹^k := by
  have h := fixed_center_replicas hk η hη (fun _ : Fin 1 => x)
  have he : gramInverseProduct k (fun _ : Fin 1 => x) = (ENNReal.ofReal ‖x‖)⁻¹^k := by
    simp only [gramInverseProduct, Fin.prod_univ_one]
    rw [show (0 : Fin 1) = ⊥ from rfl, gramSchmidt_bot]
  simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, he] using h

noncomputable def mixedCubeAverage {k d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (η : ℝ) (X Z : Fin k → Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, boxKernel η (projectVector X x) 0 * boxKernel η (projectVector Z x) 0 ∂μ

lemma auxiliary_average_le {k d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [SigmaFinite μ] (hk : 0 < k) (η : ℝ) (hη : 0 < η) (X : Fin k → Fin d → ℝ) :
    (∫⁻ Z,mixedCubeAverage μ η X Z ∂gaussianRows k d) ≤
      ∫⁻ x,boxKernel η (projectVector X x) 0 * (ENNReal.ofReal ‖x‖)⁻¹^k ∂μ := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun x : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) =>
      boxKernel η (projectVector X x.2) 0 * boxKernel η (projectVector x.1 x.2) 0) :=
    ((measurable_zero_kernel (k := k) (d := d) η).comp
      (f := fun x : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) => (X,x.2))
      (measurable_const.prodMk measurable_snd)).mul
      (measurable_zero_kernel (k := k) (d := d) η)
  unfold mixedCubeAverage
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_mono
  intro x
  dsimp only
  have hmX : Measurable (fun Z : Fin k → Fin d → ℝ => boxKernel η (projectVector Z x) 0) :=
    (measurable_zero_kernel (k := k) (d := d) η).comp
      (f := fun Z : Fin k → Fin d → ℝ => (Z,x)) (measurable_id.prodMk measurable_const)
  rw [lintegral_const_mul _ hmX]
  exact mul_le_mul_right (fresh_rows_kernel_le hk η hη x) _

theorem mixed_fixed_origin_moment {k d n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite μ]
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hk : 0 < k) (hn : 2*k < n)
    (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ 2)
    (hballB : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^(2*k)))
    (hballD : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (D*r^n))
    (L : ℕ) (hDB : D ≤ B*2^L) (η : ℝ) (hη : 0 < η) :
    (∫⁻ X, (∫⁻ Z, mixedCubeAverage μ η X Z ∂gaussianRows k d)^k ∂gaussianRows k d) ≤
      ENNReal.ofReal ((9^(k-1)*3^n*2^(n+2*k+2))*B*((L:ℝ)+2))^k := by
  let w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖x‖)⁻¹^k
  have hw : Measurable w := measurable_norm.ennreal_ofReal.inv.pow_const _
  have hz : ∀ᵐ x ∂μ, ‖x‖ ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using ball_bound_zero_null μ (by omega : 0 < 2*k) hB hballB
  have : SigmaFinite (μ.withDensity w) := SigmaFinite.withDensity_of_ne_top (by
    filter_upwards [hz] with x hx
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by
      exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (norm_nonneg x) hx.symm)).ne')))
  let M : ℝ≥0∞ := ENNReal.ofReal ((9^(k-1)*3^n*2^(n+2*k+2))*B*((L:ℝ)+2))
  have hcond : ∀ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty → Module.finrank ℝ V.direction ≤ k-1 →
      (∫⁻ x,(ENNReal.ofReal (infDist x (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k
        ∂μ.withDensity w) ≤ M := by
    intro V hV hdim
    have hg : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
        (ENNReal.ofReal (infDist x (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k) :=
      (continuous_infDist_pt _).measurable.ennreal_ofReal.inv.pow_const _
    rw [lintegral_withDensity_eq_lintegral_mul μ hw hg]
    change (∫⁻ x, (ENNReal.ofReal ‖x‖)⁻¹^k *
      (ENNReal.ofReal (infDist x (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k ∂μ) ≤ M
    apply (mixed_integral_logarithmic μ hB hD hk hn hsupport hballB hballD V hV hdim L hDB).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : (9:ℝ)^(Module.finrank ℝ V.direction) ≤ 9^(k-1) :=
      pow_le_pow_right₀ (by norm_num) hdim
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity))
        (by positivity)) hB) (by positivity)
  calc
    _ ≤ ∫⁻ X, (∫⁻ x,boxKernel η (projectVector X x) 0 * w x ∂μ)^k ∂gaussianRows k d := by
      apply lintegral_mono
      intro X
      exact pow_le_pow_left' (auxiliary_average_le μ hk η hη X) k
    _ = ∫⁻ X,(∫⁻ x,boxKernel η (projectVector X x) 0 ∂μ.withDensity w)^k ∂gaussianRows k d := by
      apply lintegral_congr
      intro X
      congr 1
      have hg : Measurable (fun x : EuclideanSpace ℝ (Fin d) => boxKernel η (projectVector X x) 0) :=
        (measurable_zero_kernel (k := k) (d := d) η).comp
          (f := fun x : EuclideanSpace ℝ (Fin d) => (X,x)) (measurable_const.prodMk measurable_id)
      rw [lintegral_withDensity_eq_lintegral_mul μ hw hg]
      apply lintegral_congr
      intro x
      exact mul_comm _ _
    _ ≤ M^k := fixed_center_moment (μ.withDensity w) id measurable_id hk (k-1) M hcond k (by omega) η hη

end Projection

end KernelPotential

end OAI
