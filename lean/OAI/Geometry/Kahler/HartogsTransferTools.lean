import OAI.Geometry.Kahler.HartogsFrame

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

def liftBaseMap (C : Base → Base) (q : Ambient) : Ambient := (C q.1,q.2)

lemma liftBaseMap_analyticAt {C : Base → Base} {p : Ambient} (hC : AnalyticAt ℂ C p.1) :
    AnalyticAt ℂ (liftBaseMap C) p :=
  (hC.comp ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt p)).prod
    ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt p)

lemma fderiv_liftBaseMap {C : Base → Base} {p : Ambient} (hC : DifferentiableAt ℂ C p.1)
    (u : Ambient) : fderiv ℂ (liftBaseMap C) p u = (fderiv ℂ C p.1 u.1,u.2) := by
  have hh := (hC.hasFDerivAt.comp p (ContinuousLinearMap.fst ℂ Base ℂ).hasFDerivAt).prodMk
    (ContinuousLinearMap.snd ℂ Base ℂ).hasFDerivAt
  change HasFDerivAt (liftBaseMap C) _ p at hh
  rw [hh.fderiv]
  rfl

lemma baseHessian_value_comp {f : Base → ℝ} {C : Base → Base} {z : Base}
    (hf : ContDiffAt ℝ 2 f (C z)) (hC : AnalyticAt ℂ C z) (u v : Base) :
    (∑ i, ∑ j, baseHessian (f ∘ C) z i j * u i * star (v j)) =
      ∑ i, ∑ j, baseHessian f (C z) i j * (fderiv ℂ C z u) i * star ((fderiv ℂ C z v) j) := by
  have hfc : ContDiffAt ℝ 2 (f ∘ C) z := hf.comp z (hC.contDiffAt.restrict_scalars ℝ)
  have he := complexHessian_pullback
    (hf.comp (f := fun q : Ambient => q.1) (liftBaseMap C (z,0)) contDiffAt_fst)
    (liftBaseMap_analyticAt (p := (z,0)) hC)
  have hh := congrArg (fun A => hermitianValue A (u,0) (v,0)) he
  change hermitianValue (complexHessian (fun q : Ambient => (f ∘ C) q.1) (z,0)) (u,0) (v,0) = _ at hh
  erw [hermitianValue_lift_base hfc, hermitianValue_pullback,
    fderiv_liftBaseMap hC.differentiableAt, fderiv_liftBaseMap hC.differentiableAt,
    hermitianValue_lift_base hf] at hh
  exact hh

lemma chartWeight_contDiffAt {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) :
    ContDiffAt ℝ ∞ (φ ∘ centeredChart r U) 0 := by
  exact (hφ.contDiffAt (isOpen_ball.mem_nhds (centeredChart_zero_mem hr hr1 U))).comp 0
    ((centeredChart_analyticAt U (z := 0) (by simp)).contDiffAt.restrict_scalars ℝ)

lemma chartControl_psh {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {c C : ℝ} (hc : 0 ≤ c) (hctl : ChartControl φ c C) : IsPshBase φ := by
  intro z hz v
  obtain ⟨r,U,hr,hr1,hz0⟩ := exists_centeredChart hz
  have hi := fderiv_centeredChart_zero_injective hr hr1 U
  have hsurj := (LinearMap.injective_iff_surjective (f := (fderiv ℂ (centeredChart r U) 0).toLinearMap)).mp hi
  obtain ⟨u,hu⟩ := hsurj v
  have hf : ContDiffAt ℝ 2 φ (centeredChart r U 0) :=
    (hφ.contDiffAt (isOpen_ball.mem_nhds (by rw [hz0]; exact hz))).of_le (WithTop.coe_le_coe.mpr le_top)
  have he := baseHessian_value_comp hf (centeredChart_analyticAt U (z := 0) (by simp)) u u
  change fderiv ℂ (centeredChart r U) 0 u = v at hu
  erw [hu,hz0] at he
  rw [← he]
  exact (mul_nonneg hc (sq_nonneg _)).trans (hctl r hr hr1 U u).1

lemma euclidean_q_base (u : Fin 2 → ℂ) : euclidean.q u = ‖(WithLp.toLp 2 u : Base)‖^2 := by
  simp only [euclidean, HForm.q, form, Matrix.one_mulVec, dotProduct, Pi.star_apply]
  rw [PiLp.norm_sq_eq_of_L2, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

lemma form_q_base (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (u : Fin 2 → ℂ) :
    (form A hA).q u = (∑ i, ∑ j, A i j * u i * star (u j)).re := by
  simp only [HForm.q, form, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma chartControl_form_bounds {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {c C : ℝ} (hctl : ChartControl φ c C) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) :
    (∀ u, c * euclidean.q u ≤ (form (baseHessian (φ ∘ centeredChart r U) 0)
      (baseHessian_isHermitian ((chartWeight_contDiffAt hφ hr hr1 U).of_le (WithTop.coe_le_coe.mpr le_top)))).q u) ∧
    (∀ u, (form (baseHessian (φ ∘ centeredChart r U) 0)
      (baseHessian_isHermitian ((chartWeight_contDiffAt hφ hr hr1 U).of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C*euclidean.q u) := by
  constructor <;> intro u <;> rw [euclidean_q_base, form_q_base]
  · exact (hctl r hr hr1 U (WithLp.toLp 2 u)).1
  · exact (hctl r hr hr1 U (WithLp.toLp 2 u)).2

lemma chartJets_lifted_bounds {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {C : ℝ} (hj : ChartJets φ C) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) :
    (∀ i j k : Fin 2, ‖liftedThird (φ ∘ centeredChart r U) (0,0) i.castSucc j.castSucc k.castSucc‖ ≤ C) ∧
    (∀ i j k l : Fin 2, ‖liftedFourth (φ ∘ centeredChart r U) (0,0) i.castSucc j.castSucc k.castSucc l.castSucc‖ ≤ C) := by
  have hf := chartWeight_contDiffAt hφ hr hr1 U
  constructor
  · intro i j k
    rw [liftedThird_horizontal (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    have hh := hj r hr hr1 U j k i 0
    linarith only [hh, norm_nonneg (dbarBase (fun z => baseHessian (φ ∘ centeredChart r U) z j k) 0 0),
      norm_nonneg (dzBase (fun z => dbarBase (fun q => baseHessian (φ ∘ centeredChart r U) q j k) z 0) 0 i)]
  · intro i j k l
    rw [liftedFourth_horizontal (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    have hh := hj r hr hr1 U k l i j
    linarith only [hh, norm_nonneg (dzBase (fun z => baseHessian (φ ∘ centeredChart r U) z k l) 0 i),
      norm_nonneg (dbarBase (fun z => baseHessian (φ ∘ centeredChart r U) z k l) 0 j)]

end PinchedHartogs

end

end OAI
