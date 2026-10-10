import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem scalarDirection_swap {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (a b x : Euc n) : fderiv ℝ (scalarDirection φ a) x b =
      fderiv ℝ (scalarDirection φ b) x a := by
  rw [scalarDirection_fderiv hφ,scalarDirection_fderiv hφ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) b a

 theorem flux_direction_parts {V : Euc n → Euc n} (hV : ContDiff ℝ 1 V)
    {U : Set (Euc n)} (φ : SmoothLocalTest U) (e : Euc n) :
    (∫ x, inner ℝ (fderiv ℝ V x e) (gradient φ.val x)) =
      -(∫ x, inner ℝ (V x) (gradient (scalarDirection φ.val e) x)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let u : Fin n → Euc n → ℝ := fun i x ↦ inner ℝ (b i) (V x)
  have hu (i : Fin n) : ContDiff ℝ 1 (u i) := (innerSL ℝ (b i)).contDiff.comp hV
  have hdu (i : Fin n) (x : Euc n) : fderiv ℝ (u i) x e =
      inner ℝ (b i) (fderiv ℝ V x e) := by
    exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L e)
      (((innerSL ℝ (b i)).hasFDerivAt.comp x (hV.differentiable (by simp) x).hasFDerivAt).fderiv)
  have hv (i : Fin n) : ContDiff ℝ 1 (scalarDirection φ.val (b i)) :=
    (scalarDirection_contDiff φ.property.1 (b i)).of_le (by simp)
  have hvc (i : Fin n) : HasCompactSupport (scalarDirection φ.val (b i)) :=
    φ.property.2.1.of_isClosed_subset (isClosed_tsupport _) (scalarDirection_tsupport _ _)
  have hp (i : Fin n) := scalar_compact_integration_parts_C1 (hu i) (hv i) (hvc i) e
  have hsum (x : Euc n) : inner ℝ (fderiv ℝ V x e) (gradient φ.val x) =
      ∑ i, fderiv ℝ (u i) x e * scalarDirection φ.val (b i) x := by
    simp only [hdu,scalarDirection,← inner_gradient_left]
    simpa only [real_inner_comm] using (b.sum_inner_mul_inner (fderiv ℝ V x e) (gradient φ.val x)).symm
  have hsum' (x : Euc n) : inner ℝ (V x) (gradient (scalarDirection φ.val e) x) =
      ∑ i, u i x * fderiv ℝ (scalarDirection φ.val (b i)) x e := by
    simp only [scalarDirection_swap φ.property.1 (b _) e,u,← inner_gradient_left]
    simpa only [real_inner_comm] using (b.sum_inner_mul_inner (V x)
      (gradient (scalarDirection φ.val e) x)).symm
  simp_rw [hsum,hsum']
  rw [integral_finsetSum _ (fun i _ ↦ (hp i).2.1),
    integral_finsetSum _ (fun i _ ↦ (hp i).1)]
  simp only [(fun i ↦ (hp i).2.2),Finset.sum_neg_distrib,neg_neg]

 theorem WeakFluxEquation.derivative {V : Euc n → Euc n} (hV : ContDiff ℝ 1 V)
    {U : Set (Euc n)} (h : WeakFluxEquation V U) (e : Euc n) :
    WeakFluxEquation (fun x ↦ fderiv ℝ V x e) U := by
  intro φ
  rw [flux_direction_parts hV φ e]
  exact neg_eq_zero.mpr (h (directionLocalTest φ e))

 theorem gradient_direction_swap {f : Euc n → ℝ} (hf : ContDiff ℝ 2 f)
    (e x : Euc n) : gradient (fun y ↦ fderiv ℝ f y e) x =
      fderiv ℝ (gradient f) x e := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (gradient f) := (InnerProductSpace.toDual ℝ (Euc n)).symm.toContinuousLinearMap.contDiff.comp hdf
  apply ext_inner_right ℝ
  intro a
  rw [inner_gradient_left]
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) a e
  have hd := congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L a)
    (((ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x
      (hdf.differentiable (by simp) x).hasFDerivAt).fderiv)
  have hga := congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L e)
    (((innerSL ℝ a).hasFDerivAt.comp x (hg.differentiable (by simp) x).hasFDerivAt).fderiv)
  have heq : (fun y ↦ inner ℝ a (gradient f y)) = fun y ↦ fderiv ℝ f y a := by
    funext y
    rw [real_inner_comm,inner_gradient_left]
  change fderiv ℝ (fun y ↦ inner ℝ a (gradient f y)) x e = inner ℝ a (fderiv ℝ (gradient f) x e) at hga
  rw [heq] at hga
  have hda := congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L e)
    (((ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x
      (hdf.differentiable (by simp) x).hasFDerivAt).fderiv)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply,
    real_inner_comm,Function.comp_def] using hd.trans (hs.trans (hda.symm.trans hga))

end RPISingularHarnack

end

end OAI
