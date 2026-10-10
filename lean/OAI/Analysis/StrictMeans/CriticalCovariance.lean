import OAI.Analysis.StrictMeans.RankPairing

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def affineUpperHomeomorph (z : UpperHalfPlane) : UpperHalfPlane ≃ₜ UpperHalfPlane where
  toFun := affineProduct z
  invFun w := ⟨((w:ℂ) - (z.re:ℂ)) / (z.im:ℂ), by
    simpa [Complex.div_ofReal_im] using div_pos w.im_pos z.im_pos⟩
  left_inv w := by
    apply UpperHalfPlane.ext
    change ((affineAt z w) - (z.re:ℂ)) / (z.im:ℂ) = w
    simp [affineAt, z.im_ne_zero]
  right_inv w := by
    apply UpperHalfPlane.ext
    change (z.re:ℂ) + (z.im:ℂ) * (((w:ℂ) - (z.re:ℂ)) / (z.im:ℂ)) = w
    field_simp [z.im_ne_zero]
    ring
  continuous_toFun :=
    (continuous_const.add (continuous_const.mul UpperHalfPlane.continuous_coe)).upperHalfPlaneMk _
  continuous_invFun :=
    ((UpperHalfPlane.continuous_coe.sub continuous_const).div_const _).upperHalfPlaneMk _

@[simp] lemma affineUpperHomeomorph_apply (z w : UpperHalfPlane) :
    affineUpperHomeomorph z w = affineProduct z w := rfl

def targetRebase (f : DiskFamily) (z : UpperHalfPlane) (ξ : ℂ) : ℂ :=
  (ξ - halfPlaneFunction f z) / ((z.im:ℂ) * deriv (halfPlaneFunction f) z)

lemma targetRebase_injective (f : DiskFamily) (z : UpperHalfPlane) :
    Function.Injective (targetRebase f z) := by
  intro ξ η he
  have hd : (z.im:ℂ) * deriv (halfPlaneFunction f) z ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr z.im_ne_zero)
      (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  simpa using ((div_left_inj' hd).mp he)

lemma criticalMap_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) :
    criticalMap k (halfPlaneFunction (rebase f z)) w =
      targetRebase f z (criticalMap k (halfPlaneFunction f) (affineProduct z w)) := by
  unfold criticalMap targetRebase
  rw [halfPlaneFunction_rebase f z w.im_pos, halfPlaneFunction_rebase_deriv]
  simp only [coe_affineProduct,affineAt_im,Complex.ofReal_mul]
  by_cases hk : k = 0
  · simp [hk]
  · field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero,
      halfPlaneFunction_deriv_ne_zero f z.im_pos,Complex.ofReal_ne_zero.mpr hk]
    ring

lemma criticalMap_rebase_eq_iff (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) (ξ : ℂ) :
    criticalMap k (halfPlaneFunction (rebase f z)) w = targetRebase f z ξ ↔
      criticalMap k (halfPlaneFunction f) (affineProduct z w) = ξ := by
  rw [criticalMap_rebase, (targetRebase_injective f z).eq_iff]

@[simp] lemma affineProduct_im (z w : UpperHalfPlane) :
    (affineProduct z w).im = z.im * w.im := affineAt_im z w

def heightRebaseScale (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) : ℝ :=
  ‖deriv (halfPlaneFunction f) z‖ / z.im^(k-1)

lemma heightRebaseScale_pos (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    0 < heightRebaseScale k f z :=
  div_pos (norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos))
    (Real.rpow_pos_of_pos z.im_pos _)

lemma criticalHeight_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) :
    criticalHeight k (halfPlaneFunction (rebase f z)) w =
      heightRebaseScale k f z * criticalHeight k (halfPlaneFunction f) (affineProduct z w) := by
  unfold criticalHeight heightRebaseScale
  rw [halfPlaneFunction_rebase_deriv]
  simp only [coe_affineProduct,affineAt_im,UpperHalfPlane.coe_im,norm_inv,norm_div]
  rw [Real.mul_rpow z.im_pos.le w.im_pos.le]
  field_simp [(norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)).ne',
    (norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f (affineAt_mapsTo z w.im_pos))).ne',
    (Real.rpow_pos_of_pos z.im_pos (k-1)).ne']

lemma reciprocalPotential_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) (ξ : ℂ) :
    reciprocalPotential k (rebase f z,targetRebase f z ξ) w =
      reciprocalPotential k (f,ξ) (affineProduct z w) / heightRebaseScale k f z := by
  unfold reciprocalPotential targetRebase heightRebaseScale
  rw [halfPlaneFunction_rebase f z w.im_pos,← sub_div]
  simp only [sub_sub_sub_cancel_right,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos z.im_pos,affineProduct_im,coe_affineProduct]
  rw [Real.mul_rpow z.im_pos.le w.im_pos.le,
    Real.rpow_sub z.im_pos,Real.rpow_one]
  field_simp [z.im_ne_zero,(Real.rpow_pos_of_pos z.im_pos k).ne',
    (Real.rpow_pos_of_pos w.im_pos k).ne',
    (norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)).ne']

lemma goodPair_rebase {k : ℝ} {f : DiskFamily} {ξ : ℂ} (hg : GoodPair k (f,ξ))
    (z : UpperHalfPlane) : GoodPair k (rebase f z,targetRebase f z ξ) := by
  refine ⟨?_,?_,?_⟩
  · apply (compactPotential_iff _ _).mpr
    intro r hr
    have hc := (compactPotential_iff _ _).mp hg.1
      (r * heightRebaseScale k f z) (mul_pos hr (heightRebaseScale_pos k f z))
    convert (affineUpperHomeomorph z).isCompact_preimage.mpr hc using 1
    ext w
    simp only [mem_ofPred_eq,mem_preimage,affineUpperHomeomorph_apply]
    rw [reciprocalPotential_rebase,div_le_iff₀ (heightRebaseScale_pos k f z)]
  · intro w hw
    rw [jacobianExpression_rebase]
    exact hg.2.1 (affineProduct z w) ((criticalMap_rebase_eq_iff k f z w ξ).mp hw)
  · intro v w hv hw he
    apply (affineUpperHomeomorph z).injective
    apply hg.2.2 (affineProduct z v) (affineProduct z w)
      ((criticalMap_rebase_eq_iff k f z v ξ).mp hv)
      ((criticalMap_rebase_eq_iff k f z w ξ).mp hw)
    rw [criticalHeight_rebase,criticalHeight_rebase] at he
    exact mul_left_cancel₀ (heightRebaseScale_pos k f z).ne' he

lemma goodPair_rebase_iff (k : ℝ) (f : DiskFamily) (ξ : ℂ) (z : UpperHalfPlane) :
    GoodPair k (rebase f z,targetRebase f z ξ) ↔ GoodPair k (f,ξ) := by
  refine ⟨fun hg => ?_,fun hg => goodPair_rebase hg z⟩
  refine ⟨?_,?_,?_⟩
  · apply (compactPotential_iff _ _).mpr
    intro r hr
    have hc := (compactPotential_iff _ _).mp hg.1
      (r / heightRebaseScale k f z) (div_pos hr (heightRebaseScale_pos k f z))
    convert hc.image (affineUpperHomeomorph z).continuous using 1
    ext w
    constructor
    · intro hw
      let v := (affineUpperHomeomorph z).symm w
      have hv : affineProduct z v = w := (affineUpperHomeomorph z).apply_symm_apply w
      refine ⟨v,?_,hv⟩
      change reciprocalPotential k (rebase f z,targetRebase f z ξ) v ≤ _
      rw [reciprocalPotential_rebase,hv]
      exact (div_le_div_iff_of_pos_right (heightRebaseScale_pos k f z)).mpr hw
    · rintro ⟨v,hv,rfl⟩
      change reciprocalPotential k (rebase f z,targetRebase f z ξ) v ≤ _ at hv
      rw [reciprocalPotential_rebase] at hv
      exact (div_le_div_iff_of_pos_right (heightRebaseScale_pos k f z)).mp hv
  · intro w hw
    let v := (affineUpperHomeomorph z).symm w
    have hv : affineProduct z v = w := (affineUpperHomeomorph z).apply_symm_apply w
    have hc : criticalMap k (halfPlaneFunction (rebase f z)) v = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z v ξ).mpr (hv.symm ▸ hw)
    simpa only [jacobianExpression_rebase,← coe_affineProduct,hv] using hg.2.1 v hc
  · intro u v hu hv he
    let a := (affineUpperHomeomorph z).symm u
    let b := (affineUpperHomeomorph z).symm v
    have ha : affineProduct z a = u := (affineUpperHomeomorph z).apply_symm_apply u
    have hb : affineProduct z b = v := (affineUpperHomeomorph z).apply_symm_apply v
    have hca : criticalMap k (halfPlaneFunction (rebase f z)) a = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z a ξ).mpr (ha.symm ▸ hu)
    have hcb : criticalMap k (halfPlaneFunction (rebase f z)) b = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z b ξ).mpr (hb.symm ▸ hv)
    have hab := hg.2.2 a b hca hcb (by
      rw [criticalHeight_rebase,criticalHeight_rebase,ha,hb,he])
    calc u = affineProduct z a := ha.symm
         _ = affineProduct z b := congrArg (affineProduct z) hab
         _ = v := hb

end
end StrictInverseFirstPower

end

end OAI
