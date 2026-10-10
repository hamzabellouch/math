import OAI.Analysis.StrictMeans.HalfPlane

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isOpen_halfPlane : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

lemma halfPlaneFunction_hasDeriv (f : DiskFamily) (z : UpperHalfPlane) :
    HasDerivAt (halfPlaneFunction f) (deriv (halfPlaneFunction f) z) z :=
  ((halfPlaneFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds z.im_pos)).hasDerivAt

def rebaseDiskFunction (f : DiskFamily) (z : UpperHalfPlane) (w : ℂ) : ℂ :=
  (halfPlaneFunction f (affineAt z (cayleyToHalfPlane w)) - halfPlaneFunction f z) /
    (2 * I * z.im * deriv (halfPlaneFunction f) z)

lemma rebase_den_ne_zero (f : DiskFamily) (z : UpperHalfPlane) :
    2 * I * z.im * deriv (halfPlaneFunction f) z ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by simp) (Complex.ofReal_ne_zero.mpr z.im_ne_zero))
    (halfPlaneFunction_deriv_ne_zero f z.im_pos)

lemma rebaseDiskFunction_differentiableOn (f : DiskFamily) (z : UpperHalfPlane) :
    DifferentiableOn ℂ (rebaseDiskFunction f z) (ball 0 1) := by
  have ha : DifferentiableOn ℂ (fun w => affineAt z (cayleyToHalfPlane w)) (ball 0 1) :=
    (cayley_differentiableOn.const_mul (z.im : ℂ)).const_add (z.re : ℂ)
  exact ((halfPlaneFunction_differentiableOn f).comp ha
    (fun w hw => affineAt_mapsTo z (cayley_mem_halfPlane hw))).sub_const _ |>.div_const _

lemma rebaseDiskFunction_injOn (f : DiskFamily) (z : UpperHalfPlane) :
    InjOn (rebaseDiskFunction f z) (ball 0 1) := by
  intro a ha b hb hab
  apply cayleyToHalfPlane_injOn ha hb
  apply affineAt_injective z
  apply halfPlaneFunction_injOn f
    (affineAt_mapsTo z (cayley_mem_halfPlane ha))
    (affineAt_mapsTo z (cayley_mem_halfPlane hb))
  exact sub_left_injective
    ((div_left_inj' (rebase_den_ne_zero f z)).mp hab)

@[simp] lemma rebaseDiskFunction_zero (f : DiskFamily) (z : UpperHalfPlane) :
    rebaseDiskFunction f z 0 = 0 := by
  simp [rebaseDiskFunction]

lemma rebaseDiskFunction_hasDerivAt_zero (f : DiskFamily) (z : UpperHalfPlane) :
    HasDerivAt (rebaseDiskFunction f z) 1 0 := by
  have hc : HasDerivAt cayleyToHalfPlane (2 * I) 0 := by
    simpa using cayleyToHalfPlane_hasDerivAt (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  have ha : HasDerivAt (fun w : ℂ => affineAt z (cayleyToHalfPlane w))
      ((z.im : ℂ) * (2 * I)) 0 :=
    (affineAt_hasDerivAt z (cayleyToHalfPlane 0)).comp 0 hc
  have hf' : HasDerivAt (halfPlaneFunction f) (deriv (halfPlaneFunction f) z)
      (affineAt z (cayleyToHalfPlane 0)) := by simpa using halfPlaneFunction_hasDeriv f z
  have hf := hf'.comp (0 : ℂ) ha
  have hh : HasDerivAt (rebaseDiskFunction f z)
      ((deriv (halfPlaneFunction f) z * ((z.im : ℂ) * (2 * I))) /
        (2 * I * z.im * deriv (halfPlaneFunction f) z)) 0 :=
    (hf.sub_const (halfPlaneFunction f z)).div_const _
  convert! hh using 1
  field_simp [halfPlaneFunction_deriv_ne_zero f z.im_pos,
    Complex.ofReal_ne_zero.mpr z.im_ne_zero]

def rebaseDiskMap (f : DiskFamily) (z : UpperHalfPlane) : C(UnitDisk, ℂ) :=
  ⟨fun w => rebaseDiskFunction f z w,
    (rebaseDiskFunction_differentiableOn f z).continuousOn.comp_continuous
      continuous_subtype_val (fun w => w.property)⟩

lemma rebaseDiskMap_extension (f : DiskFamily) (z : UpperHalfPlane) {w : ℂ}
    (hw : w ∈ ball 0 1) :
    diskExtension (rebaseDiskMap f z) w = rebaseDiskFunction f z w := by
  simp only [diskExtension, dite_eq_left hw, rebaseDiskMap, ContinuousMap.coe_mk]

lemma rebaseDiskMap_normalized (f : DiskFamily) (z : UpperHalfPlane) :
    DiskNormalized (rebaseDiskMap f z) := by
  have he : EqOn (diskExtension (rebaseDiskMap f z)) (rebaseDiskFunction f z) (ball 0 1) :=
    fun _ hw => rebaseDiskMap_extension f z hw
  refine ⟨(rebaseDiskFunction_differentiableOn f z).congr he,
    fun a ha b hb hab => rebaseDiskFunction_injOn f z ha hb ?_, ?_, ?_⟩
  · simpa only [he ha, he hb] using hab
  · rw [he (mem_ball_self zero_lt_one), rebaseDiskFunction_zero]
  · exact ((rebaseDiskFunction_hasDerivAt_zero f z).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)) he)).deriv

def rebase (f : DiskFamily) (z : UpperHalfPlane) : DiskFamily :=
  ⟨rebaseDiskMap f z, rebaseDiskMap_normalized f z⟩

lemma halfPlaneFunction_rebase (f : DiskFamily) (z : UpperHalfPlane) {w : ℂ}
    (hw : 0 < w.im) :
    halfPlaneFunction (rebase f z) w =
      (halfPlaneFunction f (affineAt z w) - halfPlaneFunction f z) /
        ((z.im : ℂ) * deriv (halfPlaneFunction f) z) := by
  change 2 * I * diskExtension (rebaseDiskMap f z) (cayleyToDisk w) = _
  rw [rebaseDiskMap_extension f z (cayleyToDisk_mem hw)]
  unfold rebaseDiskFunction
  rw [cayleyToHalfPlane_toDisk hw]
  field_simp

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def cayleyHalfPlaneMap : C(UnitDisk, UpperHalfPlane) :=
  ⟨fun w => ⟨cayleyToHalfPlane w, cayley_mem_halfPlane w.property⟩,
    (cayley_differentiableOn.continuousOn.comp_continuous continuous_subtype_val
      (fun w => w.property)).upperHalfPlaneMk _⟩

lemma continuous_affineProduct :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane => affineProduct p.1 p.2) := by
  exact ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp continuous_fst)).add
    ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_fst)).mul
      (UpperHalfPlane.continuous_coe.comp continuous_snd))).upperHalfPlaneMk _

lemma continuous_rebaseDiskFunction :
    Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      rebaseDiskFunction p.1.1 p.1.2 p.2) := by
  have ht : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      affineProduct p.1.2 (cayleyHalfPlaneMap p.2)) :=
    continuous_affineProduct.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (cayleyHalfPlaneMap.continuous.comp continuous_snd))
  have hf := continuous_halfPlaneFunction.comp
    ((continuous_fst.comp continuous_fst).prodMk ht)
  have hz : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      halfPlaneFunction p.1.1 p.1.2) := continuous_halfPlaneFunction.comp continuous_fst
  have hd : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      deriv (halfPlaneFunction p.1.1) p.1.2) := continuous_halfPlaneFunction_deriv.comp continuous_fst
  have hy : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      (p.1.2.im : ℂ)) := Complex.continuous_ofReal.comp
    (UpperHalfPlane.continuous_im.comp (continuous_snd.comp continuous_fst))
  exact (hf.sub hz).div ((continuous_const.mul hy).mul hd)
    (fun p => rebase_den_ne_zero p.1.1 p.1.2)

lemma continuous_rebase :
    Continuous (fun p : DiskFamily × UpperHalfPlane => rebase p.1 p.2) := by
  exact (ContinuousMap.continuous_of_continuous_uncurry
    (fun p : DiskFamily × UpperHalfPlane => rebaseDiskMap p.1 p.2)
    continuous_rebaseDiskFunction).subtype_mk _

lemma halfPlaneFunction_of_cayley (f : DiskFamily) {w : ℂ} (hw : w ∈ ball 0 1) :
    halfPlaneFunction f (cayleyToHalfPlane w) = 2 * I * diskExtension f.val w := by
  simp only [halfPlaneFunction, cayleyToDisk_toHalfPlane hw]

lemma diskFamily_ext {f g : DiskFamily}
    (h : ∀ z : UpperHalfPlane, halfPlaneFunction f z = halfPlaneFunction g z) : f = g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  have he := h (cayleyHalfPlaneMap w)
  change halfPlaneFunction f (cayleyToHalfPlane w) =
    halfPlaneFunction g (cayleyToHalfPlane w) at he
  rw [halfPlaneFunction_of_cayley f w.property, halfPlaneFunction_of_cayley g w.property,
    diskExtension_coe, diskExtension_coe] at he
  exact mul_left_cancel₀ (by simp : (2 : ℂ) * I ≠ 0) he

lemma halfPlaneFunction_rebase_deriv (f : DiskFamily) (z w : UpperHalfPlane) :
    deriv (halfPlaneFunction (rebase f z)) w =
      deriv (halfPlaneFunction f) (affineProduct z w) / deriv (halfPlaneFunction f) z := by
  have hf := (halfPlaneFunction_hasDeriv f (affineProduct z w)).comp (w : ℂ)
    (affineAt_hasDerivAt z w)
  have hh := (hf.sub_const (halfPlaneFunction f z)).div_const
    ((z.im : ℂ) * deriv (halfPlaneFunction f) z)
  have he : halfPlaneFunction (rebase f z) =ᶠ[𝓝 (w : ℂ)]
      fun u => (halfPlaneFunction f (affineAt z u) - halfPlaneFunction f z) /
        ((z.im : ℂ) * deriv (halfPlaneFunction f) z) :=
    Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds w.im_pos)
      (fun u hu => halfPlaneFunction_rebase f z hu)
  rw [(hh.congr_of_eventuallyEq he).deriv]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]

lemma rebase_one (f : DiskFamily) : rebase f UpperHalfPlane.I = f := by
  apply diskFamily_ext
  intro w
  rw [halfPlaneFunction_rebase f _ w.im_pos]
  simp

lemma rebase_assoc (f : DiskFamily) (z w : UpperHalfPlane) :
    rebase (rebase f z) w = rebase f (affineProduct z w) := by
  apply diskFamily_ext
  intro u
  rw [halfPlaneFunction_rebase (rebase f z) w u.im_pos,
    halfPlaneFunction_rebase f z (affineAt_mapsTo w u.im_pos),
    halfPlaneFunction_rebase f z w.im_pos,
    halfPlaneFunction_rebase_deriv,
    halfPlaneFunction_rebase f (affineProduct z w) u.im_pos]
  rw [affineAt_assoc, show (affineProduct z w).im = z.im * w.im from affineAt_im z w]
  push_cast
  simp only [coe_affineProduct]
  field_simp [halfPlaneFunction_deriv_ne_zero f z.im_pos]
  ring

def halfPlaneQ (f : DiskFamily) (z : UpperHalfPlane) : ℂ :=
  (deriv (halfPlaneFunction f) z)⁻¹

lemma halfPlaneQ_ne_zero (f : DiskFamily) (z : UpperHalfPlane) : halfPlaneQ f z ≠ 0 :=
  inv_ne_zero (halfPlaneFunction_deriv_ne_zero f z.im_pos)

@[simp] lemma halfPlaneQ_I (f : DiskFamily) : halfPlaneQ f UpperHalfPlane.I = 1 := by
  simp [halfPlaneQ]

lemma halfPlaneQ_rebase (f : DiskFamily) (z w : UpperHalfPlane) :
    halfPlaneQ (rebase f z) w = halfPlaneQ f (affineProduct z w) / halfPlaneQ f z := by
  simp only [halfPlaneQ, halfPlaneFunction_rebase_deriv, inv_div, div_inv_eq_mul]
  ring

lemma continuous_halfPlaneQ :
    Continuous (fun p : DiskFamily × UpperHalfPlane => halfPlaneQ p.1 p.2) :=
  continuous_halfPlaneFunction_deriv.inv₀
    (fun p => halfPlaneFunction_deriv_ne_zero p.1 p.2.im_pos)

end
end StrictInverseFirstPower

end

end OAI
