import OAI.Analysis.StrictMeans.Rebasing

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
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def affineDiskFunction (w : ℂ) : ℂ := w / (1 - w)

lemma affineDiskFunction_differentiableOn :
    DifferentiableOn ℂ affineDiskFunction (ball 0 1) :=
  differentiableOn_id.div (differentiableOn_id.const_sub 1)
    (fun _ hw => one_sub_ne_zero_of_mem_disk hw)

lemma affineDiskFunction_injOn : InjOn affineDiskFunction (ball 0 1) := by
  intro a ha b hb hab
  have h := (div_eq_div_iff (one_sub_ne_zero_of_mem_disk ha)
    (one_sub_ne_zero_of_mem_disk hb)).mp hab
  linear_combination h

lemma affineDiskFunction_hasDerivAt_zero : HasDerivAt affineDiskFunction 1 0 := by
  convert! (hasDerivAt_id (0 : ℂ)).div
    ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by norm_num : (1 : ℂ) - 0 ≠ 0) using 1
  simp

def affineDiskMap : C(UnitDisk, ℂ) :=
  ⟨fun w => affineDiskFunction w,
    affineDiskFunction_differentiableOn.continuousOn.comp_continuous
      continuous_subtype_val (fun w => w.property)⟩

lemma affineDiskMap_extension {w : ℂ} (hw : w ∈ ball 0 1) :
    diskExtension affineDiskMap w = affineDiskFunction w := by
  simp only [diskExtension, dite_eq_left hw, affineDiskMap, ContinuousMap.coe_mk]

lemma affineDiskMap_normalized : DiskNormalized affineDiskMap := by
  have he : EqOn (diskExtension affineDiskMap) affineDiskFunction (ball 0 1) :=
    fun _ hw => affineDiskMap_extension hw
  refine ⟨affineDiskFunction_differentiableOn.congr he,
    fun a ha b hb hab => affineDiskFunction_injOn ha hb ?_, ?_, ?_⟩
  · simpa only [he ha, he hb] using hab
  · rw [he (mem_ball_self zero_lt_one)]
    simp [affineDiskFunction]
  · exact (affineDiskFunction_hasDerivAt_zero.congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)) he)).deriv

def affineFamily : DiskFamily := ⟨affineDiskMap, affineDiskMap_normalized⟩

instance : Nonempty DiskFamily := ⟨affineFamily⟩

lemma halfPlaneFunction_affineFamily {z : ℂ} (hz : 0 < z.im) :
    halfPlaneFunction affineFamily z = z - I := by
  change 2 * I * diskExtension affineDiskMap (cayleyToDisk z) = _
  rw [affineDiskMap_extension (cayleyToDisk_mem hz)]
  dsimp only [affineDiskFunction, cayleyToDisk]
  have hd := add_I_ne_zero hz
  have he : 1 - (z - I) / (z + I) = 2 * I / (z + I) := by
    field_simp
    ring
  rw [he]
  field_simp

lemma halfPlaneFunction_affineFamily_deriv (z : UpperHalfPlane) :
    deriv (halfPlaneFunction affineFamily) z = 1 := by
  apply HasDerivAt.deriv
  exact ((hasDerivAt_id (z : ℂ)).sub_const I).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds z.im_pos)
      (fun _ hw => halfPlaneFunction_affineFamily hw))

@[simp] lemma halfPlaneQ_affineFamily (z : UpperHalfPlane) : halfPlaneQ affineFamily z = 1 := by
  simp only [halfPlaneQ, halfPlaneFunction_affineFamily_deriv, inv_one]

@[simp] lemma rebase_affineFamily (z : UpperHalfPlane) : rebase affineFamily z = affineFamily := by
  apply diskFamily_ext
  intro w
  rw [halfPlaneFunction_rebase affineFamily z w.im_pos,
    halfPlaneFunction_affineFamily (affineAt_mapsTo z w.im_pos),
    halfPlaneFunction_affineFamily z.im_pos, halfPlaneFunction_affineFamily w.im_pos,
    halfPlaneFunction_affineFamily_deriv]
  dsimp only [affineAt]
  rw [← z.re_add_im]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  ring

def rebaseUncurried : C(DiskFamily × UpperHalfPlane, DiskFamily) :=
  ⟨fun p => rebase p.1 p.2, continuous_rebase⟩

def rebaseMap (z : UpperHalfPlane) : C(DiskFamily, DiskFamily) :=
  rebaseUncurried.comp ((ContinuousMap.id DiskFamily).prodMk (ContinuousMap.const DiskFamily z))

def weightMap (z : UpperHalfPlane) : C(DiskFamily, ℝ) :=
  ⟨fun f => ‖halfPlaneQ f z‖,
    (continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).norm⟩

def affineOperator (z : UpperHalfPlane) : C(DiskFamily, ℝ) →L[ℝ] C(DiskFamily, ℝ) :=
  (ContinuousLinearMap.mul ℝ C(DiskFamily, ℝ) (weightMap z)).comp
    (ContinuousMap.compCLM ℝ ℝ (rebaseMap z))

@[simp] lemma affineOperator_apply (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)) (f : DiskFamily) :
    affineOperator z φ f = ‖halfPlaneQ f z‖ * φ (rebase f z) := rfl

lemma affineOperator_monotone (z : UpperHalfPlane) : Monotone (affineOperator z) := by
  intro φ ψ h f
  change ‖halfPlaneQ f z‖ * φ (rebase f z) ≤ ‖halfPlaneQ f z‖ * ψ (rebase f z)
  exact mul_le_mul_of_nonneg_left (h (rebase f z)) (norm_nonneg _)

lemma affineOperator_mul (z w : UpperHalfPlane) :
    affineOperator z * affineOperator w = affineOperator (affineProduct z w) := by
  ext φ f
  simp only [mul_apply_eq_comp, affineOperator_apply, rebase_assoc, halfPlaneQ_rebase,
    norm_div]
  field_simp [norm_ne_zero_iff.mpr (halfPlaneQ_ne_zero f z)]

@[simp] lemma affineOperator_one : affineOperator UpperHalfPlane.I = 1 := by
  ext φ f
  simp [rebase_one]

@[simp] lemma affineOperator_affineFamily (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)) :
    affineOperator z φ affineFamily = φ affineFamily := by simp

lemma continuous_affineOperator_apply (φ : C(DiskFamily, ℝ)) :
    Continuous (fun p : UpperHalfPlane × DiskFamily => affineOperator p.1 φ p.2) := by
  exact (continuous_halfPlaneQ.comp continuous_swap).norm.mul
    (φ.continuous.comp (continuous_rebase.comp continuous_swap))

lemma continuous_affineOperator_strong (φ : C(DiskFamily, ℝ)) :
    Continuous (fun z : UpperHalfPlane => affineOperator z φ) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_affineOperator_apply φ)

def dyadicLeft : UpperHalfPlane := ⟨-(1 / 2 : ℂ) + I / 2, by norm_num⟩
def dyadicRight : UpperHalfPlane := ⟨(1 / 2 : ℂ) + I / 2, by norm_num⟩

def dyadicOperator : C(DiskFamily, ℝ) →L[ℝ] C(DiskFamily, ℝ) :=
  (1 / 2 : ℝ) • (affineOperator dyadicLeft + affineOperator dyadicRight)

lemma dyadicOperator_monotone : Monotone dyadicOperator := by
  intro φ ψ h f
  change (1 / 2 : ℝ) * _ ≤ (1 / 2 : ℝ) * _
  exact mul_le_mul_of_nonneg_left
    (add_le_add (affineOperator_monotone dyadicLeft h f)
      (affineOperator_monotone dyadicRight h f)) (by norm_num)

@[simp] lemma dyadicOperator_affineFamily (φ : C(DiskFamily, ℝ)) :
    dyadicOperator φ affineFamily = φ affineFamily := by
  change (1 / 2 : ℝ) * (affineOperator dyadicLeft φ affineFamily +
    affineOperator dyadicRight φ affineFamily) = _
  simp
  ring

lemma dyadicOperator_pow_affineFamily (n : ℕ) :
    (dyadicOperator ^ n) (1 : C(DiskFamily, ℝ)) affineFamily = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, dyadicOperator_affineFamily, ih]

lemma dyadicOperator_pow_norm_ge_one (n : ℕ) : 1 ≤ ‖dyadicOperator ^ n‖ := by
  have he := ((dyadicOperator ^ n) (1 : C(DiskFamily, ℝ))).norm_coe_le_norm affineFamily
  rw [dyadicOperator_pow_affineFamily, norm_one] at he
  exact he.trans (by simpa using (dyadicOperator ^ n).le_opNorm (1 : C(DiskFamily, ℝ)))

end
end StrictInverseFirstPower

end

end OAI
