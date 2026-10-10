import OAI.Analysis.StrictMeans.CompactFamily

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

namespace StrictInverseFirstPower
noncomputable section

def cayleyToHalfPlane (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem one_sub_ne_zero_of_mem_disk {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    1 - w ≠ 0 := by
  intro h
  have : w = 1 := (sub_eq_zero.mp h).symm
  simp [this] at hw

theorem cayley_im_mul_norm_sq {w : ℂ} (hw : 1 - w ≠ 0) :
    (cayleyToHalfPlane w).im * ‖1 - w‖ ^ 2 = 1 - ‖w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [cayleyToHalfPlane, Complex.div_im]
  have hsq : Complex.normSq (1 - w) ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
  field_simp
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem cayley_mem_halfPlane {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    0 < (cayleyToHalfPlane w).im := by
  have hn : ‖w‖ < 1 := by simpa using hw
  have h := cayley_im_mul_norm_sq (one_sub_ne_zero_of_mem_disk hw)
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hp := lt_of_lt_of_eq hpos h.symm
  exact (mul_pos_iff.mp hp).resolve_right (by
    rintro ⟨_, hs⟩
    exact (not_lt_of_ge (sq_nonneg ‖1 - w‖)) hs) |>.1

theorem cayley_differentiableOn :
    DifferentiableOn ℂ cayleyToHalfPlane (ball 0 1) := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · exact fun w hw => one_sub_ne_zero_of_mem_disk hw

def cayleyToDisk (z : ℂ) : ℂ := (z - I) / (z + I)

lemma add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

lemma cayleyToDisk_mem {z : ℂ} (hz : 0 < z.im) :
    cayleyToDisk z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right, cayleyToDisk, norm_div,
    div_lt_one (norm_pos_iff.mpr (add_I_ne_zero hz))]
  have hsq : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [normSq_apply, add_re, I_re, add_zero, add_im, I_im,
      sub_re, sub_zero, sub_im]
    ring
  nlinarith [norm_nonneg (z + I), norm_nonneg (z - I)]

@[simp] lemma cayleyToDisk_I : cayleyToDisk I = 0 := by simp [cayleyToDisk]
@[simp] lemma cayleyToHalfPlane_zero : cayleyToHalfPlane 0 = I := by simp [cayleyToHalfPlane]

lemma cayleyToHalfPlane_toDisk {z : ℂ} (hz : 0 < z.im) :
    cayleyToHalfPlane (cayleyToDisk z) = z := by
  have hd := add_I_ne_zero hz
  have hi := one_sub_ne_zero_of_mem_disk (cayleyToDisk_mem hz)
  dsimp only [cayleyToHalfPlane, cayleyToDisk] at hi ⊢
  field_simp
  ring

lemma cayleyToDisk_toHalfPlane {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    cayleyToDisk (cayleyToHalfPlane w) = w := by
  have hd := one_sub_ne_zero_of_mem_disk hw
  have hi := add_I_ne_zero (cayley_mem_halfPlane hw)
  dsimp only [cayleyToDisk, cayleyToHalfPlane] at hi ⊢
  field_simp
  ring

lemma cayleyToDisk_hasDerivAt {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt cayleyToDisk (2 * I / (z + I) ^ 2) z := by
  convert! ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I)
    (add_I_ne_zero hz) using 1; simp
  ring

lemma cayleyToHalfPlane_hasDerivAt {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasDerivAt cayleyToHalfPlane (2 * I / (1 - w) ^ 2) w := by
  convert! (((hasDerivAt_id w).const_add 1).const_mul I).div
    ((hasDerivAt_id w).const_sub 1) (one_sub_ne_zero_of_mem_disk hw) using 1;
    simp
  ring

lemma cayleyToDisk_differentiableOn :
    DifferentiableOn ℂ cayleyToDisk {z : ℂ | 0 < z.im} :=
  fun _ hz => (cayleyToDisk_hasDerivAt hz).differentiableAt.differentiableWithinAt

lemma cayleyToDisk_injOn : InjOn cayleyToDisk {z : ℂ | 0 < z.im} := by
  intro z hz w hw h
  have := congrArg cayleyToHalfPlane h
  simpa only [cayleyToHalfPlane_toDisk hz, cayleyToHalfPlane_toDisk hw] using this

lemma cayleyToHalfPlane_injOn : InjOn cayleyToHalfPlane (ball 0 1) := by
  intro z hz w hw h
  have := congrArg cayleyToDisk h
  simpa only [cayleyToDisk_toHalfPlane hz, cayleyToDisk_toHalfPlane hw] using this

def affineAt (z : UpperHalfPlane) (w : ℂ) : ℂ := z.re + (z.im : ℂ) * w

@[simp] lemma affineAt_im (z : UpperHalfPlane) (w : ℂ) :
    (affineAt z w).im = z.im * w.im := by simp [affineAt]

@[simp] lemma affineAt_re (z : UpperHalfPlane) (w : ℂ) :
    (affineAt z w).re = z.re + z.im * w.re := by simp [affineAt]

lemma affineAt_mapsTo (z : UpperHalfPlane) :
    MapsTo (affineAt z) {w : ℂ | 0 < w.im} {w : ℂ | 0 < w.im} := by
  intro w hw
  simpa only [mem_ofPred_eq, affineAt_im] using mul_pos z.im_pos hw

lemma affineAt_injective (z : UpperHalfPlane) : Injective (affineAt z) := by
  intro a b hab
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr z.im_ne_zero) (add_left_cancel hab)

lemma affineAt_hasDerivAt (z : UpperHalfPlane) (w : ℂ) :
    HasDerivAt (affineAt z) (z.im : ℂ) w := by
  convert! ((hasDerivAt_id w).const_mul (z.im : ℂ)).const_add (z.re : ℂ) using 1
  simp

@[simp] lemma affineAt_I (z : UpperHalfPlane) : affineAt z I = z := z.re_add_im

@[simp] lemma affineAt_one (w : ℂ) : affineAt UpperHalfPlane.I w = w := by
  simp [affineAt]

def affineProduct (z w : UpperHalfPlane) : UpperHalfPlane :=
  ⟨affineAt z w, affineAt_mapsTo z w.im_pos⟩

@[simp] lemma coe_affineProduct (z w : UpperHalfPlane) :
    (affineProduct z w : ℂ) = affineAt z w := rfl

lemma affineAt_assoc (z w : UpperHalfPlane) (u : ℂ) :
    affineAt z (affineAt w u) = affineAt (affineProduct z w) u := by
  change (z.re : ℂ) + (z.im : ℂ) * ((w.re : ℂ) + (w.im : ℂ) * u) =
    ((affineAt z w).re : ℂ) + ((affineAt z w).im : ℂ) * u
  rw [affineAt_re, affineAt_im]
  change (z.re : ℂ) + (z.im : ℂ) * ((w.re : ℂ) + (w.im : ℂ) * u) =
    ((z.re + z.im * w.re : ℝ) : ℂ) + ((z.im * w.im : ℝ) : ℂ) * u
  push_cast
  ring

lemma affineProduct_assoc (z w u : UpperHalfPlane) :
    affineProduct (affineProduct z w) u = affineProduct z (affineProduct w u) := by
  apply UpperHalfPlane.ext
  exact (affineAt_assoc z w u).symm

def affineInverse (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(-(z.re : ℂ) + I) / (z.im : ℂ), by
    simpa [Complex.div_im, pow_two] using
      (div_pos z.im_pos (sq_pos_of_pos z.im_pos))⟩

lemma affineAt_inverse (z : UpperHalfPlane) :
    affineAt z (affineInverse z) = I := by
  dsimp [affineAt, affineInverse]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def halfPlaneFunction (f : DiskFamily) (z : ℂ) : ℂ :=
  2 * I * diskExtension f.val (cayleyToDisk z)

lemma halfPlaneFunction_differentiableOn (f : DiskFamily) :
    DifferentiableOn ℂ (halfPlaneFunction f) {z : ℂ | 0 < z.im} := by
  exact (f.property.1.comp cayleyToDisk_differentiableOn
    (fun _ hz => cayleyToDisk_mem hz)).const_mul (2 * I)

lemma halfPlaneFunction_injOn (f : DiskFamily) :
    InjOn (halfPlaneFunction f) {z : ℂ | 0 < z.im} := by
  intro z hz w hw h
  apply cayleyToDisk_injOn hz hw
  apply f.property.2.1 (cayleyToDisk_mem hz) (cayleyToDisk_mem hw)
  exact mul_left_cancel₀ (by simp : (2 : ℂ) * I ≠ 0) h

@[simp] lemma halfPlaneFunction_I (f : DiskFamily) : halfPlaneFunction f I = 0 := by
  simp [halfPlaneFunction, f.property.2.2.1]

lemma halfPlaneFunction_hasDerivAt (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (halfPlaneFunction f)
      (2 * I * (deriv (diskExtension f.val) (cayleyToDisk z) *
        (2 * I / (z + I) ^ 2))) z := by
  exact ((f.property.1.differentiableAt
    (isOpen_ball.mem_nhds (cayleyToDisk_mem hz))).hasDerivAt.comp z
      (cayleyToDisk_hasDerivAt hz)).const_mul (2 * I)

lemma halfPlaneFunction_deriv (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    deriv (halfPlaneFunction f) z =
      2 * I * (deriv (diskExtension f.val) (cayleyToDisk z) *
        (2 * I / (z + I) ^ 2)) :=
  (halfPlaneFunction_hasDerivAt f hz).deriv

@[simp] lemma halfPlaneFunction_deriv_I (f : DiskFamily) :
    deriv (halfPlaneFunction f) I = 1 := by
  rw [halfPlaneFunction_deriv f (by simp), cayleyToDisk_I, f.property.2.2.2]
  field_simp
  norm_num [Complex.I_sq]

lemma halfPlaneFunction_deriv_ne_zero (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    deriv (halfPlaneFunction f) z ≠ 0 := by
  rw [halfPlaneFunction_deriv f hz]
  exact mul_ne_zero (by simp) (mul_ne_zero
    (diskFamily_derivative_ne_zero f ⟨_, cayleyToDisk_mem hz⟩)
    (div_ne_zero (by simp) (pow_ne_zero _ (add_I_ne_zero hz))))

def cayleyDiskMap : C(UpperHalfPlane, UnitDisk) :=
  ⟨fun z => ⟨cayleyToDisk z, cayleyToDisk_mem z.im_pos⟩,
    ((cayleyToDisk_differentiableOn.continuousOn.comp_continuous
      UpperHalfPlane.continuous_coe (fun z => z.im_pos))).subtype_mk _⟩

lemma continuous_halfPlaneFunction :
    Continuous (fun p : DiskFamily × UpperHalfPlane => halfPlaneFunction p.1 p.2) := by
  have h : Continuous (fun p : DiskFamily × UpperHalfPlane =>
      2 * I * p.1.val (cayleyDiskMap p.2)) :=
    continuous_const.mul ((continuous_subtype_val.comp continuous_fst).eval
      (cayleyDiskMap.continuous.comp continuous_snd))
  exact h.congr (fun p => by
    simp only [halfPlaneFunction, cayleyDiskMap, ContinuousMap.coe_mk,
      diskExtension, dite_eq_left (cayleyToDisk_mem p.2.im_pos)])

lemma continuous_halfPlaneFunction_deriv :
    Continuous (fun p : DiskFamily × UpperHalfPlane => deriv (halfPlaneFunction p.1) p.2) := by
  have hh : (fun p : DiskFamily × UpperHalfPlane => deriv (halfPlaneFunction p.1) p.2) =
      fun p => 2 * I * (deriv (diskExtension p.1.val) (cayleyToDisk p.2) *
        (2 * I / ((p.2 : ℂ) + I) ^ 2)) := by
    funext p
    exact halfPlaneFunction_deriv p.1 p.2.im_pos
  rw [hh]
  apply Continuous.mul continuous_const
  apply Continuous.mul
  · exact continuous_diskFamily_derivative.comp
      (continuous_fst.prodMk (cayleyDiskMap.continuous.comp continuous_snd))
  · apply Continuous.div continuous_const
    · exact ((UpperHalfPlane.continuous_coe.comp continuous_snd).add continuous_const).pow 2
    · intro p
      exact pow_ne_zero _ (add_I_ne_zero p.2.im_pos)

end
end StrictInverseFirstPower

end

end OAI
