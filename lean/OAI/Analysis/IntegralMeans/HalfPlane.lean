import OAI.Analysis.IntegralMeans.CompactClass

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def halfPlane : Set ℂ := {z | 0 < z.im}

lemma isOpen_halfPlane : IsOpen halfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

def HalfPlaneSchlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f halfPlane ∧ f Complex.I = 0 ∧ deriv f Complex.I = 1

def affine (z w : ℂ) : ℂ := (z.re : ℂ) + (z.im : ℂ) * w

@[simp] lemma affine_I (z : ℂ) : affine z Complex.I = z := by
  apply Complex.ext <;> simp [affine]

@[simp] lemma I_affine (w : ℂ) : affine Complex.I w = w := by
  simp [affine]

lemma affine_assoc (z w u : ℂ) : affine (affine z w) u = affine z (affine w u) := by
  apply Complex.ext <;> simp [affine, Complex.mul_re, Complex.mul_im] <;> ring

lemma affine_mem {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    affine z w ∈ halfPlane := by
  change 0 < (affine z w).im
  simpa [affine] using mul_pos hz hw

lemma affine_injective {z : ℂ} (hz : z ∈ halfPlane) : Function.Injective (affine z) := by
  intro u v h
  dsimp [affine] at h
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))) (add_left_cancel h)

lemma hasDerivAt_affine (z w : ℂ) : HasDerivAt (affine z) (z.im : ℂ) w := by
  convert (hasDerivAt_const w (z.re : ℂ)).add
    ((hasDerivAt_id w).const_mul (z.im : ℂ)) using 1 <;> first | rfl | simp

def reroot (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (f (affine z w) - f z) / ((z.im : ℂ) * deriv f z)

lemma hasDerivAt_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    HasDerivAt (reroot f z) (deriv f (affine z w) / deriv f z) w := by
  have hfd := (hf.1 (affine z w) (affine_mem hz hw)).differentiableAt
    (isOpen_halfPlane.mem_nhds (affine_mem hz hw))
  have h := ((hfd.hasDerivAt.comp w (hasDerivAt_affine z w)).sub_const (f z)).div_const
    ((z.im : ℂ) * deriv f z)
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  convert h using 1 <;> first | rfl | field_simp

lemma deriv_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    deriv (reroot f z) w = deriv f (affine z w) / deriv f z :=
  (hasDerivAt_reroot hf hz hw).deriv

lemma reroot_normalized {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) : HalfPlaneSchlicht (reroot f z) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hdf : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro w hw
    exact (hasDerivAt_reroot hf hz hw).differentiableAt.differentiableWithinAt
  · intro u hu v hv h
    apply affine_injective hz
    apply hf.2 (affine_mem hz hu) (affine_mem hz hv)
    have hh : f (affine z u) - f z = f (affine z v) - f z :=
      (div_left_inj' (mul_ne_zero hy hdf)).mp h
    exact sub_left_injective hh
  · simp [reroot]
  · rw [deriv_reroot hf hz (by simp [halfPlane]), affine_I, div_self hdf]

lemma reroot_comp {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    reroot (reroot f z) w = reroot f (affine z w) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hv : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw)
  have hdf : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hdg : deriv f (affine z w) ≠ 0 :=
    univalent_deriv_ne_zero isOpen_halfPlane hf (affine_mem hz hw)
  funext u
  have him : ((affine z w).im : ℂ) = (z.im : ℂ) * (w.im : ℂ) := by
    simp [affine]
  change (reroot f z (affine w u) - reroot f z w) /
    ((w.im : ℂ) * deriv (reroot f z) w) = _
  rw [deriv_reroot hf hz hw]
  simp only [reroot, affine_assoc, him]
  field_simp
  ring

def reciprocalDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ := (deriv f z)⁻¹

lemma reciprocalDeriv_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    reciprocalDeriv (reroot f z) w = reciprocalDeriv f (affine z w) / reciprocalDeriv f z := by
  simp [reciprocalDeriv, deriv_reroot hf hz hw, div_eq_mul_inv, mul_comm]

def diskCayley (z : ℂ) : ℂ := (z-Complex.I)/(z+Complex.I)

def halfCayley (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)

lemma cayley_den_ne_zero {z : ℂ} (hz : z ∈ halfPlane) : z+Complex.I ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at this
  change 0 < z.im at hz
  linarith

lemma halfCayley_den_ne_zero {z : ℂ} (hz : z ∈ disk) : 1-z ≠ 0 := by
  intro he
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  rw [← sub_eq_zero.mp he] at hz'
  norm_num at hz'

lemma diskCayley_maps {z : ℂ} (hz : z ∈ halfPlane) : diskCayley z ∈ disk := by
  have hd := cayley_den_ne_zero hz
  simp only [disk,Metric.mem_ball,dist_zero_right,diskCayley,norm_div]
  rw [div_lt_one (norm_pos_iff.mpr hd)]
  have hsql : ‖z-Complex.I‖^2 = z.re^2+(z.im-1)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hsqr : ‖z+Complex.I‖^2 = z.re^2+(z.im+1)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hz' : 0 < z.im := hz
  nlinarith [norm_nonneg (z+Complex.I),norm_nonneg (z-Complex.I)]

lemma halfCayley_im {z : ℂ} (_hz : z ∈ disk) :
    (halfCayley z).im = (1-‖z‖^2)/‖1-z‖^2 := by
  simp only [halfCayley,Complex.div_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma halfCayley_maps {z : ℂ} (hz : z ∈ disk) : halfCayley z ∈ halfPlane := by
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  change 0 < (halfCayley z).im
  rw [halfCayley_im hz]
  exact div_pos (by nlinarith [norm_nonneg z])
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (halfCayley_den_ne_zero hz)))

lemma halfCayley_diskCayley {z : ℂ} (hz : z ∈ halfPlane) : halfCayley (diskCayley z) = z := by
  have hd := cayley_den_ne_zero hz
  have hd2 := halfCayley_den_ne_zero (diskCayley_maps hz)
  dsimp [halfCayley,diskCayley] at *
  field_simp
  ring_nf

lemma diskCayley_halfCayley {z : ℂ} (hz : z ∈ disk) : diskCayley (halfCayley z) = z := by
  have hd := halfCayley_den_ne_zero hz
  have hd2 := cayley_den_ne_zero (halfCayley_maps hz)
  dsimp [halfCayley,diskCayley] at *
  field_simp
  ring

lemma diskCayley_hasDerivAt {z : ℂ} (hz : z ∈ halfPlane) :
    HasDerivAt diskCayley (2*Complex.I/(z+Complex.I)^2) z := by
  convert ((hasDerivAt_id z).sub_const Complex.I).div
    ((hasDerivAt_id z).add_const Complex.I) (cayley_den_ne_zero hz) using 1 <;> try rfl
  simp only [id_eq,mul_one,one_mul]
  ring

lemma halfCayley_hasDerivAt {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt halfCayley (2*Complex.I/(1-z)^2) z := by
  convert (((hasDerivAt_id z).const_add 1).const_mul Complex.I).div
    ((hasDerivAt_id z).const_sub 1) (halfCayley_den_ne_zero hz) using 1 <;> try rfl
  simp only [id_eq,mul_one]
  ring

@[simp] lemma diskCayley_I : diskCayley Complex.I = 0 := by simp [diskCayley]

@[simp] lemma halfCayley_zero : halfCayley 0 = Complex.I := by simp [halfCayley]

def diskToHalf (f : ℂ → ℂ) (z : ℂ) : ℂ := 2*Complex.I*f (diskCayley z)

def halfToDisk (f : ℂ → ℂ) (z : ℂ) : ℂ := f (halfCayley z)/(2*Complex.I)

lemma hasDerivAt_diskToHalf {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    {z : ℂ} (hz : z ∈ halfPlane) : HasDerivAt (diskToHalf f)
      (-(4 : ℂ)*deriv f (diskCayley z)/(z+Complex.I)^2) z := by
  have hd := ((hf _ (diskCayley_maps hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (diskCayley_maps hz))).hasDerivAt
  convert (hd.comp z (diskCayley_hasDerivAt hz)).const_mul (2*Complex.I) using 1 <;> try rfl
  ring_nf
  simp [Complex.I_sq]

lemma hasDerivAt_halfToDisk {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f halfPlane)
    {z : ℂ} (hz : z ∈ disk) : HasDerivAt (halfToDisk f)
      (deriv f (halfCayley z)/(1-z)^2) z := by
  have hd := ((hf _ (halfCayley_maps hz)).differentiableAt
    (isOpen_halfPlane.mem_nhds (halfCayley_maps hz))).hasDerivAt
  convert (hd.comp z (halfCayley_hasDerivAt hz)).div_const (2*Complex.I) using 1 <;> try rfl
  field_simp

lemma diskToHalf_schlicht {f : ℂ → ℂ} (hf : Schlicht f) :
    HalfPlaneSchlicht (diskToHalf f) := by
  refine ⟨⟨fun z hz => (hasDerivAt_diskToHalf hf.1.1 hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    have hm := hf.1.2 (diskCayley_maps hz) (diskCayley_maps hw)
      ((mul_left_cancel₀ (by simp : (2 : ℂ)*Complex.I ≠ 0)) he)
    simpa only [halfCayley_diskCayley hz,halfCayley_diskCayley hw] using congrArg halfCayley hm
  · simp [diskToHalf,hf.2.1]
  · rw [(hasDerivAt_diskToHalf hf.1.1 (show Complex.I ∈ halfPlane by simp [halfPlane])).deriv]
    norm_num [hf.2.2,add_sq,mul_assoc,Complex.I_sq,Complex.I_mul_I]

lemma halfToDisk_schlicht {f : ℂ → ℂ} (hf : HalfPlaneSchlicht f) :
    Schlicht (halfToDisk f) := by
  refine ⟨⟨fun z hz => (hasDerivAt_halfToDisk hf.1.1 hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    have hm := hf.1.2 (halfCayley_maps hz) (halfCayley_maps hw)
      ((div_left_inj' (by simp : (2 : ℂ)*Complex.I ≠ 0)).mp he)
    simpa only [diskCayley_halfCayley hz,diskCayley_halfCayley hw] using congrArg diskCayley hm
  · simp [halfToDisk,hf.2.1]
  · rw [(hasDerivAt_halfToDisk hf.1.1 (show (0 : ℂ) ∈ disk by simp [disk])).deriv]
    simp [hf.2.2]

lemma diskToHalf_halfToDisk {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ halfPlane) :
    diskToHalf (halfToDisk f) z = f z := by
  simp only [diskToHalf,halfToDisk,halfCayley_diskCayley hz]
  field_simp

lemma halfToDisk_diskToHalf {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ disk) :
    halfToDisk (diskToHalf f) z = f z := by
  simp [diskToHalf,halfToDisk,diskCayley_halfCayley hz]

def classFun (g : DiskClass) : ℂ → ℂ := diskToHalf (diskExtend g.1)

lemma classFun_schlicht (g : DiskClass) : HalfPlaneSchlicht (classFun g) :=
  diskToHalf_schlicht g.2

def classOfHalf (f : ℂ → ℂ) (hf : HalfPlaneSchlicht f) : DiskClass :=
  ⟨⟨fun z => halfToDisk f z, continuousOn_iff_continuous_domRestrict.mp
    (halfToDisk_schlicht hf).1.1.continuousOn⟩,by
      have he : EqOn (diskExtend (⟨fun z => halfToDisk f z,
        continuousOn_iff_continuous_domRestrict.mp
          (halfToDisk_schlicht hf).1.1.continuousOn⟩ : C(disk,ℂ))) (halfToDisk f) disk := by
        intro z hz
        exact diskExtend_apply _ ⟨z,hz⟩
      refine ⟨⟨(halfToDisk_schlicht hf).1.1.congr he,?_⟩,?_,?_⟩
      · intro z hz w hw h
        exact (halfToDisk_schlicht hf).1.2 hz hw ((he hz).symm.trans (h.trans (he hw)))
      · rw [he (by simp [disk])]
        exact (halfToDisk_schlicht hf).2.1
      · rw [he.deriv Metric.isOpen_ball (by simp [disk])]
        exact (halfToDisk_schlicht hf).2.2⟩

lemma classFun_classOfHalf {f : ℂ → ℂ} (hf : HalfPlaneSchlicht f) :
    EqOn (classFun (classOfHalf f hf)) f halfPlane := by
  intro z hz
  dsimp [classFun,diskToHalf,classOfHalf]
  rw [diskExtend_apply _ (⟨diskCayley z,diskCayley_maps hz⟩ : disk)]
  exact diskToHalf_halfToDisk hz

lemma continuous_classFun_eval : Continuous (fun p : DiskClass × halfPlane => classFun p.1 p.2) := by
  have hm' : Continuous (fun z : halfPlane => diskCayley z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (diskCayley_hasDerivAt z.2).continuousAt.comp continuous_subtype_val.continuousAt
  have h := (continuous_diskClassJet_eval 0).comp
    (continuous_id.prodMap (hm'.subtype_mk (fun z => diskCayley_maps z.2)))
  simpa only [iteratedDeriv_zero,classFun,diskToHalf,Function.comp_def,Prod.map, id_eq] using h.const_mul (2*Complex.I)

instance : LocallyCompactSpace halfPlane := isOpen_halfPlane.locallyCompactSpace

instance : T2Space DiskClass := inferInstanceAs (T2Space diskSchlichtSet)

instance : MeasurableSpace DiskClass := borel DiskClass

instance : BorelSpace DiskClass := ⟨rfl⟩

lemma differentiableOn_iteratedDeriv_open {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

lemma tendstoLocallyUniformlyOn_iteratedDeriv_open.{u_1} {U : Set ℂ} (hU : IsOpen U)
    {ι : Type u_1} {l : Filter ι} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l U := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hf.mono (fun i h => differentiableOn_iteratedDeriv_open hU h n)) hU

def classJet (n : ℕ) (g : DiskClass) : C(halfPlane,ℂ) :=
  ⟨fun z => iteratedDeriv n (classFun g) z, continuousOn_iff_continuous_domRestrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_halfPlane (classFun_schlicht g).1.1 n).continuousOn⟩

lemma continuous_classJet (n : ℕ) : Continuous (classJet n) := by
  have hc : Continuous (classJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_classFun_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn classFun (classFun g) (𝓝 g) halfPlane :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_halfPlane h
      (Eventually.of_forall (fun f : DiskClass => (classFun_schlicht f).1.1)) n)

lemma continuous_classJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × halfPlane => iteratedDeriv n (classFun p.1) p.2) :=
  continuous_eval.comp ((continuous_classJet n).prodMap continuous_id)

def rerootClass (g : DiskClass) (z : halfPlane) : DiskClass :=
  classOfHalf (reroot (classFun g) z) (reroot_normalized (classFun_schlicht g).1 z.2)

lemma classFun_rerootClass (g : DiskClass) (z : halfPlane) :
    EqOn (classFun (rerootClass g z)) (reroot (classFun g) z) halfPlane :=
  classFun_classOfHalf _

lemma continuous_rerootClass : Continuous (fun p : DiskClass × halfPlane => rerootClass p.1 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun p : (DiskClass × halfPlane) × disk =>
      (⟨halfCayley p.2,halfCayley_maps p.2.2⟩ : halfPlane)) := by
    apply Continuous.subtype_mk
    have hm : Continuous (fun z : disk => halfCayley z) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (halfCayley_hasDerivAt z.2).continuousAt.comp continuous_subtype_val.continuousAt
    exact hm.comp continuous_snd
  have ha : Continuous (fun p : (DiskClass × halfPlane) × disk =>
      (⟨affine p.1.2 (halfCayley p.2),affine_mem p.1.2.2 (halfCayley_maps p.2.2)⟩ : halfPlane)) := by
    apply Continuous.subtype_mk
    have hre : Continuous (fun p : (DiskClass × halfPlane) × disk => p.1.2.val.re) := Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    have him : Continuous (fun p : (DiskClass × halfPlane) × disk => p.1.2.val.im) := Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul (continuous_subtype_val.comp hc))
  have hvalue := continuous_classFun_eval.comp ((continuous_fst.comp continuous_fst).prodMk ha)
  have hroot : Continuous (fun p : (DiskClass × halfPlane) × disk => classFun p.1.1 p.1.2) :=
    continuous_classFun_eval.comp continuous_fst
  have hder : Continuous (fun p : (DiskClass × halfPlane) × disk => deriv (classFun p.1.1) p.1.2) := by
    simpa only [iteratedDeriv_one,Function.comp_def] using
      ((continuous_classJet_eval 1).comp (continuous_fst : Continuous (Prod.fst : (DiskClass × halfPlane) × disk → DiskClass × halfPlane)))
  have him : Continuous (fun p : (DiskClass × halfPlane) × disk => (p.1.2.val.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hdiv := (hvalue.sub hroot).div (him.mul hder) (fun p => mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt p.1.2.2))
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1.1).1 p.1.2.2))
  exact hdiv.div_const (2*Complex.I)

lemma class_ext {g h : DiskClass} (he : EqOn (classFun g) (classFun h) halfPlane) : g = h := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  have hx := congrArg (fun q : ℂ => q/(2*Complex.I)) (he (halfCayley_maps z.2))
  have hg : (classFun g) (halfCayley z)/(2*Complex.I) = g.1 z := by
    exact (halfToDisk_diskToHalf z.2).trans (diskExtend_apply _ z)
  have hh : (classFun h) (halfCayley z)/(2*Complex.I) = h.1 z := by
    exact (halfToDisk_diskToHalf z.2).trans (diskExtend_apply _ z)
  rwa [hg,hh] at hx

lemma reroot_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) {z : ℂ} (hz : z ∈ halfPlane) :
    EqOn (reroot f z) (reroot g z) halfPlane := by
  intro w hw
  simp only [reroot,he (affine_mem hz hw),he hz,he.deriv isOpen_halfPlane hz]

lemma rerootClass_comp (g : DiskClass) (z w : halfPlane) :
    rerootClass (rerootClass g z) w = rerootClass g ⟨affine z w,affine_mem z.2 w.2⟩ := by
  apply class_ext
  intro u hu
  rw [classFun_rerootClass _ _ hu,reroot_congr (classFun_rerootClass g z) w.2 hu,
    reroot_comp (classFun_schlicht g).1 z.2 w.2,classFun_rerootClass _ _ hu]

def classWeight (g : DiskClass) (z : halfPlane) : ℝ := ‖reciprocalDeriv (classFun g) z‖^2

lemma classWeight_pos (g : DiskClass) (z : halfPlane) : 0 < classWeight g z := by
  apply sq_pos_of_ne_zero
  exact norm_ne_zero_iff.mpr (inv_ne_zero
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 z.2))

lemma continuous_classWeight : Continuous (fun p : DiskClass × halfPlane => classWeight p.1 p.2) := by
  have hd : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
  exact (hd.inv₀ (fun p => univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.2)).norm.pow 2

lemma classWeight_cocycle (g : DiskClass) (z w : halfPlane) :
    classWeight g z * classWeight (rerootClass g z) w =
      classWeight g ⟨affine z w,affine_mem z.2 w.2⟩ := by
  have he := (classFun_rerootClass g z).deriv isOpen_halfPlane w.2
  have hq : reciprocalDeriv (classFun (rerootClass g z)) w =
      reciprocalDeriv (reroot (classFun g) z) w := congrArg Inv.inv he
  simp only [classWeight,hq,reciprocalDeriv_reroot (classFun_schlicht g).1 z.2 w.2,norm_div,div_pow]
  have hn : ‖reciprocalDeriv (classFun g) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (inv_ne_zero
      (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 z.2))
  field_simp

end Brennan

end

end OAI
