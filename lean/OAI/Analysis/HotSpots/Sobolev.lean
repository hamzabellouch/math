import OAI.Analysis.HotSpots.Reciprocal

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots


lemma existsUnique_of_coercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B u v = ℓ v := by
  let e := hB.continuousLinearEquivOfBilin
  let y := (InnerProductSpace.toDual ℝ V).symm ℓ
  refine ⟨e.symm y, ?_, ?_⟩
  · intro v
    calc
      B (e.symm y) v = inner ℝ (e (e.symm y)) v :=
        (hB.continuousLinearEquivOfBilin_apply _ _).symm
      _ = ℓ v := by simp [y, InnerProductSpace.toDual_symm_apply]
  · intro u hu
    apply e.injective
    rw [e.apply_symm_apply]
    apply ext_inner_right ℝ
    intro v
    calc
      inner ℝ (e u) v = B u v := hB.continuousLinearEquivOfBilin_apply _ _
      _ = ℓ v := hu v
      _ = inner ℝ y v := InnerProductSpace.toDual_symm_apply.symm




lemma test_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp φ 2 (volume.restrict Ω) :=
  MemLp.mono_measure Measure.restrict_le_self
    (hφ.continuous.memLp_of_hasCompactSupport hc)

lemma test_derivative_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : Plane) :
    MemLp (fun x => (fderiv ℝ φ x) e) 2 (volume.restrict Ω) :=
  MemLp.mono_measure Measure.restrict_le_self
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport (hc.fderiv_apply ℝ e))

lemma HasH1Gradient.add {Ω : Set Plane} {v w : Plane → ℝ} {g k : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hw : HasH1Gradient Ω w k) :
    HasH1Gradient Ω (v + w) (g + k) := by
  refine ⟨hv.1.add hw.1, hv.2.1.add hw.2.1, ?_⟩
  intro φ hφ hc hs e
  have hi1 : Integrable (fun x => v x * (fderiv ℝ φ x) e) (volume.restrict Ω) :=
    hv.1.integrable_mul (test_derivative_memLp hφ hc e)
  have hi2 : Integrable (fun x => w x * (fderiv ℝ φ x) e) (volume.restrict Ω) :=
    hw.1.integrable_mul (test_derivative_memLp hφ hc e)
  have hj1 : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
    (hv.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
  have hj2 : Integrable (fun x => inner ℝ (k x) e * φ x) (volume.restrict Ω) :=
    (hw.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
  simp only [Pi.add_apply, inner_add_left, add_mul]
  rw [integral_add hi1 hi2, integral_add hj1 hj2,
    hv.2.2 φ hφ hc hs e, hw.2.2 φ hφ hc hs e]
  ring

lemma HasH1Gradient.smul {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (a : ℝ) :
    HasH1Gradient Ω (a • v) (a • g) := by
  refine ⟨hv.1.const_smul a, hv.2.1.const_smul a, ?_⟩
  intro φ hφ hc hs e
  simp only [Pi.smul_apply, smul_eq_mul, real_inner_smul_left, mul_assoc,
    integral_const_mul]
  rw [hv.2.2 φ hφ hc hs e]
  ring

lemma HasH1Gradient.sub {Ω : Set Plane} {v w : Plane → ℝ} {g k : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hw : HasH1Gradient Ω w k) :
    HasH1Gradient Ω (v - w) (g - k) := by
  simpa [sub_eq_add_neg] using hv.add (hw.smul (-1))

lemma integral_test_derivative_zero {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : Plane) :
    (∫ x, (fderiv ℝ φ x) e) = 0 := by
  have hdi : Integrable (fun x => (fderiv ℝ φ x) e) volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ e)
  have hint := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Plane => (1 : ℝ)) (g := φ) (v := e) (μ := volume)
    (by simp) (by simpa using hdi)
    (by simpa using hφ.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const (1 : ℝ))
    (fun x _ => hφ.differentiable (by simp) x)
  simpa using hint

lemma HasH1Gradient.const {Ω : Set Plane} (hbound : Bornology.IsBounded Ω) (a : ℝ) :
    HasH1Gradient Ω (fun _ => a) 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbound.measure_lt_top.ne
  refine ⟨memLp_const a, MemLp.zero, ?_⟩
  intro φ hφ hc hs e
  have hr : (∫ x in Ω, (fderiv ℝ φ x) e) = (∫ x, (fderiv ℝ φ x) e) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport (fun y => (fderiv ℝ φ y) e) :=
      fun hh => hx (hs (tsupport_fderiv_apply_subset ℝ e hh))
    exact image_eq_zero_of_notMem_tsupport (f := fun y => (fderiv ℝ φ y) e) hnot
  simp only [Pi.zero_apply, inner_zero_left, zero_mul, integral_zero, neg_zero,
    integral_const_mul, hr, integral_test_derivative_zero hφ hc e, mul_zero]

lemma integrable_mul_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => f x * φ x) volume := by
  have hh : Continuous (fun x => f x * φ x) :=
    (hf.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hs)
  exact hh.integrable_of_hasCompactSupport hc.mul_left

lemma setIntegral_mul_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, f x * φ x) = ∫ x, f x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)), mul_zero]

lemma integral_mul_test_fderiv {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (e : Plane) :
    (∫ x in Ω, f x * (fderiv ℝ φ x) e) =
      -(∫ x in Ω, (fderiv ℝ f x) e * φ x) := by
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : ContinuousOn (fun x => (fderiv ℝ f x) e) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hds : tsupport (fun x => (fderiv ℝ φ x) e) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ e).trans hs
  rw [setIntegral_mul_test hds, setIntegral_mul_test hs]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_test hΩ hdf hφ.continuous hc hs)
    (integrable_mul_test hΩ hf.continuousOn hdφ (hc.fderiv_apply ℝ e) hds)
    (integrable_mul_test hΩ hf.continuousOn hφ.continuous hc hs)
    (fun x hx => ((hf x (hs hx)).contDiffAt (hΩ.mem_nhds (hs hx))).differentiableAt (by simp))
    (fun x _ => hφ.differentiable (by simp) x)

lemma HasH1Gradient.of_contDiffOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hv : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp (gradient f) 2 (volume.restrict Ω)) :
    HasH1Gradient Ω f (gradient f) := by
  refine ⟨hv, hg, ?_⟩
  intro φ hφ hc hs e
  simpa only [inner_gradient_left] using integral_mul_test_fderiv hΩ hf hφ hc hs e

lemma test_gradient_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp (gradient φ) 2 (volume.restrict Ω) := by
  apply MemLp.mono_measure Measure.restrict_le_self
  have hdc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (hφ.continuous_fderiv (by simp))
  apply hdc.memLp_of_hasCompactSupport
  exact (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ Plane).symm)

lemma HasH1Gradient.test {Ω : Set Plane} {φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    HasH1Gradient Ω φ (gradient φ) :=
  .of_contDiffOn hΩ hφ.contDiffOn (test_memLp hφ hc) (test_gradient_memLp hφ hc)


lemma test_vector_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : Plane) :
    MemLp (fun x => φ x • e) 2 (volume.restrict Ω) :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).comp_memLp'
    (test_memLp hφ hc)


structure H1Test (Ω : Set Plane) where
  val : Plane → ℝ
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val
  support : tsupport val ⊆ Ω

namespace H1Test
variable {Ω : Set Plane}
def scalar (φ : H1Test Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  (test_memLp φ.smooth φ.compact).toLp φ.val

def derivative (φ : H1Test Ω) (e : Plane) : Lp ℝ 2 (volume.restrict Ω) :=
  (test_derivative_memLp φ.smooth φ.compact e).toLp (fun x => (fderiv ℝ φ.val x) e)

def vector (φ : H1Test Ω) (e : Plane) : Lp Plane 2 (volume.restrict Ω) :=
  (test_vector_memLp φ.smooth φ.compact e).toLp (fun x => φ.val x • e)
end H1Test

abbrev H1Ambient (Ω : Set Plane) := WithLp 2
  (Lp ℝ 2 (volume.restrict Ω) × Lp Plane 2 (volume.restrict Ω))


def h1Graph (Ω : Set Plane) : Submodule ℝ (H1Ambient Ω) where
  carrier := {v | ∀ (φ : H1Test Ω) (e : Plane),
    ⟪v.fst, φ.derivative e⟫_ℝ + ⟪v.snd, φ.vector e⟫_ℝ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw φ e
    simp only [WithLp.add_fst, WithLp.add_snd, inner_add_left]
    linear_combination hv φ e + hw φ e
  smul_mem' := by
    intro a v hv φ e
    simp only [WithLp.smul_fst, WithLp.smul_snd, real_inner_smul_left]
    linear_combination a * hv φ e

lemma h1Graph_closed (Ω : Set Plane) : IsClosed (h1Graph Ω : Set (H1Ambient Ω)) := by
  change IsClosed {v : H1Ambient Ω | ∀ (φ : H1Test Ω) (e : Plane),
    ⟪v.fst, φ.derivative e⟫_ℝ + ⟪v.snd, φ.vector e⟫_ℝ = 0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro e
  apply isClosed_eq _ continuous_const
  exact (((WithLp.fstL 2 ℝ _ _).continuous.inner continuous_const).add
    ((WithLp.sndL 2 ℝ _ _).continuous.inner continuous_const))

abbrev H1 (Ω : Set Plane) := h1Graph Ω

instance H1.completeSpace (Ω : Set Plane) : CompleteSpace (H1 Ω) :=
  (h1Graph_closed Ω).completeSpace_coe

lemma h1Graph_mem_iff (Ω : Set Plane) (v : H1Ambient Ω) :
    v ∈ h1Graph Ω ↔ HasH1Gradient Ω v.fst v.snd := by
  have hscalar (φ : H1Test Ω) (e : Plane) :
      ⟪v.fst, φ.derivative e⟫_ℝ = ∫ x in Ω, v.fst x * (fderiv ℝ φ.val x) e := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(test_derivative_memLp (Ω := Ω) φ.smooth φ.compact e).coeFn_toLp] with x hx
    simp only [H1Test.derivative] at *
    simp [hx, RCLike.inner_apply, mul_comm]
  have hvector (φ : H1Test Ω) (e : Plane) :
      ⟪v.snd, φ.vector e⟫_ℝ = ∫ x in Ω, inner ℝ (v.snd x) e * φ.val x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(test_vector_memLp (Ω := Ω) φ.smooth φ.compact e).coeFn_toLp] with x hx
    simp only [H1Test.vector] at *
    rw [hx, inner_smul_right]
    simp [mul_comm]
  constructor
  · intro hv
    refine ⟨Lp.memLp _, Lp.memLp _, ?_⟩
    intro φ hφ hc hs e
    have h := hv (H1Test.mk φ hφ hc hs) e
    rw [hscalar, hvector] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro hv φ e
    rw [hscalar, hvector, hv.2.2 φ.val φ.smooth φ.compact φ.support e]
    exact neg_add_cancel _

lemma HasH1Gradient.congr {Ω : Set Plane} {v w : Plane → ℝ} {g k : Plane → Plane}
    (h : HasH1Gradient Ω v g) (hv : v =ᵐ[volume.restrict Ω] w)
    (hg : g =ᵐ[volume.restrict Ω] k) : HasH1Gradient Ω w k := by
  refine ⟨(memLp_congr_ae hv).mp h.1, (memLp_congr_ae hg).mp h.2.1, ?_⟩
  intro φ hφ hc hs e
  calc
    (∫ x in Ω, w x * (fderiv ℝ φ x) e) = ∫ x in Ω, v x * (fderiv ℝ φ x) e := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = -(∫ x in Ω, inner ℝ (g x) e * φ x) := h.2.2 φ hφ hc hs e
    _ = -(∫ x in Ω, inner ℝ (k x) e * φ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

def HasH1Gradient.toH1 {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (h : HasH1Gradient Ω v g) : H1 Ω :=
  ⟨WithLp.toLp 2 (h.1.toLp v, h.2.1.toLp g),
    (h1Graph_mem_iff Ω _).mpr (h.congr h.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm)⟩

namespace H1
variable {Ω : Set Plane}
def value : H1 Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (WithLp.fstL 2 ℝ _ _).comp (h1Graph Ω).subtypeL

def grad : H1 Ω →L[ℝ] Lp Plane 2 (volume.restrict Ω) :=
  (WithLp.sndL 2 ℝ _ _).comp (h1Graph Ω).subtypeL

lemma hasH1Gradient (u : H1 Ω) : HasH1Gradient Ω (value u) (grad u) :=
  (h1Graph_mem_iff Ω u.val).mp u.property

lemma norm_sq (u : H1 Ω) : ‖u‖^2 = ‖value u‖^2 + ‖grad u‖^2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 u.val

lemma value_toH1 {v : Plane → ℝ} {g : Plane → Plane} (h : HasH1Gradient Ω v g) :
    value h.toH1 = h.1.toLp v := rfl

lemma grad_toH1 {v : Plane → ℝ} {g : Plane → Plane} (h : HasH1Gradient Ω v g) :
    grad h.toH1 = h.2.1.toLp g := rfl

lemma grad_unique (hΩ : IsOpen Ω) {v : Plane → ℝ} {g k : Plane → Plane}
    (hg : HasH1Gradient Ω v g) (hk : HasH1Gradient Ω v k) :
    g =ᵐ[volume.restrict Ω] k := by
  have hi (e : Plane) : ∀ᵐ x ∂volume.restrict Ω, inner ℝ (g x - k x) e = 0 := by
    have hl := ((hg.2.1.sub hk.2.1).inner_const (𝕜 := ℝ) e).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have ht := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (μ := volume.restrict Ω) (hl.locallyIntegrableOn Ω)
      (fun φ hφ hc hs => show (∫ x in Ω, φ x • inner ℝ (g x - k x) e) = 0 from by
        have hgφ := hg.2.2 φ hφ hc hs e
        have hkφ := hk.2.2 φ hφ hc hs e
        have hgi : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
          (hg.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        have hki : Integrable (fun x => inner ℝ (k x) e * φ x) (volume.restrict Ω) :=
          (hk.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        simp only [smul_eq_mul, inner_sub_left, mul_sub]
        rw [integral_sub (by simpa [Pi.mul_apply, mul_comm] using hgi) (by simpa [Pi.mul_apply, mul_comm] using hki)]
        simp_rw [mul_comm (φ _)]
        linarith)
    filter_upwards [ht, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    exact hx hxΩ
  have hb : ∀ᵐ x ∂volume.restrict Ω, ∀ i : Fin 2,
      inner ℝ (g x - k x) (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 :=
    ae_all_iff.mpr fun i => hi _
  filter_upwards [hb] with x hx
  have hz : g x - k x = 0 := by
    ext i
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right] using hx i
  exact sub_eq_zero.mp hz

lemma value_injective (hΩ : IsOpen Ω) : Function.Injective (value (Ω := Ω)) := by
  intro u v huv
  have hdata : (value u : Plane → ℝ) =ᵐ[volume.restrict Ω] value v := by rw [huv]
  have hgrad := grad_unique hΩ ((hasH1Gradient u).congr hdata (Filter.EventuallyEq.refl _ _))
    (hasH1Gradient v)
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext huv (Lp.ext hgrad)
end H1


def smoothTestSpace (Ω : Set Plane) : Submodule ℝ (Plane → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, by simp⟩
    change IsCompact (tsupport (0 : Plane → ℝ))
    simp
  add_mem' := by
    rintro f g ⟨hf, hfc, hfs⟩ ⟨hg, hgc, hgs⟩
    exact ⟨hf.add hg, hfc.add hgc, (tsupport_add f g).trans (union_subset hfs hgs)⟩
  smul_mem' := by
    rintro a f ⟨hf, hfc, hfs⟩
    exact ⟨hf.const_smul a, hfc.smul_left,
      (tsupport_smul_subset_right (fun _ => a) f).trans hfs⟩

def smoothTestToH1 {Ω : Set Plane} (hΩ : IsOpen Ω) : smoothTestSpace Ω →ₗ[ℝ] H1 Ω where
  toFun f := (HasH1Gradient.test hΩ f.property.1 f.property.2.1).toH1
  map_add' f g := by
    apply H1.value_injective hΩ
    exact (test_memLp (Ω := Ω) f.property.1 f.property.2.1).toLp_add
      (test_memLp (Ω := Ω) g.property.1 g.property.2.1)
  map_smul' a f := by
    apply H1.value_injective hΩ
    exact (test_memLp (Ω := Ω) f.property.1 f.property.2.1).toLp_const_smul a

lemma smoothTestToH1_value_norm {Ω : Set Plane} (hΩ : IsOpen Ω)
    (f : smoothTestSpace Ω) :
    ‖H1.value (smoothTestToH1 hΩ f)‖ =
      (eLpNorm (f : Plane → ℝ) 2 (volume.restrict Ω)).toReal := by
  rw [show smoothTestToH1 hΩ f =
    (HasH1Gradient.test hΩ f.property.1 f.property.2.1).toH1 from rfl,
    H1.value_toH1]
  exact Lp.norm_toLp _ _

lemma smoothTestToH1_grad_norm {Ω : Set Plane} (hΩ : IsOpen Ω)
    (f : smoothTestSpace Ω) :
    ‖H1.grad (smoothTestToH1 hΩ f)‖ =
      (eLpNorm (gradient (f : Plane → ℝ)) 2 (volume.restrict Ω)).toReal := by
  rw [show smoothTestToH1 hΩ f =
    (HasH1Gradient.test hΩ f.property.1 f.property.2.1).toH1 from rfl,
    H1.grad_toH1]
  exact Lp.norm_toLp _ _


def h10Submodule {Ω : Set Plane} (hΩ : IsOpen Ω) : Submodule ℝ (H1 Ω) :=
  (smoothTestToH1 hΩ).range.topologicalClosure

abbrev H10 {Ω : Set Plane} (hΩ : IsOpen Ω) := h10Submodule hΩ

instance H10.normedAddCommGroup {Ω : Set Plane} (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10 hΩ) := (h10Submodule hΩ).normedAddCommGroup

instance H10.innerProductSpace {Ω : Set Plane} (hΩ : IsOpen Ω) :
    InnerProductSpace ℝ (H10 hΩ) := (h10Submodule hΩ).innerProductSpace

instance H10.completeSpace {Ω : Set Plane} (hΩ : IsOpen Ω) : CompleteSpace (H10 hΩ) :=
  (LinearMap.range (smoothTestToH1 hΩ)).isClosed_topologicalClosure.completeSpace_coe



lemma test_sobolev_ennreal {Ω : Set Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    eLpNorm f 2 (volume.restrict Ω) ≤
      eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 *
        eLpNorm (fderiv ℝ f) 1 (volume.restrict Ω) := by
  have hn : NNReal.HolderConjugate (Module.finrank ℝ Plane) 2 := by
    simpa [Plane, finrank_euclideanSpace] using NNReal.HolderConjugate.two_two
  have hS := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure Plane)
    (hf.of_le (by simp)) hc hn
  have hs' : Function.support f ⊆ Ω := (subset_tsupport _).trans hs
  have hds : Function.support (fderiv ℝ f) ⊆ Ω :=
    (subset_tsupport _).trans ((tsupport_fderiv_subset ℝ).trans hs)
  rw [eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable hs',
    eLpNorm_restrict_eq_of_support_subset (f := fderiv ℝ f)
      (p := (1 : ℝ≥0∞)) (μ := volume)
      (hf.continuous_fderiv (by simp)).aestronglyMeasurable hds]
  exact hS

lemma eLpNorm_fderiv_le_L2_gradient {Ω : Set Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    eLpNorm (fderiv ℝ f) 1 (volume.restrict Ω) ≤
      eLpNorm (gradient f) 2 (volume.restrict Ω) * (volume Ω) ^ (1 / 2 : ℝ) := by
  have hL := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict Ω) (f := fderiv ℝ f)
    (p := 1) (q := 2) (by norm_num)
    (hf.continuous_fderiv (by simp)).aestronglyMeasurable
  have hG : eLpNorm (fderiv ℝ f) 2 (volume.restrict Ω) =
      eLpNorm (gradient f) 2 (volume.restrict Ω) := by
    apply eLpNorm_congr_norm_ae
      (hf.continuous_fderiv (by simp)).aestronglyMeasurable
      (((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
        (hf.continuous_fderiv (by simp))).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x =>
      ((InnerProductSpace.toDual ℝ Plane).symm.norm_map _).symm
  rw [hG] at hL
  convert hL using 1
  norm_num


lemma test_poincare_ennreal {Ω : Set Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    eLpNorm f 2 (volume.restrict Ω) ≤
      (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
      (volume Ω) ^ (1 / 2 : ℝ) * eLpNorm (gradient f) 2 (volume.restrict Ω) := by
  calc
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 1 (volume.restrict Ω) := test_sobolev_ennreal hf hc hs
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
        (eLpNorm (gradient f) 2 (volume.restrict Ω) * (volume Ω) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_right (eLpNorm_fderiv_le_L2_gradient hf) _
    _ = _ := by ac_rfl

lemma test_poincare_real {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω) :
    (eLpNorm f 2 (volume.restrict Ω)).toReal ≤
      ((eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
      (volume Ω) ^ (1 / 2 : ℝ)).toReal *
      (eLpNorm (gradient f) 2 (volume.restrict Ω)).toReal := by
  have hA : (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  have hB : (volume Ω) ^ (1 / 2 : ℝ) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hb.measure_lt_top.ne
  have hg := test_gradient_memLp (Ω := Ω) hf hc
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA hB) hg.eLpNorm_ne_top)
    (test_poincare_ennreal hf hc hs)
  rwa [ENNReal.toReal_mul] at h



lemma smoothTest_poincare {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : smoothTestSpace Ω,
      ‖H1.value (smoothTestToH1 hΩ f)‖ ≤ C * ‖H1.grad (smoothTestToH1 hΩ f)‖ := by
  let A : ℝ≥0∞ := eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2
  let B : ℝ≥0∞ := (volume Ω) ^ (1 / 2 : ℝ)
  let C := (A * B).toReal + 1
  refine ⟨C, add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one, ?_⟩
  intro f
  have hreal := test_poincare_real hb f.property.1 f.property.2.1 f.property.2.2
  rw [smoothTestToH1_value_norm, smoothTestToH1_grad_norm]
  apply hreal.trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ENNReal.toReal_nonneg

private lemma norm_bound_on_closure {Domain : Type*} {Value : Type*} {Gradient : Type*}
    [TopologicalSpace Domain] [SeminormedAddCommGroup Value]
    [SeminormedAddCommGroup Gradient] (value : Domain → Value) (grad : Domain → Gradient)
    (hvalue : Continuous value) (hgrad : Continuous grad) (constant : ℝ)
    {tests : Set Domain} (hbound : ∀ point ∈ tests, ‖value point‖ ≤ constant * ‖grad point‖)
    {point : Domain} (hpoint : point ∈ closure tests) :
    ‖value point‖ ≤ constant * ‖grad point‖ :=
  closure_minimal hbound (isClosed_le hvalue.norm (continuous_const.mul hgrad.norm)) hpoint

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

local instance : NormedSpace ℝ (H10 hΩ) := (H10.innerProductSpace hΩ).toNormedSpace

def value : H10 hΩ →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  H1.value.comp (h10Submodule hΩ).subtypeL

def grad : H10 hΩ →L[ℝ] Lp Plane 2 (volume.restrict Ω) :=
  H1.grad.comp (h10Submodule hΩ).subtypeL

lemma norm_sq (u : H10 hΩ) : ‖u‖ ^ 2 = ‖value hΩ u‖ ^ 2 + ‖grad hΩ u‖ ^ 2 :=
  H1.norm_sq u.val

lemma poincare (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H10 hΩ, ‖value hΩ u‖ ≤ C * ‖grad hΩ u‖ := by
  obtain ⟨C, hC, htest⟩ := smoothTest_poincare hΩ hb
  have hsub : ∀ v ∈ ((smoothTestToH1 hΩ).range : Set (H1 Ω)),
      ‖H1.value v‖ ≤ C * ‖H1.grad v‖ := by
    rintro v ⟨f, rfl⟩
    exact htest f
  refine ⟨C, hC, fun u => ?_⟩
  exact norm_bound_on_closure H1.value H1.grad
    H1.value.continuous H1.grad.continuous C hsub u.property


def energy : H10 hΩ →L[ℝ] H10 hΩ →L[ℝ] ℝ := by
  letI : NormedSpace ℝ (H10 hΩ) := (H10.innerProductSpace hΩ).toNormedSpace
  let a : Lp Plane 2 (volume.restrict Ω) →L[ℝ]
      Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ := innerSL ℝ
  let b : H10 hΩ →L[ℝ] Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ :=
    a.comp (grad hΩ)
  let c : Lp Plane 2 (volume.restrict Ω) →L[ℝ] H10 hΩ →L[ℝ] ℝ := ContinuousLinearMap.flip (E := H10 hΩ) (F := Lp Plane 2 (volume.restrict Ω)) b
  let d : H10 hΩ →L[ℝ] H10 hΩ →L[ℝ] ℝ := c.comp (grad hΩ)
  exact ContinuousLinearMap.flip (E := H10 hΩ) (F := H10 hΩ) d

@[simp] lemma energy_apply (u v : H10 hΩ) :
    energy hΩ u v = inner ℝ (grad hΩ u) (grad hΩ v) := rfl

lemma energy_coercive (hb : Bornology.IsBounded Ω) :
    @IsCoercive (H10 hΩ) (H10.normedAddCommGroup hΩ).toSeminormedAddCommGroup
      (H10.innerProductSpace hΩ).toNormedSpace (energy hΩ) := by
  obtain ⟨C, hC, hP⟩ := poincare hΩ hb
  have hD : 0 < C ^ 2 + 1 := by positivity
  refine ⟨1 / (C ^ 2 + 1), by positivity, fun u => ?_⟩
  have hsq := (sq_le_sq₀ (norm_nonneg (value hΩ u))
    (mul_nonneg hC.le (norm_nonneg (grad hΩ u)))).mpr (hP u)
  have hbound : ‖u‖ ^ 2 ≤ (C ^ 2 + 1) * ‖grad hΩ u‖ ^ 2 := by
    rw [norm_sq hΩ]
    nlinarith
  calc
    (1 / (C ^ 2 + 1)) * ‖u‖ * ‖u‖ = ‖u‖ ^ 2 / (C ^ 2 + 1) := by ring
    _ ≤ ‖grad hΩ u‖ ^ 2 := (div_le_iff₀ hD).mpr (by simpa [mul_comm] using hbound)
    _ = energy hΩ u u := (real_inner_self_eq_norm_sq _).symm



lemma existsUnique_energy_solution (hb : Bornology.IsBounded Ω)
    (ℓ : H10 hΩ →L[ℝ] ℝ) :
    ∃! u : H10 hΩ, ∀ v : H10 hΩ, energy hΩ u v = ℓ v := by
  exact @existsUnique_of_coercive (H10 hΩ) (H10.normedAddCommGroup hΩ)
    (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    (energy hΩ) (energy_coercive hΩ hb) ℓ


lemma existsUnique_dirichlet_solution (hb : Bornology.IsBounded Ω)
    (f : Lp ℝ 2 (volume.restrict Ω)) :
    ∃! u : H10 hΩ, ∀ v : H10 hΩ,
      inner ℝ (grad hΩ u) (grad hΩ v) = inner ℝ f (value hΩ v) :=
  existsUnique_energy_solution hΩ hb ((innerSL ℝ f).comp (value hΩ))

end H10
end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
namespace StrictHotSpots.DiskCutoff

lemma transition_deriv_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      exact Real.smoothTransition.zero_of_nonpos hx.le
    simpa using h.deriv_eq
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      exact Real.smoothTransition.one_of_one_le hx.le
    simpa using h.deriv_eq

lemma transition_deriv_bound : ∃ L : ℝ, 0 ≤ L ∧
    ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (deriv Real.smoothTransition) (Icc (0 : ℝ) 1) from
      (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp) |>.continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have h : t < 0 ∨ 1 < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
    rw [transition_deriv_zero h, norm_zero]
    exact le_max_right _ _

variable {E : Type*} [NormedAddCommGroup E]

def cutoff (κ : ℝ) (x : E) : ℝ :=
  Real.smoothTransition (κ * (1 - ‖x‖ ^ 2) - 1)

lemma cutoff_nonneg (κ : ℝ) (x : E) : 0 ≤ cutoff κ x :=
  Real.smoothTransition.nonneg _

lemma cutoff_le_one (κ : ℝ) (x : E) : cutoff κ x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma cutoff_zero {κ : ℝ} {x : E} (hκ : 0 < κ) (hx : 1 - κ⁻¹ ≤ ‖x‖ ^ 2) :
    cutoff κ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hx)]

lemma cutoff_one {κ : ℝ} {x : E} (hx : 2 ≤ κ * (1 - ‖x‖ ^ 2)) :
    cutoff κ x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

lemma cutoff_tsupport {κ : ℝ} (hκ : 0 < κ) :
    tsupport (cutoff (E := E) κ) ⊆ {x | ‖x‖ ^ 2 ≤ 1 - κ⁻¹} := by
  apply closure_minimal _ (isClosed_le (continuous_norm.pow 2) continuous_const)
  intro x hx
  change ‖x‖ ^ 2 ≤ 1 - κ⁻¹
  by_contra hh
  exact hx (cutoff_zero hκ (le_of_lt (lt_of_not_ge hh)))

lemma cutoff_tsupport_disk {κ : ℝ} (hκ : 0 < κ) :
    tsupport (cutoff (E := E) κ) ⊆ Metric.ball 0 1 := by
  intro x hx
  have h := cutoff_tsupport hκ hx
  change ‖x‖ ^ 2 ≤ 1 - κ⁻¹ at h
  simp only [Metric.mem_ball, dist_zero_right]
  have hi : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hn := norm_nonneg x
  nlinarith

lemma cutoff_hasCompactSupport [ProperSpace E] {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (cutoff (E := E) κ) :=
  isCompact_closedBall 0 1 |>.of_isClosed_subset (isClosed_tsupport _)
    ((cutoff_tsupport_disk hκ).trans Metric.ball_subset_closedBall)

variable [InnerProductSpace ℝ E]

lemma cutoff_contDiff (κ : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) κ) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_const.sub (contDiff_id.norm_sq (𝕜 := ℝ)))).sub contDiff_const)

lemma cutoff_fderiv (κ : ℝ) (x : E) :
    fderiv ℝ (cutoff κ) x =
      (-2 * κ * deriv Real.smoothTransition (κ * (1 - ‖x‖ ^ 2) - 1)) • innerSL ℝ x := by
  have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have ha := ((hnorm.const_sub 1).const_mul κ).sub_const 1
  have hb := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (κ * (1 - ‖x‖ ^ 2) - 1)).hasDerivAt
  have hc := hb.comp_hasFDerivAt x ha
  change fderiv ℝ (Real.smoothTransition ∘ fun x : E => κ * (1 - ‖x‖ ^ 2) - 1) x = _
  rw [hc.fderiv]
  ext y
  simp
  ring

lemma cutoff_fderiv_zero {κ : ℝ} {x : E}
    (hx : 2 < κ * (1 - ‖x‖ ^ 2)) : fderiv ℝ (cutoff κ) x = 0 := by
  rw [cutoff_fderiv, transition_deriv_zero (Or.inr (by linarith))]
  simp

lemma cutoff_eventually_one (x : E) (hx : ‖x‖ < 1) :
    ∀ᶠ n : ℕ in atTop, cutoff ((n : ℝ) + 2) x = 1 ∧
      fderiv ℝ (cutoff ((n : ℝ) + 2)) x = 0 := by
  have hp : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 2) * (1 - ‖x‖ ^ 2)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop).atTop_mul_const hp
  filter_upwards [ht.eventually (eventually_gt_atTop (2 : ℝ))] with n hn
  exact ⟨cutoff_one hn.le, cutoff_fderiv_zero hn⟩

lemma boundary_vanishing_estimate [Nontrivial E] {f : E → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ x ∈ Metric.closedBall (0 : E) 1, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Metric.closedBall (0 : E) 1, ‖fderiv ℝ f x‖ ≤ C)
    (hz : ∀ x : E, ‖x‖ = 1 → f x = 0) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2) := by
  have hpoint : ∃ y : E, ‖y‖ = 1 ∧ ‖y-x‖ = 1-‖x‖ := by
    by_cases h : x = 0
    · obtain ⟨y,hy⟩ := exists_ne (0 : E)
      exact ⟨normalize y, norm_normalize hy, by simp [h, norm_normalize hy]⟩
    · refine ⟨normalize x, norm_normalize h, ?_⟩
      calc
        ‖normalize x - x‖ = ‖(1-‖x‖) • normalize x‖ := by rw [sub_smul, one_smul, norm_smul_normalize]
        _ = 1-‖x‖ := by rw [norm_smul, norm_normalize h, mul_one, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx)]
  obtain ⟨y,hy,hdist⟩ := hpoint
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hf hd
    (convex_closedBall (0 : E) (1 : ℝ))
    (show x ∈ Metric.closedBall (0 : E) 1 by simpa using hx)
    (show y ∈ Metric.closedBall (0 : E) 1 by simp [hy])
  rw [hz y hy, zero_sub, norm_neg, hdist] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith [norm_nonneg x]

lemma cutoff_mul_contDiff {f : E → ℝ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R)) :
    ContDiff ℝ ∞ (fun x => cutoff κ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (cutoff (E := E) κ)
  · have hxd := cutoff_tsupport_disk hκ hx
    have hxR : x ∈ Metric.ball (0 : E) R := Metric.ball_subset_ball hR.le hxd
    exact (cutoff_contDiff κ).contDiffAt.mul
      ((hf x hxR).contDiffAt (Metric.isOpen_ball.mem_nhds hxR))
  · have he := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

omit [InnerProductSpace ℝ E] in
lemma cutoff_mul_hasCompactSupport [ProperSpace E] {f : E → ℝ} {κ : ℝ}
    (hκ : 0 < κ) : HasCompactSupport (fun x => cutoff κ x * f x) :=
  (cutoff_hasCompactSupport hκ).mul_right

omit [InnerProductSpace ℝ E] in
lemma cutoff_mul_norm_le {f : E → ℝ} {κ C : ℝ} {x : E} (hf : ‖f x‖ ≤ C) :
    ‖cutoff κ x * f x‖ ≤ C := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans hf

lemma cutoff_mul_fderiv_bound {f : E → ℝ} {κ C L : ℝ} {x : E}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hx : ‖x‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hd : ‖fderiv ℝ f x‖ ≤ C)
    (hz : ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2))
    (ht : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) :
    ‖fderiv ℝ (fun x => cutoff κ x * f x) x‖ ≤ C + 4 * C * L := by
  rw [fderiv_fun_mul ((cutoff_contDiff κ).differentiable (by simp) x) hf]
  apply (norm_add_le _ _).trans
  have h1 : ‖cutoff κ x • fderiv ℝ f x‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans hd
  have h2 : ‖f x • fderiv ℝ (cutoff κ) x‖ ≤ 4 * C * L := by
    by_cases hh : 2 < κ * (1 - ‖x‖ ^ 2)
    · rw [cutoff_fderiv_zero hh, smul_zero, norm_zero]
      positivity
    · have hh' : κ * (1 - ‖x‖ ^ 2) ≤ 2 := le_of_not_gt hh
      rw [norm_smul, cutoff_fderiv, norm_smul]
      simp only [norm_mul, norm_neg, Real.norm_of_nonneg hκ.le,
        innerSL_apply_norm]
      rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
      have hn : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      calc
        _ ≤ (C * (1 - ‖x‖ ^ 2)) * (2 * κ * L * 1) := by
          apply mul_le_mul hz _ (by positivity) (mul_nonneg hC hn)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (ht _) (by positivity)) hx
            (norm_nonneg _) (by positivity)
        _ = 2 * C * L * (κ * (1 - ‖x‖ ^ 2)) := by ring
        _ ≤ 4 * C * L := by nlinarith [mul_le_mul_of_nonneg_left hh' (show 0 ≤ 2 * C * L by positivity)]
  exact add_le_add h1 h2

end StrictHotSpots.DiskCutoff

namespace StrictHotSpots.L2VectorLimits
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma norm_sq_eq_integral_norm_sq (f : Lp F 2 ν) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma norm_toLp_sub_sq {f g : X → F} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂ν := by
  rw [norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hfx hgx
  simp only [hx, hfx, hgx, Pi.sub_apply]

lemma tendsto_toLp_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → F} {g : X → F} {b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 ν) (hg : MemLp g 2 ν) (hb : MemLp b 2 ν)
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) := by
  have ht : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂ν) l (𝓝 0) := by
    have hm : ∀ᶠ n in l, AEStronglyMeasurable (fun x => ‖f n x-g x‖ ^ 2) ν :=
      Eventually.of_forall fun n => ((hf n).sub hg).aestronglyMeasurable.norm.pow 2
    have hd : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖‖f n x-g x‖ ^ 2‖ ≤ (b x+‖g x‖)^2 := by
      filter_upwards [hdom] with n hn
      filter_upwards [hn] with x hx
      have h1 : ‖f n x-g x‖ ≤ b x+‖g x‖ :=
        by linarith [norm_sub_le (f n x) (g x)]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hl : ∀ᵐ x ∂ν, Tendsto (fun n => ‖f n x-g x‖ ^ 2) l (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (g x)).norm.pow 2
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun x => (b x+‖g x‖)^2) hm hd (hb.add hg.norm).integrable_sq hl
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) l (𝓝 0) := by
    simpa only [norm_toLp_sub_sq] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr

end StrictHotSpots.L2VectorLimits

namespace StrictHotSpots
namespace H1
lemma tendsto_of_value_grad {Ω : Set Plane} {ι : Type*} {l : Filter ι}
    {f : ι → H1 Ω} {g : H1 Ω}
    (hv : Tendsto (fun n => value (f n)) l (𝓝 (value g)))
    (hg : Tendsto (fun n => grad (f n)) l (𝓝 (grad g))) :
    Tendsto f l (𝓝 g) := by
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp hg).pow 2
  have hsq : Tendsto (fun n => ‖f n-g‖ ^ 2) l (𝓝 0) := by
    simpa only [norm_sq, map_sub, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using h1.add h2
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr
end H1

namespace DiskH10
open DiskCutoff

def disk : Set Plane := Metric.ball 0 1

lemma norm_gradient_eq (f : Plane → ℝ) (x : Plane) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma smooth_zero_boundary_bounds {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x ∈ disk, ‖f x‖ ≤ C) ∧
      (∀ x ∈ disk, ‖fderiv ℝ f x‖ ≤ C) ∧
      (∀ x ∈ disk, ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2)) := by
  have hs : Metric.closedBall (0 : Plane) 1 ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hR
  have hdc := hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Plane) 1).exists_bound_of_continuousOn
    (hdc.mono hs)
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hd : ∀ x ∈ Metric.closedBall (0 : Plane) 1, ‖fderiv ℝ f x‖ ≤ C :=
    fun x hx => (hB x hx).trans (le_max_left _ _)
  have hdiff : ∀ x ∈ Metric.closedBall (0 : Plane) 1, DifferentiableAt ℝ f x :=
    fun x hx => ((hf x (hs hx)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hx))).differentiableAt (by simp)
  have hv : ∀ x ∈ disk, ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2) := by
    intro x hx
    exact boundary_vanishing_estimate hC hdiff hd hz (by simpa [disk] using (Metric.ball_subset_closedBall hx))
  refine ⟨C,hC,?_,fun x hx => hd x (Metric.ball_subset_closedBall hx),hv⟩
  intro x hx
  exact (hv x hx).trans (by nlinarith [sq_nonneg ‖x‖, mul_nonneg hC (sq_nonneg ‖x‖)])

lemma smooth_memH1 {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R)) :
    HasH1Gradient disk f (gradient f) := by
  have hs : Metric.closedBall (0 : Plane) 1 ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hR
  let : IsFiniteMeasure (volume.restrict disk) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hfc := hf.continuousOn
  have hgc : ContinuousOn (gradient f) (Metric.ball 0 R) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp))
  have hb {F : Type} [NormedAddCommGroup F] {g : Plane → F}
      (hg : ContinuousOn g (Metric.ball 0 R)) : MemLp g 2 (volume.restrict disk) := by
    obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Plane) 1).exists_bound_of_continuousOn (hg.mono hs)
    have hm : AEStronglyMeasurable g (volume.restrict disk) :=
      (hg.mono ((Metric.ball_subset_closedBall).trans hs)).aestronglyMeasurable Metric.isOpen_ball.measurableSet
    apply MemLp.of_bound hm C
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  exact HasH1Gradient.of_contDiffOn Metric.isOpen_ball
    (hf.mono ((Metric.ball_subset_closedBall).trans hs)) (hb hfc) (hb hgc)



lemma smooth_zero_boundary_memH10 {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → f x = 0) :
    (smooth_memH1 hR hf).toH1 ∈ h10Submodule (Ω := disk) Metric.isOpen_ball := by
  let hΩ : IsOpen disk := Metric.isOpen_ball
  let h := smooth_memH1 hR hf
  let : IsFiniteMeasure (volume.restrict disk) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  obtain ⟨C,hC,hv,hd,hzC⟩ := smooth_zero_boundary_bounds hR hf hz
  obtain ⟨L,hL,ht⟩ := transition_deriv_bound
  let ψ : ℕ → Plane → ℝ := fun n x => cutoff ((n : ℝ) + 2) x * f x
  have hκ (n : ℕ) : 0 < (n : ℝ) + 2 := by positivity
  have hψ (n : ℕ) : ContDiff ℝ ∞ (ψ n) := cutoff_mul_contDiff (hκ n) hR hf
  have hc (n : ℕ) : HasCompactSupport (ψ n) := cutoff_mul_hasCompactSupport (hκ n)
  have hs (n : ℕ) : tsupport (ψ n) ⊆ disk :=
    tsupport_mul_subset_left.trans (cutoff_tsupport_disk (hκ n))
  let test : ℕ → smoothTestSpace disk := fun n => ⟨ψ n, hψ n, hc n, hs n⟩
  have hdiff (x : Plane) (hx : x ∈ disk) : DifferentiableAt ℝ f x := by
    have hxR : x ∈ Metric.ball (0 : Plane) R := Metric.ball_subset_ball hR.le hx
    exact ((hf x hxR).contDiffAt (Metric.isOpen_ball.mem_nhds hxR)).differentiableAt (by simp)
  have hval : Tendsto (fun n => H1.value (smoothTestToH1 hΩ (test n))) atTop
      (𝓝 (H1.value h.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => test_memLp (hψ n) (hc n)) h.1 (memLp_const C)
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact cutoff_mul_norm_le (hv x hx)
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have he : ∀ᶠ n : ℕ in atTop, ψ n x = f x := by
        filter_upwards [cutoff_eventually_one x (by simpa [disk] using hx)] with n hn
        simp only [ψ, hn.1, one_mul]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  have hgrad : Tendsto (fun n => H1.grad (smoothTestToH1 hΩ (test n))) atTop
      (𝓝 (H1.grad h.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => test_gradient_memLp (hψ n) (hc n)) h.2.1 (memLp_const (C + 4 * C * L))
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [norm_gradient_eq]
      exact cutoff_mul_fderiv_bound (hκ n) hC hL
        (by simpa [disk] using (Metric.ball_subset_closedBall hx))
        (hdiff x hx) (hd x hx) (hzC x hx) ht
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have he : ∀ᶠ n : ℕ in atTop, gradient (ψ n) x = gradient f x := by
        filter_upwards [cutoff_eventually_one x (by simpa [disk] using hx)] with n hn
        unfold gradient ψ
        rw [fderiv_fun_mul ((cutoff_contDiff _).differentiable (by simp) x) (hdiff x hx)]
        simp only [hn.1, hn.2, one_smul, smul_zero, add_zero]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  change h.toH1 ∈ closure ((smoothTestToH1 hΩ).range : Set (H1 disk))
  exact mem_closure_of_tendsto (H1.tendsto_of_value_grad hval hgrad)
    (Eventually.of_forall fun n => ⟨test n, rfl⟩)

end DiskH10
end StrictHotSpots

open scoped Laplacian
namespace StrictHotSpots

lemma integral_inner_gradient_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, inner ℝ (gradient f x) (gradient φ x)) =
      -(∫ x in Ω, Δ f x * φ x) := by
  let b := stdOrthonormalBasis ℝ Plane
  have hd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (b i)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hdd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i)) Ω :=
    ((hd i).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have he (x : Plane) : inner ℝ (gradient f x) (gradient φ x) =
      ∑ i, fderiv ℝ f x (b i) * fderiv ℝ φ x (b i) := by
    rw [← b.sum_inner_mul_inner (gradient f x) (gradient φ x)]
    simp only [inner_gradient_left, inner_gradient_right, starRingEnd_apply, star_trivial]
  have hl (x : Plane) (hx : x ∈ Ω) : Δ f x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i _
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    rw [fderiv_clm_apply
      ((((hf x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp
  have hi (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ f x (b i) * fderiv ℝ φ x (b i)) (volume.restrict Ω) := by
    apply Integrable.restrict
    exact integrable_mul_test hΩ (hd i).continuousOn
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans hs)
  have hj (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) * φ x)
      (volume.restrict Ω) :=
    (integrable_mul_test hΩ (hdd i).continuousOn hφ.continuous hc hs).restrict
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_test_fderiv hΩ (hd _) hφ hc hs]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [hl x hx, Finset.sum_mul]

lemma inner_toLp_toLp {X F : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f g : X → F}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

lemma smoothTest_value {Ω : Set Plane} (hΩ : IsOpen Ω) (φ : smoothTestSpace Ω) :
    H1.value (smoothTestToH1 hΩ φ) =
      (test_memLp (Ω := Ω) φ.property.1 φ.property.2.1).toLp (φ : Plane → ℝ) := by
  rw [show smoothTestToH1 hΩ φ =
    (HasH1Gradient.test hΩ φ.property.1 φ.property.2.1).toH1 from rfl, H1.value_toH1]

lemma smoothTest_grad {Ω : Set Plane} (hΩ : IsOpen Ω) (φ : smoothTestSpace Ω) :
    H1.grad (smoothTestToH1 hΩ φ) =
      (test_gradient_memLp (Ω := Ω) φ.property.1 φ.property.2.1).toLp (gradient (φ : Plane → ℝ)) := by
  rw [show smoothTestToH1 hΩ φ =
    (HasH1Gradient.test hΩ φ.property.1 φ.property.2.1).toH1 from rfl, H1.grad_toH1]

lemma smooth_weak_poisson {Ω : Set Plane} {u f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (huH1 : HasH1Gradient Ω u (gradient u))
    (hf : MemLp f 2 (volume.restrict Ω))
    (hp : ∀ x ∈ Ω, Δ u x = -f x) (v : H10 hΩ) :
    inner ℝ (H1.grad huH1.toH1) (H10.grad hΩ v) =
      inner ℝ (hf.toLp f) (H10.value hΩ v) := by
  let S : Set (H1 Ω) := {w | inner ℝ (H1.grad huH1.toH1) (H1.grad w) =
    inner ℝ (hf.toLp f) (H1.value w)}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner H1.grad.continuous)
    (continuous_const.inner H1.value.continuous)
  have hi : ((smoothTestToH1 hΩ).range : Set (H1 Ω)) ⊆ S := by
    rintro w ⟨φ,rfl⟩
    change inner ℝ (H1.grad huH1.toH1) (H1.grad (smoothTestToH1 hΩ φ)) =
      inner ℝ (hf.toLp f) (H1.value (smoothTestToH1 hΩ φ))
    rw [H1.grad_toH1, smoothTest_grad, smoothTest_value, inner_toLp_toLp, inner_toLp_toLp,
      integral_inner_gradient_test hΩ hu φ.property.1 φ.property.2.1 φ.property.2.2]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hp x hx]
    ring
  exact (closure_minimal hi hS) v.property

end StrictHotSpots







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
