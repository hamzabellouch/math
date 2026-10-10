import OAI.Dynamics.TriangleBilliards.SeamEnergy

namespace OAI

universe uA uC

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis

/-- Fubini for a real bounded spatial kernel.  Both input slices are merely
integrable; neither is differentiated. -/
lemma real_kernel_adjoint_slice {A : Type uA} [MeasurableSpace A]
    {μ : Measure A} [SFinite μ] {k l : A → A → ℝ}
    (hk : StronglyMeasurable (Function.uncurry k)) {K : ℝ}
    (hK : ∀ x y, |k x y| ≤ K) (hs : ∀ x y, k x y = l y x)
    {f g : A → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (∫ y, k x y • f y ∂μ) * conj (g x) ∂μ) =
      ∫ y, f y * conj (∫ x, l y x • g x ∂μ) ∂μ := by
  have hgc : Integrable (fun x => conj (g x)) μ :=
    hg.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Eventually.of_forall fun _ => by simp)
  have hi : Integrable (Function.uncurry (fun x y => (k x y • f y) * conj (g x)))
      (μ.prod μ) := by
    have hh := (hgc.mul_prod hf).bdd_mul
      (Complex.continuous_ofReal.comp_stronglyMeasurable hk).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa only [Complex.norm_real, Real.norm_eq_abs, Function.uncurry] using hK p.1 p.2)
    convert hh using 1
    ext p
    change (k p.1 p.2 • f p.2) * conj (g p.1) =
      (k p.1 p.2 : ℂ) * (conj (g p.1) * f p.2)
    rw [Complex.real_smul]
    ring
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hs]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis

def fiberKernel {A : Type uA} {C : Type uC} [MeasurableSpace A] (μ : Measure A)
    (J : C → C) (k : A → A → C → ℝ) (f : A × C → ℂ) (z : A × C) : ℂ :=
  ∫ y, k z.1 y z.2 • f (y, J z.2) ∂μ

/-- The transport-reversing kernel identity gives the adjoint on a product
space.  This is applicable to both the direct term (J = id) and a wall
reflection, including a derivative kernel with the opposite sign. -/
lemma fiberKernel_adjoint {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure C} [SFinite μ] [SFinite ν]
    {J : C → C} (hJ : MeasurePreserving J ν ν) (hJe : MeasurableEmbedding J)
    (hJJ : Function.Involutive J) {k l : A → A → C → ℝ}
    (hk : ∀ c, StronglyMeasurable (Function.uncurry (fun x y => k x y c)))
    (hK : ∀ c, ∃ K : ℝ, ∀ x y, |k x y c| ≤ K)
    (hs : ∀ x y c, k x y c = l y x (J c))
    {f g : A × C → ℂ} (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hpair₁ : Integrable (fun z => fiberKernel μ J k f z * conj (g z)) (μ.prod ν))
    (hpair₂ : Integrable (fun z => f z * conj (fiberKernel μ J l g z)) (μ.prod ν)) :
    (∫ z, fiberKernel μ J k f z * conj (g z) ∂μ.prod ν) =
      ∫ z, f z * conj (fiberKernel μ J l g z) ∂μ.prod ν := by
  rw [integral_prod_symm _ hpair₁, integral_prod_symm _ hpair₂]
  calc
    _ = ∫ c, ∫ y, f (y, J c) * conj (fiberKernel μ J l g (y, J c)) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hJ.quasiMeasurePreserving.ae hf.prod_left_ae, hg.prod_left_ae] with c hfc hgc
      obtain ⟨K,hKc⟩ := hK c
      have h := real_kernel_adjoint_slice (hk c) hKc (fun x y => hs x y c) hfc hgc
      simpa only [fiberKernel, hJJ c] using h
    _ = _ := hJ.integral_comp hJe (fun c => ∫ y, f (y,c) * conj (fiberKernel μ J l g (y,c)) ∂μ)

end TriangularBilliards.Analysis

namespace TriangularBilliards
open SpatialSmoothing Filter Analysis
open scoped Topology ComplexConjugate

lemma kernel_swap (ε : ℝ) (x y : ℂ) : kernel ε (x-y) = kernel ε (y-x) := by
  exact kernel_radial ε (norm_sub_rev x y)

lemma kernel_wall_swap (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y : ℂ) :
    kernel ε (x-wallReflection Q i y) = kernel ε (y-wallReflection Q i x) := by
  rw [← kernel_wall_transfer, kernel_swap]

lemma kernel_fderiv_neg (ε : ℝ) (x : ℂ) :
    fderiv ℝ (kernel ε) (-x) = -fderiv ℝ (kernel ε) x := by
  simp only [kernel_fderiv, smul_neg, rho_fderiv_neg]

lemma kernel_derivative_swap (ε : ℝ) (x y V : ℂ) :
    fderiv ℝ (kernel ε) (x-y) V = -fderiv ℝ (kernel ε) (y-x) V := by
  rw [← neg_sub x y, kernel_fderiv_neg]
  simp only [_root_.neg_apply, neg_neg]

/-- Reversal of a reflected short segment also reverses its transported
kernel derivative. This is proved from the actual wall unfolding. -/
lemma kernel_wall_derivative_swap (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y V : ℂ) :
    fderiv ℝ (kernel ε) (x-wallReflection Q i y) V =
      -fderiv ℝ (kernel ε) (y-wallReflection Q i x) (reflect (Q.tangent i) V) := by
  have h₁ := ((kernel_contDiff ε).differentiable (by simp) (x-wallReflection Q i y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (wallReflection Q i y))
  have h₂ := ((kernel_contDiff ε).differentiable (by simp) (y-wallReflection Q i x)).hasFDerivAt.comp x
    ((wallReflection_hasFDerivAt Q i x).const_sub y)
  have he : (fun x => kernel ε (x-wallReflection Q i y)) =
      (fun x => kernel ε (y-wallReflection Q i x)) := funext (fun x => kernel_wall_swap Q i ε x y)
  change HasFDerivAt (fun x => kernel ε (x-wallReflection Q i y)) _ x at h₁
  change HasFDerivAt (fun x => kernel ε (y-wallReflection Q i x)) _ x at h₂
  rw [he] at h₁
  have hd := h₁.unique h₂
  have ha := congrArg (fun L : ℂ →L[ℝ] ℝ => L V) hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    _root_.neg_apply, map_neg] at ha
  exact ha

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Analytic Filter
open scoped ComplexConjugate

lemma fiberKernel_stronglyMeasurable {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} [SFinite μ] {J : C → C} (hJ : Measurable J)
    {k : A → A → C → ℝ}
    (hk : StronglyMeasurable (fun p : (A × C) × A => k p.1.1 p.2 p.1.2))
    {f : A × C → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fiberKernel μ J k f) := by
  exact (hk.smul (hf.comp_measurable (measurable_snd.prodMk (hJ.comp measurable_fst.snd)))).integral_prod_right

lemma fiberKernel_memLp {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure C} [IsFiniteMeasure μ] [SFinite ν]
    {J : C → C} (hJ : MeasurePreserving J ν ν) {k : A → A → C → ℝ}
    (hk : StronglyMeasurable (fun p : (A × C) × A => k p.1.1 p.2 p.1.2))
    {K : ℝ} (hK : ∀ x y c, |k x y c| ≤ K)
    {f : A × C → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (μ.prod ν)) :
    MemLp (fiberKernel μ J k f) 2 (μ.prod ν) := by
  let g : A × C → ℂ := fun z => f (z.1,J z.2)
  have hg : StronglyMeasurable g := hf.comp_measurable (measurable_fst.prodMk (hJ.measurable.comp measurable_snd))
  have hg₂ : MemLp g 2 (μ.prod ν) := hf₂.comp_measurePreserving ((MeasurePreserving.id μ).prod hJ)
  have hF := hk.smul (hf.comp_measurable (measurable_snd.prodMk (hJ.measurable.comp measurable_fst.snd)))
  have hb : ∀ x c y, ‖k x y c • f (y,J c)‖ₑ ≤ ENNReal.ofReal K * ‖g (y,c)‖ₑ := by
    intro x c y
    rw [enorm_smul]
    exact mul_le_mul' (by simpa only [Real.enorm_eq_ofReal_abs] using
      ENNReal.ofReal_le_ofReal (hK x y c)) le_rfl
  have hrow (x : A) : ∫⁻ y : A, ENNReal.ofReal K ∂μ ≤ ENNReal.ofReal K * μ Set.univ := by simp
  have hbound := fiber_kernel_integral_schur_sq μ μ ν (K := fun _ _ : A => ENNReal.ofReal K)
    (F := fun z y => k z.1 y z.2 • f (y,J z.2))
    (measurable_const : Measurable (Function.uncurry (fun _ _ : A => ENNReal.ofReal K)))
    hg.enorm hrow hrow hF hb
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
    (by norm_num) (fiberKernel_stronglyMeasurable hJ.measurable hk hf).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hfint : ∫⁻ y, ‖g y‖ₑ ^ (2 : ℕ) ∂μ.prod ν < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hg₂.eLpNorm_lt_top
  have hA : ENNReal.ofReal K * μ Set.univ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  exact hbound.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA hA) hfint)

lemma memLp_conj {A : Type uA} [MeasurableSpace A] {μ : Measure A} {p : ℝ≥0∞}
    {f : A → ℂ} (hf : MemLp f p μ) : MemLp (fun x => conj (f x)) p μ := by
  apply hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall fun _ => by simp

lemma fiberKernel_L2_adjoint {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure C} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {J : C → C} (hJ : MeasurePreserving J ν ν) (hJe : MeasurableEmbedding J)
    (hJJ : Function.Involutive J) {k l : A → A → C → ℝ}
    (hk : StronglyMeasurable (fun p : (A × C) × A => k p.1.1 p.2 p.1.2))
    (hl : StronglyMeasurable (fun p : (A × C) × A => l p.1.1 p.2 p.1.2))
    {K L : ℝ} (hK : ∀ x y c, |k x y c| ≤ K) (hL : ∀ x y c, |l x y c| ≤ L)
    (hs : ∀ x y c, k x y c = l y x (J c))
    {f g : A × C → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν)) :
    (∫ z, fiberKernel μ J k f z * conj (g z) ∂μ.prod ν) =
      ∫ z, f z * conj (fiberKernel μ J l g z) ∂μ.prod ν := by
  apply fiberKernel_adjoint hJ hJe hJJ
    (fun c => hk.comp_measurable ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    (fun c => ⟨K,fun x y => hK x y c⟩) hs (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
  · exact (fiberKernel_memLp hJ hk hK hfm hf).integrable_mul (memLp_conj hg)
  · exact hf.integrable_mul (memLp_conj (fiberKernel_memLp hJ hl hL hgm hg))

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped ComplexConjugate

abbrev DirectionParity := Circle × ZMod 2

def associatedField (f : DoublePhase → ℂ) (p : ℂ × DirectionParity) : ℂ :=
  f ((p.1,p.2.1),p.2.2)

lemma associatedField_memLp (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (associatedField f) 2
      ((volume.restrict Q.table).prod (angularMeasure.prod parityMeasure)) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have ha := measurePreserving_prodAssoc μ angularMeasure parityMeasure
  have hh := hf.comp_measurePreserving (ha.symm MeasurableEquiv.prodAssoc)
  have h := hh.smul_measure Q.area_lt_top.ne
  change MemLp (associatedField f) 2 _ at h
  simpa only [μ, Measure.prod_smul_left, smul_smul,
    ENNReal.mul_inv_cancel Q.area_pos.ne' Q.area_lt_top.ne, one_smul] using h

lemma associatedField_stronglyMeasurable {f : DoublePhase → ℂ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (associatedField f) :=
  hf.comp_measurable ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

lemma double_integral_assoc (Q : Triangle) (F : DoublePhase → ℂ) :
    ∫ z, F z ∂doubleMeasure Q = ((volume Q.table)⁻¹).toReal •
      ∫ p : ℂ × DirectionParity, F ((p.1,p.2.1),p.2.2)
        ∂(volume.restrict Q.table).prod (angularMeasure.prod parityMeasure) := by
  simp only [doubleMeasure, phaseMeasure, Measure.prod_smul_left, integral_smul_measure]
  congr 1
  exact (measurePreserving_prodAssoc (volume.restrict Q.table) angularMeasure parityMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun p : ℂ × DirectionParity => F ((p.1,p.2.1),p.2.2))

def directionParityReflection (Q : Triangle) (i : Fin 3) (c : DirectionParity) : DirectionParity :=
  (reflectedDirection Q i c.1,c.2+1)

lemma directionParityReflection_involutive (Q : Triangle) (i : Fin 3) :
    Function.Involutive (directionParityReflection Q i) := by
  rintro ⟨v,b⟩
  simp only [directionParityReflection, reflectedDirection_involutive, Prod.mk.injEq, true_and]
  have : (1 : ZMod 2) + 1 = 0 := by decide
  rw [add_assoc, this, add_zero]

lemma measurePreserving_directionParity (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (directionParityReflection Q i) (angularMeasure.prod parityMeasure)
      (angularMeasure.prod parityMeasure) := by
  convert (measurePreserving_reflectedDirection Q i).prod (measurePreserving_parity_add 1) using 1
  funext ⟨v,b⟩
  exact congrArg (fun q => (reflectedDirection Q i v,q)) (add_comm b 1)

lemma measurableEmbedding_directionParity (Q : Triangle) (i : Fin 3) :
    MeasurableEmbedding (directionParityReflection Q i) :=
  (MeasurableEquiv.ofInvolutive (directionParityReflection Q i)
    (directionParityReflection_involutive Q i)
    (measurePreserving_directionParity Q i).measurable).measurableEmbedding

/-- Kernel integration on the two physical triangle copies, with the exact
unnormalized Euclidean spatial integral and normalized phase pairing. -/
def doubleKernel (Q : Triangle) (J : DirectionParity → DirectionParity)
    (k : ℂ → ℂ → DirectionParity → ℝ) (f : DoublePhase → ℂ)
    (z : DoublePhase) : ℂ :=
  fiberKernel (volume.restrict Q.table) J k (associatedField f)
    (z.1.1,(z.1.2,z.2))

lemma doubleKernel_adjoint (Q : Triangle) {J : DirectionParity → DirectionParity}
    (hJ : MeasurePreserving J (angularMeasure.prod parityMeasure) (angularMeasure.prod parityMeasure))
    (hJe : MeasurableEmbedding J) (hJJ : Function.Involutive J)
    {k l : ℂ → ℂ → DirectionParity → ℝ}
    (hk : StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => k p.1.1 p.2 p.1.2))
    (hl : StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => l p.1.1 p.2 p.1.2))
    {K L : ℝ} (hK : ∀ x y c, |k x y c| ≤ K) (hL : ∀ x y c, |l x y c| ≤ L)
    (hs : ∀ x y c, k x y c = l y x (J c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q J k f z * conj (g z) ∂doubleMeasure Q) =
      ∫ z, f z * conj (doubleKernel Q J l g z) ∂doubleMeasure Q := by
  have : IsFiniteMeasure (volume.restrict Q.table) := ⟨by simpa using Q.area_lt_top⟩
  rw [double_integral_assoc, double_integral_assoc]
  congr 1
  exact fiberKernel_L2_adjoint hJ hJe hJJ hk hl hK hL hs
    (associatedField_stronglyMeasurable hfm) (associatedField_stronglyMeasurable hgm)
    (associatedField_memLp Q hf) (associatedField_memLp Q hg)

lemma doubleKernel_neg (Q : Triangle) (J : DirectionParity → DirectionParity)
    (k : ℂ → ℂ → DirectionParity → ℝ) (f : DoublePhase → ℂ) (z : DoublePhase) :
    doubleKernel Q J (fun x y c => -k x y c) f z = -doubleKernel Q J k f z := by
  simp only [doubleKernel, fiberKernel, neg_smul, integral_neg]

lemma doubleKernel_skew (Q : Triangle) {J : DirectionParity → DirectionParity}
    (hJ : MeasurePreserving J (angularMeasure.prod parityMeasure) (angularMeasure.prod parityMeasure))
    (hJe : MeasurableEmbedding J) (hJJ : Function.Involutive J)
    {k : ℂ → ℂ → DirectionParity → ℝ}
    (hk : StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => k p.1.1 p.2 p.1.2))
    {K : ℝ} (hK : ∀ x y c, |k x y c| ≤ K)
    (hs : ∀ x y c, k x y c = -k y x (J c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q J k f z * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (doubleKernel Q J k g z) ∂doubleMeasure Q) := by
  have h := doubleKernel_adjoint Q hJ hJe hJJ (l := fun x y c => -k x y c) hk hk.neg hK
    (fun x y c => by simpa only [abs_neg] using hK x y c) hs hfm hgm hf hg
  simpa only [doubleKernel_neg, map_neg, mul_neg, integral_neg] using h

end TriangularBilliards

end
end
end
end
end
end

end OAI
