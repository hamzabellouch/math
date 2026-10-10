import Mathlib
import OAI.Geometry.CubicTorus.Regularity.GradientCalibration

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
namespace CubicTorus

lemma coordinatePullback_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ x, ‖G x‖ ≤ 1) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ 1 + 2 * |t| * M := by
  have hu := hG (coordinateMove i f t x)
  have hd : ‖fderiv ℝ f x (G (coordinateMove i f t x))‖ ≤ M :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [hM x, norm_nonneg (fderiv ℝ f x)])
  calc
    _ ≤ ‖coordinateJacobian i f t x • G (coordinateMove i f t x)‖ +
        ‖(t * fderiv ℝ f x (G (coordinateMove i f t x))) • EuclideanSpace.single i 1‖ :=
      norm_sub_le _ _
    _ ≤ (1 + |t| * M) + |t| * M := by
      simp only [norm_smul, norm_mul]
      have he : ‖(EuclideanSpace.single i (1 : ℝ) : Cover)‖ = 1 := by simp
      rw [he, mul_one, Real.norm_eq_abs t]
      exact add_le_add
        (by simpa only [mul_one] using
          (mul_le_mul (coordinateJacobian_norm_le i hM t x) hu
            (norm_nonneg _) (by positivity)))
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

def fiberPoint (i : Fin 3) (x : Cover) (u : ℝ) : Cover :=
  x + (u - x i) • EuclideanSpace.single i 1

lemma fiberPoint_self (i : Fin 3) (x : Cover) : fiberPoint i x (x i) = x := by
  simp [fiberPoint]

lemma fiberPoint_apply_same (i : Fin 3) (x : Cover) (u : ℝ) : fiberPoint i x u i = u := by
  simp [fiberPoint]

lemma fiberPoint_apply_ne (i j : Fin 3) (hij : i ≠ j) (x : Cover) (u : ℝ) :
    fiberPoint i x u j = x j := by
  simp [fiberPoint, hij]

lemma norm_fiberPoint_sub (i : Fin 3) (x : Cover) (u v : ℝ) :
    ‖fiberPoint i x u - fiberPoint i x v‖ = |u - v| := by
  have he : fiberPoint i x u - fiberPoint i x v =
      (u - v) • EuclideanSpace.single i 1 := by
    unfold fiberPoint
    module
  rw [he, norm_smul]
  simp

lemma coordinateMove_fiber_strictMono (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) (x : Cover) :
    StrictMono (fun u : ℝ ↦ coordinateMove i f t (fiberPoint i x u) i) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro u v huv
  have hb := hLip.norm_sub_le (fiberPoint i x v) (fiberPoint i x u)
  rw [norm_fiberPoint_sub, Real.norm_eq_abs, abs_of_pos (sub_pos.2 huv)] at hb
  have hc := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  rw [← abs_mul] at hc
  have hd := (abs_le.1 hc).1
  simp only [coordinateMove_apply, fiberPoint_apply_same, ↓reduceIte]
  nlinarith [mul_pos (sub_pos.2 ht) (sub_pos.2 huv)]

lemma coordinateMove_mapsTo_cube (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) :
    MapsTo (coordinateMove i f t) fundamentalCube fundamentalCube := by
  intro x hx j
  by_cases hij : i = j
  · subst j
    have hmono := coordinateMove_fiber_strictMono i hf hM ht x
    have hzero : coordinateMove i f t (fiberPoint i x 0) i = 0 := by
      rw [coordinateMove_apply, fiberPoint_apply_same,
        hface _ (Or.inl (fiberPoint_apply_same i x 0))]
      simp
    have hone : coordinateMove i f t (fiberPoint i x 1) i = 1 := by
      rw [coordinateMove_apply, fiberPoint_apply_same,
        hface _ (Or.inr (fiberPoint_apply_same i x 1))]
      simp
    have hlo := hmono.monotone (hx i).1
    have hhi := hmono (hx i).2
    rw [hzero, fiberPoint_self] at hlo
    dsimp only at hhi
    rw [hone, fiberPoint_self] at hhi
    exact ⟨hlo, hhi⟩
  · simpa [coordinateMove_apply, hij] using hx j

lemma coordinateMove_image_cube (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) :
    coordinateMove i f t '' fundamentalCube = fundamentalCube := by
  apply Subset.antisymm (image_subset_iff.2 (coordinateMove_mapsTo_cube i hf hM hface ht))
  intro x hx
  let g : ℝ → ℝ := fun u ↦ coordinateMove i f t (fiberPoint i x u) i
  have hfp : Continuous (fiberPoint i x) :=
    continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  have hm : Continuous (coordinateMove i f t) :=
    continuous_id.add ((continuous_const.mul hf.continuous).smul continuous_const)
  have hg : Continuous g := (EuclideanSpace.proj i).continuous.comp (hm.comp hfp)
  have hzero : g 0 = 0 := by
    dsimp [g]
    rw [coordinateMove_apply, fiberPoint_apply_same,
      hface _ (Or.inl (fiberPoint_apply_same i x 0))]
    simp
  have hone : g 1 = 1 := by
    dsimp [g]
    rw [coordinateMove_apply, fiberPoint_apply_same,
      hface _ (Or.inr (fiberPoint_apply_same i x 1))]
    simp
  have hi : x i ∈ Icc (g 0) (g 1) := by
    rw [hzero, hone]
    exact ⟨(hx i).1, (hx i).2.le⟩
  obtain ⟨u, hu, hux⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hg.continuousOn hi
  have hu1 : u < 1 := by
    by_contra hn
    have : u = 1 := le_antisymm hu.2 (le_of_not_gt hn)
    subst u
    rw [hone] at hux
    linarith [(hx i).2]
  refine ⟨fiberPoint i x u, ?_, ?_⟩
  · intro j
    by_cases hij : i = j
    · subst j
      simpa only [fiberPoint_apply_same] using And.intro hu.1 hu1
    · simpa only [fiberPoint_apply_ne i j hij] using hx j
  · ext j
    by_cases hij : i = j
    · subst j
      exact hux
    · simp [coordinateMove_apply, hij, fiberPoint_apply_ne i j hij]

end CubicTorus

namespace CubicTorus

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

def coordinateRegion (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (E : Set Torus) : Set Torus :=
  representative ⁻¹' (coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E))

lemma measurableSet_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) :
    MeasurableSet (coordinateRegion i f t E) := by
  have hc : Continuous (coordinateMove i f t) :=
    continuous_id.add ((continuous_const.mul hf.continuous).smul continuous_const)
  exact (hc.measurableEmbedding (coordinateMove_injective i hf hM ht)).measurableSet_image'
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)) |>.preimage
      measurable_representative

lemma coordinateRegion_lift (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) (E : Set Torus) :
    fundamentalCube ∩ quotientMap ⁻¹' (coordinateRegion i f t E) =
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  ext x
  constructor
  · rintro ⟨hx, hE⟩
    change representative (quotientMap x) ∈
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E) at hE
    rwa [representative_quotientMap_of_mem hx] at hE
  · intro hx
    have hc : x ∈ fundamentalCube := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact coordinateMove_mapsTo_cube i hf hM hface ht hy.1
    refine ⟨hc, ?_⟩
    change representative (quotientMap x) ∈
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E)
    rwa [representative_quotientMap_of_mem hc]

lemma integral_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) (g : Cover → ℝ) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateRegion i f t E), g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        coordinateJacobian i f t x * g (coordinateMove i f t x) := by
  rw [coordinateRegion_lift i hf hM hface ht]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE))
    (fun x _ ↦ (coordinateMove_hasFDerivAt i (hf x) t).hasFDerivWithinAt)
    (coordinateMove_injective i hf hM ht).injOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [coordinateMoveDeriv_det, abs_of_pos (coordinateJacobian_pos i
    (fun y ↦ by exact_mod_cast hM y) ht x), smul_eq_mul]

lemma perimeter_coordinateRegion_le (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    perimeter (coordinateRegion i f t E) ≤
      ENNReal.ofReal (1 + 2 * |t| * M) * perimeter E := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter at ⊢
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_coordinateRegion i hfd hM hface ht hE]
  have hh := abs_flux_le_mul_perimeter hP
    (coordinatePullback_contDiff i hf t hG.1) (coordinatePullback_periodic i hp t hG.2.1)
    hC (coordinatePullback_norm_le i M.coe_nonneg hMr t hG.2.2)
  simp_rw [coordinatePullback_divergence i hf t hG.1] at hh
  calc
    _ ≤ ENNReal.ofReal ((1 + 2 * |t| * M) * (perimeter E).toReal) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hh)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hP]
      rfl

lemma finitePerimeter_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) : FinitePerimeter (coordinateRegion i f t E) := by
  refine ⟨(measurableSet_coordinateRegion i (hf.differentiable (by simp)) hM ht hE).nullMeasurableSet,
    (perimeter_coordinateRegion_le i hf hp hM hface ht hE hP).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top

end CubicTorus

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

lemma volume_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real (coordinateRegion i f t E) = torusVolume.real E +
      t * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hfd := hf.differentiable (by simp)
  have hi : IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube :=
    integrableOn_periodic_continuous
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun n x ↦ by rw [fderiv_periodic hp])
  have hv := integral_coordinateRegion i hfd hM hface ht hE (fun _ ↦ 1)
  simp only [mul_one, coordinateJacobian] at hv
  rw [integral_add (integrable_const 1) ((hi.mono_set inter_subset_left).const_mul t),
    integral_const_mul] at hv
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hv
  rw [realVolume_lift hE,
    realVolume_lift (measurableSet_coordinateRegion i hfd hM ht hE)]
  exact hv

theorem coordinate_variation (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    FinitePerimeter (coordinateRegion i f t E) ∧
    torusVolume.real (coordinateRegion i f t E) = torusVolume.real E +
      t * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f x (EuclideanSpace.single i 1) ∧
    (perimeter (coordinateRegion i f t E)).toReal ≤
      (1 + 2 * |t| * M) * (perimeter E).toReal := by
  refine ⟨finitePerimeter_coordinateRegion i hf hp hM hface ht hE hP,
    volume_coordinateRegion i hf hp hM hface ht hE, ?_⟩
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP)
    (perimeter_coordinateRegion_le i hf hp hM hface ht hE hP)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def coordinateCofactor (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x n : Cover) : Cover :=
  coordinateJacobian i f t x • n -
    (t * ⟪n, EuclideanSpace.single i 1⟫) • gradient f x

lemma inner_coordinatePullback (i : Fin 3) (f : Cover → ℝ) (t : ℝ)
    (G : Cover → Cover) (x n : Cover) :
    ⟪n, coordinatePullback i f t G x⟫ =
      ⟪coordinateCofactor i f t x n, G (coordinateMove i f t x)⟫ := by
  simp only [coordinatePullback, coordinateCofactor, inner_sub_right, real_inner_smul_right,
    inner_sub_left, real_inner_smul_left, inner_gradient_left]
  ring

lemma continuous_coordinateCofactor (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    Continuous (fun z : NormalBundle ↦ coordinateCofactor i f t z.1 z.2) := by
  unfold coordinateCofactor
  exact (((coordinateJacobian_contDiff i hf t).continuous.comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    ((continuous_const.mul ((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ)
      continuous_const)).smul ((gradient_contDiff hf).continuous.comp
        (continuous_subtype_val.comp continuous_fst)))

theorem perimeter_coordinateRegion_le_normalArea (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    perimeter (coordinateRegion i f t E) ≤
      ENNReal.ofReal (∫ z, ‖coordinateCofactor i f t z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_coordinateRegion i hfd hM hface ht hE]
  have hh := normalMeasure_flux hμ (coordinatePullback_contDiff i hf t hG.1)
    (coordinatePullback_periodic i hp t hG.2.1) hC
    (coordinatePullback_norm_le i M.coe_nonneg hMr t hG.2.2)
  simp_rw [coordinatePullback_divergence i hf t hG.1] at hh
  rw [← hh]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ (coordinatePullback_contDiff i hf t hG.1).continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_coordinateCofactor i hf t).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover), coordinatePullback i f t G z.1⟫ ≤ _
    rw [inner_coordinatePullback]
    exact (real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hG.2.2 _))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x n : Cover) : Cover :=
  fderiv ℝ f x (EuclideanSpace.single i 1) • n -
    ⟪n, EuclideanSpace.single i 1⟫ • gradient f x

lemma coordinateCofactor_eq (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x n : Cover) :
    coordinateCofactor i f t x n = n + t • coordinateNormalVelocity i f x n := by
  unfold coordinateCofactor coordinateJacobian coordinateNormalVelocity
  module

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

lemma hasDerivAt_norm_unit_line {n : Cover} (hn : ‖n‖ = 1) (a : Cover) :
    HasDerivAt (fun t : ℝ ↦ ‖n + t • a‖) ⟪n, a⟫ 0 := by
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add n
  have hs := hh.norm_sq.sqrt (by simp [hn])
  simpa only [id_eq, zero_smul, one_smul, add_zero, hn, one_pow, Real.sqrt_one, mul_one,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0),
    Real.sqrt_sq (norm_nonneg _)] using hs

lemma lipschitz_norm_line (n a : Cover) :
    LipschitzWith (Real.nnabs ‖a‖) (fun t : ℝ ↦ ‖n + t • a‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ ‖(n + x • a) - (n + y • a)‖ := dist_norm_norm_le _ _
    _ = (Real.nnabs ‖a‖ : ℝ) * dist x y := by
      rw [show (n + x • a) - (n + y • a) = (x - y) • a by module]
      simp [norm_smul, Real.norm_eq_abs, Real.dist_eq, mul_comm]

lemma hasDerivAt_integral_unit_line {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (n a : α → Cover) (hn : ∀ z, ‖n z‖ = 1)
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable (fun z ↦ ‖n z + t • a z‖) μ)
    (hint : Integrable (fun z ↦ ‖n z‖) μ)
    (hinner : AEStronglyMeasurable (fun z ↦ ⟪n z, a z⟫) μ)
    (ha : Integrable (fun z ↦ ‖a z‖) μ) :
    HasDerivAt (fun t : ℝ ↦ ∫ z, ‖n z + t • a z‖ ∂μ)
      (∫ z, ⟪n z, a z⟫ ∂μ) 0 := by
  have hi : Integrable (fun z ↦ ‖n z + (0 : ℝ) • a z‖) μ := by
    simpa only [zero_smul, add_zero] using hint
  have hL : ∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs ‖a z‖)
      (fun t : ℝ ↦ ‖n z + t • a z‖) univ :=
    Eventually.of_forall fun z ↦ (lipschitz_norm_line (n z) (a z)).lipschitzOnWith
  have hD : ∀ᵐ z ∂μ, HasDerivAt (fun t : ℝ ↦ ‖n z + t • a z‖) ⟪n z, a z⟫ 0 :=
    Eventually.of_forall fun z ↦ hasDerivAt_norm_unit_line (hn z) (a z)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip (s := univ)
    (F := fun t z ↦ ‖n z + t • a z‖) (bound := fun z ↦ ‖a z‖) (by simp)
    (Eventually.of_forall hmeas) hi hinner hL ha hD).2

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

lemma continuous_normalLine (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    Continuous (fun z : NormalBundle ↦ ‖(z.2 : Cover) +
      t • coordinateNormalVelocity i f z.1 z.2‖) := by
  exact (continuous_normalUnit.add
    ((continuous_const : Continuous (fun _ : NormalBundle ↦ t)).smul
      (continuous_coordinateNormalVelocity i hf))).norm

theorem hasDerivAt_normalArea (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (μ : FiniteMeasure NormalBundle) :
    HasDerivAt (fun t : ℝ ↦ ∫ z, ‖coordinateCofactor i f t z.1 z.2‖
      ∂(μ : Measure NormalBundle))
      (∫ z, ⟪(z.2 : Cover), coordinateNormalVelocity i f z.1 z.2⟫
        ∂(μ : Measure NormalBundle)) 0 := by
  simp_rw [coordinateCofactor_eq]
  refine hasDerivAt_integral_unit_line (fun z : NormalBundle ↦ (z.2 : Cover))
    (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2)
    (fun z ↦ z.2.property) ?_ ?_ ?_ ?_
  · exact fun t ↦ (continuous_normalLine i hf t).aestronglyMeasurable
  · exact continuous_normalUnit.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity i hf)).aestronglyMeasurable
  · exact (continuous_coordinateNormalVelocity i hf).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma normalArea_zero (i : Fin 3) (f : Cover → ℝ) (μ : FiniteMeasure NormalBundle) :
    (∫ z, ‖coordinateCofactor i f 0 z.1 z.2‖ ∂(μ : Measure NormalBundle)) = (μ.mass : ℝ) := by
  simp_rw [coordinateCofactor_eq, zero_smul, add_zero, fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const, smul_eq_mul, mul_one]
  rfl

theorem isMinimizerAt_coordinate_stationary {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (i : Fin 3) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    (hzero : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      fderiv ℝ f x (EuclideanSpace.single i 1)) = 0) :
    (∫ z, ⟪(z.2 : Cover), coordinateNormalVelocity i f z.1 z.2⟫
      ∂(μ : Measure NormalBundle)) = 0 := by
  have hlocal : IsLocalMin (fun t : ℝ ↦ ∫ z, ‖coordinateCofactor i f t z.1 z.2‖
      ∂(μ : Measure NormalBundle)) 0 := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * (M : ℝ) < 1 :=
      (continuous_abs.mul continuous_const).continuousAt.eventually
        (eventually_lt_nhds (by simp : |(0 : ℝ)| * (M : ℝ) < 1))
    filter_upwards [hsmall] with t ht
    rw [normalArea_zero, hμ.1]
    have hfin := finitePerimeter_coordinateRegion i hf hp hM hface ht hE hmin.1.2.ne
    have hvol : torusVolume (coordinateRegion i f t E) = torusVolume E := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change torusVolume.real (coordinateRegion i f t E) = torusVolume.real E
      rw [volume_coordinateRegion i hf hp hM hface ht hE, hzero, mul_zero, add_zero]
    have hleast := hmin.2.2 _ hfin (hvol.trans hmin.2.1)
    have harea := perimeter_coordinateRegion_le_normalArea i hf hp hM hface ht hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _)] using hh

  exact hlocal.hasDerivAt_eq_zero (hasDerivAt_normalArea i hf μ)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def directionalFlux (E : Set Torus) (i : Fin 3) (f : Cover → ℝ) : ℝ :=
  ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    fderiv ℝ f x (EuclideanSpace.single i 1)

lemma integrableOn_directionalDeriv (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) :=
    hf.smul contDiff_const
  have hi := integrableOn_divergence hFc
  have he : divergence (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) =
      fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact divergence_smul_const (hf.differentiable (by simp)).differentiableAt _
  rwa [he] at hi

lemma directionalFlux_add (E : Set Torus) (i : Fin 3) {f g : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    directionalFlux E i (fun x ↦ f x + g x) = directionalFlux E i f + directionalFlux E i g := by
  unfold directionalFlux
  change (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    fderiv ℝ (f + g) x (EuclideanSpace.single i 1)) = _
  simp only [fderiv_add (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt, add_apply]
  exact integral_add ((integrableOn_directionalDeriv i hf).mono_set inter_subset_left)
    ((integrableOn_directionalDeriv i hg).mono_set inter_subset_left)

structure WallVariation where
  coordinate : Fin 3
  function : Cover → ℝ
  bound : NNReal
  smooth : ContDiff ℝ (⊤ : ℕ∞) function
  periodic : ∀ n x, function (x + latticeVector n) = function x
  derivative_bound : ∀ x, ‖fderiv ℝ function x‖₊ ≤ bound
  faces : ∀ x, x coordinate = 0 ∨ x coordinate = 1 → function x = 0

lemma exists_wallVariation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0) :
    ∃ D : WallVariation, D.coordinate = i ∧ D.function = f := by
  obtain ⟨M, hM, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  refine ⟨⟨i, f, ⟨M, hM⟩, hf, hp, ?_, hface⟩, rfl, rfl⟩
  intro x
  exact_mod_cast hbound x

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinatePullback_smul (i : Fin 3) (f : Cover → ℝ) (t c : ℝ)
    (F : Cover → Cover) (x : Cover) :
    coordinatePullback i f t (fun y ↦ c • F y) x = c • coordinatePullback i f t F x := by
  simp only [coordinatePullback, map_smul, smul_sub, smul_smul]
  module

lemma coordinatePullback_norm_le_mul (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    {k : ℝ} (hk : 0 < k) (hG : ∀ x, ‖G x‖ ≤ k) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ (1 + 2 * |t| * M) * k := by
  have hnorm : ∀ y, ‖k⁻¹ • G y‖ ≤ 1 := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
    exact (mul_le_mul_of_nonneg_left (hG y) (inv_nonneg.mpr hk.le)).trans_eq
      (inv_mul_cancel₀ hk.ne')
  have hh := coordinatePullback_norm_le i hM0 hM t hnorm x
  rw [coordinatePullback_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hk.le)] at hh
  calc
    _ = k * (k⁻¹ * ‖coordinatePullback i f t G x‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ k * (1 + 2 * |t| * M) := mul_le_mul_of_nonneg_left hh hk.le
    _ = _ := mul_comm _ _

def doubleRegion (a b : WallVariation) (t s : ℝ) (E : Set Torus) : Set Torus :=
  coordinateRegion b.coordinate b.function s (coordinateRegion a.coordinate a.function t E)

def doubleCofactor (a b : WallVariation) (t s : ℝ) (x n : Cover) : Cover :=
  coordinateCofactor b.coordinate b.function s (coordinateMove a.coordinate a.function t x)
    (coordinateCofactor a.coordinate a.function t x n)

lemma continuous_doubleCofactor (a b : WallVariation) (t s : ℝ) :
    Continuous (fun z : NormalBundle ↦ doubleCofactor a b t s z.1 z.2) := by
  have hc := (coordinateMove_contDiff a.coordinate a.smooth t).continuous.comp
    (continuous_subtype_val.comp continuous_fst : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)))
  have hn := continuous_coordinateCofactor a.coordinate a.smooth t
  unfold doubleCofactor coordinateCofactor
  exact (((coordinateJacobian_contDiff b.coordinate b.smooth s).continuous.comp hc).smul hn).sub
    ((continuous_const.mul (hn.inner (𝕜 := ℝ) continuous_const)).smul
      ((gradient_contDiff b.smooth).continuous.comp hc))

theorem perimeter_doubleRegion_le_normalArea (a b : WallVariation) {t s : ℝ}
    (ht : |t| * (a.bound : ℝ) < 1) (hs : |s| * (b.bound : ℝ) < 1)
    {E : Set Torus} (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) :
    perimeter (doubleRegion a b t s E) ≤ ENNReal.ofReal
      (∫ z, ‖doubleCofactor a b t s z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  have hEa := measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
    a.derivative_bound ht hE
  have haM : ∀ x, ‖fderiv ℝ a.function x‖ ≤ (a.bound : ℝ) := fun x ↦ by
    exact_mod_cast a.derivative_bound x
  have hbM : ∀ x, ‖fderiv ℝ b.function x‖ ≤ (b.bound : ℝ) := fun x ↦ by
    exact_mod_cast b.derivative_bound x
  have hak : 0 < 1 + 2 * |t| * (a.bound : ℝ) := by positivity
  have hbk : 0 < 1 + 2 * |s| * (b.bound : ℝ) := by positivity
  unfold perimeter doubleRegion
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  let G := coordinatePullback b.coordinate b.function s F
  have hG := coordinatePullback_contDiff b.coordinate b.smooth s hF.1
  have hGp := coordinatePullback_periodic b.coordinate b.periodic s hF.2.1
  have hΓ := coordinatePullback_contDiff a.coordinate a.smooth t hG
  rw [integral_coordinateRegion b.coordinate (b.smooth.differentiable (by simp))
    b.derivative_bound b.faces hs hEa]
  simp_rw [← coordinatePullback_divergence b.coordinate b.smooth s hF.1]
  rw [integral_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
    a.derivative_bound a.faces ht hE]
  have hflux := normalMeasure_flux hμ hΓ
    (coordinatePullback_periodic a.coordinate a.periodic t hGp) (mul_pos hak hbk)
    (coordinatePullback_norm_le_mul a.coordinate a.bound.coe_nonneg haM t hbk
      (coordinatePullback_norm_le b.coordinate b.bound.coe_nonneg hbM s hF.2.2))
  simp_rw [coordinatePullback_divergence a.coordinate a.smooth t hG] at hflux
  change ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    coordinateJacobian a.coordinate a.function t x *
      divergence G (coordinateMove a.coordinate a.function t x)) ≤ _
  rw [← hflux]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ hΓ.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_doubleCofactor a b t s).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover), coordinatePullback a.coordinate a.function t G z.1⟫ ≤ _
    rw [inner_coordinatePullback]
    dsimp only [G]
    rw [inner_coordinatePullback]
    exact (real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 _))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma directionalDeriv_norm_le (a : WallVariation) (x : Cover) :
    ‖fderiv ℝ a.function x (EuclideanSpace.single a.coordinate 1)‖ ≤ (a.bound : ℝ) := by
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ a.function x)
    (EuclideanSpace.single a.coordinate 1)
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  exact h.trans (by exact_mod_cast a.derivative_bound x)

lemma gradient_norm_le (a : WallVariation) (x : Cover) :
    ‖gradient a.function x‖ ≤ (a.bound : ℝ) := by
  have h : ‖fderiv ℝ a.function x‖ ≤ (a.bound : ℝ) := by
    exact_mod_cast a.derivative_bound x
  simpa only [gradient, LinearIsometryEquiv.norm_map] using h

lemma coordinateNormalVelocity_norm_le (a : WallVariation) (x n : Cover) :
    ‖coordinateNormalVelocity a.coordinate a.function x n‖ ≤ 2 * (a.bound : ℝ) * ‖n‖ := by
  have hi : ‖⟪n, EuclideanSpace.single a.coordinate (1 : ℝ)⟫‖ ≤ ‖n‖ := by
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
      abs_real_inner_le_norm n (EuclideanSpace.single a.coordinate (1 : ℝ) : Cover)
  unfold coordinateNormalVelocity
  calc
    _ ≤ ‖fderiv ℝ a.function x (EuclideanSpace.single a.coordinate 1) • n‖ +
        ‖⟪n, EuclideanSpace.single a.coordinate 1⟫ • gradient a.function x‖ := norm_sub_le _ _
    _ ≤ (a.bound : ℝ) * ‖n‖ + ‖n‖ * (a.bound : ℝ) := by
      simp only [norm_smul]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (directionalDeriv_norm_le a x) (norm_nonneg _))
        (mul_le_mul hi (gradient_norm_le a x) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

def transportedFlux (a b : WallVariation) (E : Set Torus) (t : ℝ) : ℝ :=
  ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    coordinateJacobian a.coordinate a.function t x *
      fderiv ℝ b.function (coordinateMove a.coordinate a.function t x)
        (EuclideanSpace.single b.coordinate 1)

lemma transportedFlux_zero (a b : WallVariation) (E : Set Torus) :
    transportedFlux a b E 0 = directionalFlux E b.coordinate b.function := by
  simp only [transportedFlux, coordinateJacobian, zero_mul, add_zero, one_mul,
    coordinateMove, zero_smul, directionalFlux]

lemma continuousAt_transportedFlux (a b : WallVariation) (E : Set Torus) :
    ContinuousAt (transportedFlux a b E) 0 := by
  have hg : Continuous (fun x ↦ fderiv ℝ b.function x (EuclideanSpace.single b.coordinate 1)) :=
    (b.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmeas (t : ℝ) : Continuous (fun x ↦
      coordinateJacobian a.coordinate a.function t x *
        fderiv ℝ b.function (coordinateMove a.coordinate a.function t x)
          (EuclideanSpace.single b.coordinate 1)) :=
    (coordinateJacobian_contDiff a.coordinate a.smooth t).continuous.mul
      (hg.comp (coordinateMove_contDiff a.coordinate a.smooth t).continuous)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 :=
    (continuous_abs.continuousAt.eventually (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1))).mono
      fun _ h ↦ h.le
  have hbound : ∀ᶠ t : ℝ in 𝓝 0, ∀ x : Cover,
      ‖coordinateJacobian a.coordinate a.function t x *
        fderiv ℝ b.function (coordinateMove a.coordinate a.function t x)
          (EuclideanSpace.single b.coordinate 1)‖ ≤ (1 + (a.bound : ℝ)) * b.bound := by
    filter_upwards [hsmall] with t ht x
    rw [norm_mul]
    apply mul_le_mul _ (directionalDeriv_norm_le b _) (norm_nonneg _) (by positivity)
    exact (coordinateJacobian_norm_le a.coordinate (M := (a.bound : ℝ)) (fun y ↦ by
      exact_mod_cast a.derivative_bound y) t x).trans (by
        simpa only [one_mul] using add_le_add (le_refl (1 : ℝ))
          (mul_le_mul_of_nonneg_right ht a.bound.coe_nonneg))
  unfold transportedFlux
  apply continuousAt_of_dominated (bound := fun _ ↦ (1 + (a.bound : ℝ)) * b.bound)
    (Eventually.of_forall fun t ↦ (hmeas t).aestronglyMeasurable)
    (hbound.mono fun t ht ↦ Eventually.of_forall ht) (integrable_const _) ?_
  apply Eventually.of_forall
  intro x
  have hc : Continuous (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) := by
    exact continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  exact (((continuous_const.add (continuous_id.mul continuous_const)) :
    Continuous (fun t : ℝ ↦ coordinateJacobian a.coordinate a.function t x)).mul
    (hg.comp hc)).continuousAt

lemma volume_doubleRegion (a b : WallVariation) {t s : ℝ}
    (ht : |t| * (a.bound : ℝ) < 1) (hs : |s| * (b.bound : ℝ) < 1)
    {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real (doubleRegion a b t s E) = torusVolume.real E +
      t * directionalFlux E a.coordinate a.function + s * transportedFlux a b E t := by
  unfold doubleRegion
  rw [volume_coordinateRegion b.coordinate b.smooth b.periodic b.derivative_bound b.faces hs
    (measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
      a.derivative_bound ht hE)]
  rw [volume_coordinateRegion a.coordinate a.smooth a.periodic a.derivative_bound a.faces ht hE,
    integral_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
      a.derivative_bound a.faces ht hE]
  rfl

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_coordinateNormalVelocity_pair (a : WallVariation) :
    Continuous (fun p : Cover × Cover ↦
      coordinateNormalVelocity a.coordinate a.function p.1 p.2) := by
  unfold coordinateNormalVelocity
  exact ((((a.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    continuous_fst).smul continuous_snd).sub
    ((continuous_snd.inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff a.smooth).continuous.comp continuous_fst))

def doubleVelocityCoefficient (a b : WallVariation) (k t : ℝ) (x n : Cover) : Cover :=
  coordinateNormalVelocity a.coordinate a.function x n +
    k • coordinateNormalVelocity b.coordinate b.function
      (coordinateMove a.coordinate a.function t x)
      (n + t • coordinateNormalVelocity a.coordinate a.function x n)

lemma doubleCofactor_eq (a b : WallVariation) (k t : ℝ) (x n : Cover) :
    doubleCofactor a b t (t * k) x n = n + t • doubleVelocityCoefficient a b k t x n := by
  simp only [doubleCofactor, coordinateCofactor_eq, doubleVelocityCoefficient]
  module

lemma continuous_doubleVelocityCoefficient (a b : WallVariation) (k t : ℝ) :
    Continuous (fun z : NormalBundle ↦ doubleVelocityCoefficient a b k t z.1 z.2) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  have hn := continuous_normalUnit
  have hA := continuous_coordinateNormalVelocity a.coordinate a.smooth
  have hm := (coordinateMove_contDiff a.coordinate a.smooth t).continuous.comp hx
  unfold doubleVelocityCoefficient
  have ht : Continuous (fun _ : NormalBundle ↦ t) := continuous_const
  have hk : Continuous (fun _ : NormalBundle ↦ k) := continuous_const
  convert hA.add (hk.smul ((continuous_coordinateNormalVelocity_pair b).comp
      (hm.prodMk (hn.add (ht.smul hA))))) using 1
  ext z j
  rfl

lemma continuous_velocityAlong (a b : WallVariation) (x n : Cover) :
    Continuous (fun t : ℝ ↦ coordinateNormalVelocity b.coordinate b.function
      (coordinateMove a.coordinate a.function t x)
      (n + t • coordinateNormalVelocity a.coordinate a.function x n)) := by
  have hm : Continuous (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  have hn : Continuous (fun t : ℝ ↦ n + t • coordinateNormalVelocity a.coordinate a.function x n) :=
    continuous_const.add (continuous_id.smul continuous_const)
  simpa! only [Function.comp_def] using
    (continuous_coordinateNormalVelocity_pair b).comp (hm.prodMk hn)

lemma continuousAt_doubleVelocityCoefficient (a b : WallVariation) {k : ℝ → ℝ}
    (hk : ContinuousAt k 0) (x n : Cover) :
    ContinuousAt (fun t ↦ doubleVelocityCoefficient a b (k t) t x n) 0 := by
  exact continuousAt_const.add (hk.smul (continuous_velocityAlong a b x n).continuousAt)

lemma doubleVelocityCoefficient_norm_le (a b : WallVariation) {k t K : ℝ}
    (ht : |t| ≤ 1) (hk : |k| ≤ K) (x : Cover) {n : Cover} (hn : ‖n‖ = 1) :
    ‖doubleVelocityCoefficient a b k t x n‖ ≤
      2 * (a.bound : ℝ) + K * (2 * (b.bound : ℝ) * (1 + 2 * (a.bound : ℝ))) := by
  have hK : 0 ≤ K := (abs_nonneg k).trans hk
  have hA : ‖coordinateNormalVelocity a.coordinate a.function x n‖ ≤ 2 * (a.bound : ℝ) := by
    simpa only [hn, mul_one] using coordinateNormalVelocity_norm_le a x n
  have hn' : ‖n + t • coordinateNormalVelocity a.coordinate a.function x n‖ ≤
      1 + 2 * (a.bound : ℝ) := by
    calc
      _ ≤ ‖n‖ + ‖t • coordinateNormalVelocity a.coordinate a.function x n‖ := norm_add_le _ _
      _ ≤ 1 + 1 * (2 * (a.bound : ℝ)) := by
        rw [hn, norm_smul, Real.norm_eq_abs]
        exact add_le_add (le_refl (1 : ℝ))
          (mul_le_mul ht hA (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hB := (coordinateNormalVelocity_norm_le b
    (coordinateMove a.coordinate a.function t x)
    (n + t • coordinateNormalVelocity a.coordinate a.function x n)).trans
    (mul_le_mul_of_nonneg_left hn' (by positivity))
  unfold doubleVelocityCoefficient
  calc
    _ ≤ ‖coordinateNormalVelocity a.coordinate a.function x n‖ +
      ‖k • coordinateNormalVelocity b.coordinate b.function
        (coordinateMove a.coordinate a.function t x)
        (n + t • coordinateNormalVelocity a.coordinate a.function x n)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hA (mul_le_mul hk hB (norm_nonneg _) hK)

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma hasDerivAt_smul_continuous_zero {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {b : ℝ → H} (hb : ContinuousAt b 0) :
    HasDerivAt (fun t : ℝ ↦ t • b t) (b 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hb.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  simp [slope_def_module, ht0]

lemma hasDerivAt_norm_unit_perturbation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : H} (hn : ‖n‖ = 1) {b : ℝ → H}
    (hb : ContinuousAt b 0) :
    HasDerivAt (fun t : ℝ ↦ ‖n + t • b t‖) ⟪n, b 0⟫ 0 := by
  have hh := (hasDerivAt_smul_continuous_zero hb).const_add n
  have hs := hh.norm_sq.sqrt (by simp [hn])
  simpa only [zero_smul, add_zero, hn, one_pow, Real.sqrt_one, mul_one,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0),
    Real.sqrt_sq (norm_nonneg _)] using hs

lemma norm_slope_unit_perturbation_le {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (n : H) (b : ℝ → H) (t : ℝ) :
    ‖slope (fun u : ℝ ↦ ‖n + u • b u‖) 0 t‖ ≤ ‖b t‖ := by
  by_cases ht : t = 0
  · simp [ht]
  simp only [slope_def_module, sub_zero, zero_smul, add_zero, norm_smul]
  calc
    ‖t⁻¹‖ * ‖‖n + t • b t‖ - ‖n‖‖ ≤ ‖t⁻¹‖ * ‖(n + t • b t) - n‖ :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
        (abs_norm_sub_norm_le (n + t • b t) n)) (norm_nonneg _)
    _ = ‖b t‖ := by
      rw [add_sub_cancel_left, norm_smul, norm_inv, ← mul_assoc,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht), one_mul]

lemma hasDerivAt_integral_norm_perturbation {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {μ : Measure α}
    (n : α → H) (b : ℝ → α → H) (hn : ∀ z, ‖n z‖ = 1)
    (hint : ∀ t : ℝ, Integrable (fun z ↦ ‖n z + t • b t z‖) μ)
    (hcont : ∀ᵐ z ∂μ, ContinuousAt (fun t ↦ b t z) 0)
    (C : α → ℝ) (hC : Integrable C μ)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ z ∂μ, ‖b t z‖ ≤ C z) :
    HasDerivAt (fun t : ℝ ↦ ∫ z, ‖n z + t • b t z‖ ∂μ)
      (∫ z, ⟪n z, b 0 z⟫ ∂μ) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun z ↦ slope (fun u : ℝ ↦ ‖n z + u • b u z‖) 0 t) μ := by
    intro t
    simp only [slope_def_module, sub_zero]
    exact ((hint t).aestronglyMeasurable.sub (hint 0).aestronglyMeasurable).const_smul (t⁻¹ : ℝ)
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ z ∂μ,
      ‖slope (fun u : ℝ ↦ ‖n z + u • b u z‖) 0 t‖ ≤ C z := by
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with t ht
    exact ht.mono fun z hz ↦ (norm_slope_unit_perturbation_le (n z) (fun u ↦ b u z) t).trans hz
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun t : ℝ ↦ slope (fun u : ℝ ↦ ‖n z + u • b u z‖) 0 t)
      (𝓝[≠] 0) (𝓝 ⟪n z, b 0 z⟫) := by
    filter_upwards [hcont] with z hz
    exact (hasDerivAt_norm_unit_perturbation (hn z) hz).tendsto_slope
  have h := tendsto_integral_filter_of_dominated_convergence C
    (Eventually.of_forall hmeas) hb hC hlim
  apply h.congr'
  filter_upwards [] with t
  simp only [slope_def_module, sub_zero, integral_smul, integral_sub (hint t) (hint 0)]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

end CubicTorus
end
end
end

end OAI
