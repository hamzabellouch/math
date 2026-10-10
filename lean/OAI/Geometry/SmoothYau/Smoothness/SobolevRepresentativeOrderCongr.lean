import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContinuousSobolevFirstDerivative

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scalarAffine_hasFDerivAt (p : E) (r : ℝ) (x : E) :
    HasFDerivAt (fun y : E => p + r • y) (r • ContinuousLinearMap.id ℝ E) x := by
  simpa only [Pi.smul_apply, id_eq] using
    ((hasFDerivAt_id x).const_smul r).const_add p

lemma fderiv_scalarAffine (p : E) (r : ℝ) (u : E → ℂ) (x v : E)
    (hu : DifferentiableAt ℝ u (p + r • x)) :
    fderiv ℝ (fun y => u (p + r • y)) x v =
      (r : ℂ) * fderiv ℝ u (p + r • x) v := by
  change fderiv ℝ (u ∘ (fun y => p + r • y)) x v = _
  rw [(hu.hasFDerivAt.comp x (scalarAffine_hasFDerivAt p r x)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]

lemma differentiable_directional {u : E → ℂ} (hu : ContDiff ℝ 2 u) (v : E) :
    Differentiable ℝ (fun x => fderiv ℝ u x v) :=
  (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero |>.clm_apply
    (differentiable_const v)

lemma second_fderiv_scalarAffine (p : E) (r : ℝ) {u : E → ℂ}
    (hu : ContDiff ℝ 2 u) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u (p + r • z)) y w) x v =
      (r : ℂ) ^ 2 * fderiv ℝ (fun y => fderiv ℝ u y w) (p + r • x) v := by
  have he : (fun y => fderiv ℝ (fun z => u (p + r • z)) y w) =
      fun y => (r : ℂ) * fderiv ℝ u (p + r • y) w := by
    funext y
    exact fderiv_scalarAffine p r u y w (hu.differentiable (by norm_num) _)
  rw [he]
  have hd := (differentiable_directional hu w) (p + r • x)
  have ha := scalarAffine_hasFDerivAt p r x
  erw [fderiv_const_mul (hd.comp x ha.differentiableAt) (r : ℂ),
    _root_.smul_apply, smul_eq_mul, fderiv_scalarAffine p r _ x v hd]
  ring

lemma second_fderiv_mul {u v : E → ℂ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiable (by norm_num)
  have hdv := hv.differentiable (by norm_num)
  have hdu' := differentiable_directional hu b
  have hdv' := differentiable_directional hv b
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =
      fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b := by
    funext y
    rw [fderiv_fun_mul (hdu y) (hdv y)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he]
  erw [fderiv_fun_add ((hdu x).mul (hdv' x)) ((hdv x).mul (hdu' x)),
    fderiv_fun_mul (hdu x) (hdv' x), fderiv_fun_mul (hdv x) (hdu' x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

end Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def euclideanElliptic (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (u : E → ℂ) (x : E) : ℂ :=
  (∑ i, ∑ j, (a i j x : ℂ) *
    fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i)) +
    ∑ i, (c i x : ℂ) * fderiv ℝ u x (b i)

lemma euclideanElliptic_mul (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {χ u : E → ℂ} (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : E) :
    euclideanElliptic b a c (fun y => χ y * u y) x =
      χ x * euclideanElliptic b a c u x + euclideanElliptic b a c χ x * u x +
      ∑ i, ∑ j, (a i j x : ℂ) *
        (fderiv ℝ χ x (b i) * fderiv ℝ u x (b j) +
          fderiv ℝ χ x (b j) * fderiv ℝ u x (b i)) := by
  simp only [euclideanElliptic, second_fderiv_mul hχ hu,
    fderiv_fun_mul (hχ.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x),
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm, mul_comm]
  ring

lemma euclideanElliptic_scalarAffine (b : ι → E)
    (a : ι → ι → E → ℝ) (c : ι → E → ℝ) (p : E) (r : ℝ)
    {u : E → ℂ} (hu : ContDiff ℝ 2 u) (x : E) :
    euclideanElliptic b (fun i j y => a i j (p + r • y))
      (fun i y => r * c i (p + r • y)) (fun y => u (p + r • y)) x =
      (r : ℂ) ^ 2 * euclideanElliptic b a c u (p + r • x) := by
  simp only [euclideanElliptic, second_fderiv_scalarAffine p r hu,
    fderiv_scalarAffine p r u x _ (hu.differentiable (by norm_num) _), Complex.ofReal_mul,
    mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma euclideanElliptic_congr (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {u v : E → ℂ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    euclideanElliptic b a c u x = euclideanElliptic b a c v x := by
  have hh (w : E) : (fun y => fderiv ℝ u y w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ v y w) :=
    h.fderiv.mono (fun _ hy => congrArg (fun L : E →L[ℝ] ℂ => L w) hy)
  simp only [euclideanElliptic, h.fderiv_eq, (hh _).fderiv_eq]

lemma second_fderiv_add_at {u v : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z + v z) y b) x a =
      fderiv ℝ (fun y => fderiv ℝ u y b) x a +
        fderiv ℝ (fun y => fderiv ℝ v y b) x a := by
  have he : (fun y => fderiv ℝ (fun z => u z + v z) y b) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y b + fderiv ℝ v y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y huy hvy
    rw [fderiv_fun_add (huy.differentiableAt (by norm_num)) (hvy.differentiableAt (by norm_num))]
    rfl
  rw [he.fderiv_eq]
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  have hdv := ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  rw [fderiv_fun_add hdu hdv]
  rfl

lemma euclideanElliptic_add_at (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {u v : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    euclideanElliptic b a c (fun y => u y + v y) x =
      euclideanElliptic b a c u x + euclideanElliptic b a c v x := by
  simp only [euclideanElliptic, second_fderiv_add_at hu hv,
    fderiv_fun_add (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num)),
    _root_.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma second_fderiv_const_mul_at (d : ℂ) {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => d * u z) y b) x a =
      d * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have he : (fun y => fderiv ℝ (fun z => d * u z) y b) =ᶠ[𝓝 x]
      (fun y => d * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    erw [fderiv_const_mul (hy.differentiableAt (by norm_num)) d]
    rfl
  rw [he.fderiv_eq]
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  erw [fderiv_const_mul hdu d]
  rfl

lemma euclideanElliptic_const_mul_at (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (d : ℂ) {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    euclideanElliptic b a c (fun y => d * u y) x = d * euclideanElliptic b a c u x := by
  simp only [euclideanElliptic, second_fderiv_const_mul_at d hu]
  erw [fderiv_const_mul (hu.differentiableAt (by norm_num)) d]
  simp only [_root_.smul_apply, smul_eq_mul, mul_left_comm _ d,
    ← Finset.mul_sum, ← mul_add]

lemma euclideanElliptic_zero (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ) (x : E) :
    euclideanElliptic b a c 0 x = 0 := by
  simp [euclideanElliptic]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma fderiv_inverseScalarAffine (p : E) (r : ℝ) {u : E → ℂ} (x v : E)
    (hu : DifferentiableAt ℝ u (r⁻¹ • (x - p))) :
    fderiv ℝ (fun y => u (r⁻¹ • (y - p))) x v =
      (r⁻¹ : ℝ) * fderiv ℝ u (r⁻¹ • (x - p)) v := by
  have ha : HasFDerivAt (fun y : E => r⁻¹ • (y - p))
      (r⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).sub_const p).const_smul r⁻¹
  change fderiv ℝ (u ∘ (fun y : E => r⁻¹ • (y - p))) x v = _
  rw [(hu.hasFDerivAt.comp x ha).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul]

lemma unscale_local_equation (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (p : E) {r : ℝ} (hr : r ≠ 0) (α : ℝ) {w : E → ℂ}
    (hw : ContDiff ℝ 2 w) (f : E → ℂ) (x : E)
    (he : ((α * r ^ 2 : ℝ) : ℂ) * w (r⁻¹ • (x - p)) -
      euclideanElliptic b (fun i j y => a i j (p + r • y))
        (fun i y => r * c i (p + r • y)) w (r⁻¹ • (x - p)) =
      (r : ℂ) ^ 2 * f x) :
    (α : ℂ) * w (r⁻¹ • (x - p)) -
      euclideanElliptic b a c (fun y => w (r⁻¹ • (y - p))) x = f x := by
  have hu : ContDiff ℝ 2 (fun y => w (r⁻¹ • (y - p))) := hw.comp (by fun_prop)
  have hh := euclideanElliptic_scalarAffine b a c p r hu (r⁻¹ • (x - p))
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, mul_inv_cancel₀ hr, one_smul, add_sub_cancel] at hh
  rw [hh] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr))
  calc
    (r : ℂ) ^ 2 * ((α : ℂ) * w (r⁻¹ • (x - p)) -
        euclideanElliptic b a c (fun y => w (r⁻¹ • (y - p))) x) =
      ((α * r ^ 2 : ℝ) : ℂ) * w (r⁻¹ • (x - p)) -
        (r : ℂ) ^ 2 * euclideanElliptic b a c (fun y => w (r⁻¹ • (y - p))) x := by
          push_cast
          ring
    _ = _ := he

def ellipticCommutator (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (χ u : E → ℂ) (x : E) : ℂ :=
  euclideanElliptic b a c χ x * u x + ∑ i, ∑ j, (a i j x : ℂ) *
    (fderiv ℝ χ x (b i) * fderiv ℝ u x (b j) +
      fderiv ℝ χ x (b j) * fderiv ℝ u x (b i))

lemma cutoff_parametrix_equation (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {χ u : E → ℂ} (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u)
    (α : ℝ) (f : E → ℂ)
    (he : ∀ x ∈ support χ, (α : ℂ) * u x - euclideanElliptic b a c u x = f x)
    (x : E) :
    (α : ℂ) * (χ x * u x) - euclideanElliptic b a c (fun y => χ y * u y) x =
      χ x * f x - ellipticCommutator b a c χ u x := by
  rw [euclideanElliptic_mul b a c hχ hu]
  have hh : χ x * ((α : ℂ) * u x - euclideanElliptic b a c u x) = χ x * f x := by
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul]
    · rw [he x hx]
  dsimp only [ellipticCommutator]
  linear_combination hh

lemma support_ellipticCommutator (b : ι → E) (a : ι → ι → E → ℝ)
    (c : ι → E → ℝ) (χ u : E → ℂ) :
    support (ellipticCommutator b a c χ u) ⊆ tsupport χ := by
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  have he : euclideanElliptic b a c χ x = 0 := by
    rw [euclideanElliptic_congr b a c (notMem_tsupport_iff_eventuallyEq.mp hn)]
    exact euclideanElliptic_zero b a c x
  exact hx (by simp only [ellipticCommutator, he, hd, zero_apply,
    zero_mul, add_zero, mul_zero, Finset.sum_const_zero])
lemma ellipticCommutator_congr_coeff (b : ι → E)
    (a a' : ι → ι → E → ℝ) (c c' : ι → E → ℝ) (χ u : E → ℂ)
    (ha : ∀ x ∈ tsupport χ, ∀ i j, a i j x = a' i j x)
    (hc : ∀ x ∈ tsupport χ, ∀ i, c i x = c' i x) (x : E) :
    ellipticCommutator b a c χ u x = ellipticCommutator b a' c' χ u x := by
  by_cases hx : x ∈ tsupport χ
  · simp only [ellipticCommutator, euclideanElliptic, ha x hx, hc x hx]
  · have h1 := mt (fun h => support_ellipticCommutator b a c χ u h) hx
    have h2 := mt (fun h => support_ellipticCommutator b a' c' χ u h) hx
    exact (notMem_support.mp h1).trans (notMem_support.mp h2).symm


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction
section FirstOrderSobolev
open scoped SchwartzMap BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma sobolevRepresentative_order_congr {s t : ℝ} (h : s = t)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * t)
    (u : FourierSobolevSpace E ℂ s) : sobolevRepresentative hs u = sobolevRepresentative ht u := by
  subst t
  rfl

def firstOrderSobolev {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (β₀ : 𝓢(E, ℂ)) (β : ι → 𝓢(E, ℂ)) (b : ι → E) :
    FourierSobolevSpace E ℂ (s + 1) →L[ℂ] FourierSobolevSpace E ℂ s :=
  (sobolevProduct hs (schwartzToSobolev s β₀)) ∘L
      sobolevInclusion (s + 1) s (by linarith) +
    ∑ i, (sobolevProduct hs (schwartzToSobolev s (β i))) ∘L
      sobolevDerivative (s + 1) (b i)

lemma firstOrderSobolev_representative {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (ht : Module.finrank ℝ E < 2 * (s + 1))
    (β₀ : 𝓢(E, ℂ)) (β : ι → 𝓢(E, ℂ)) (b : ι → E)
    (u : FourierSobolevSpace E ℂ (s + 1)) (x : E) :
    sobolevRepresentative hs (firstOrderSobolev hs β₀ β b u) x =
      β₀ x * sobolevRepresentative ht u x +
        ∑ i, β i x * fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
  have hd (i : ι) : sobolevRepresentative hs (sobolevDerivative (s + 1) (b i) u) x =
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
    convert sobolevDerivative_representative (s := s + 1)
      (by simpa only [add_sub_cancel_right] using hs) ht u (b i) x using 1
    exact congrArg (fun v : E →ᵇ ℂ => v x)
      (sobolevRepresentative_order_congr (s := s) (t := s + 1 - 1) (by ring) hs _ _)
  simp only [firstOrderSobolev, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum, sobolevRepresentative_product,
    sobolevRepresentative_schwartz, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply,
    SchwartzMap.toBoundedContinuousFunction_apply,
    sobolevInclusion_representative (s + 1) s (by linarith) ht hs, hd]
end FirstOrderSobolev

section CompactDifferentialCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma contDiff_directional {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) (b : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ χ x b) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma contDiff_euclideanElliptic (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (euclideanElliptic b a c χ) := by
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact (Complex.ofRealCLM.contDiff.comp (ha i j)).mul
      (contDiff_directional (contDiff_directional hχ (b j)) (b i))
  · apply ContDiff.sum
    intro i _
    exact (Complex.ofRealCLM.contDiff.comp (hc i)).mul (contDiff_directional hχ (b i))

lemma hasCompactSupport_euclideanElliptic (b : ι → E) (a : ι → ι → E → ℝ)
    (c : ι → E → ℝ) {χ : E → ℂ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (euclideanElliptic b a c χ) := by
  apply hχ.mono'
  intro x hx
  by_contra hn
  have hd : fderiv ℝ χ x = 0 := fderiv_of_notMem_tsupport ℝ hn
  have hdd (j : ι) : fderiv ℝ (fun y => fderiv ℝ χ y (b j)) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun hh => hn (tsupport_fderiv_apply_subset ℝ (b j) hh))
  exact hx (by simp only [euclideanElliptic, hd, hdd, zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero])

def ellipticCutoffSchwartz (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) : 𝓢(E, ℂ) :=
  (hasCompactSupport_euclideanElliptic b a c hχc).toSchwartzMap
    (contDiff_euclideanElliptic b a c ha hc hχ)

def cutoffDerivativeSchwartz {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (b : E) : 𝓢(E, ℂ) :=
  (show HasCompactSupport (fun x => (a x : ℂ) * fderiv ℝ χ x b) from
    (hχc.fderiv_apply ℝ b).mul_left).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp ha).mul (contDiff_directional hχ b))
@[simp] lemma cutoffDerivativeSchwartz_apply {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (b x : E) :
    cutoffDerivativeSchwartz hχ hχc ha b x = (a x : ℂ) * fderiv ℝ χ x b := rfl
end CompactDifferentialCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarAffineHomeomorph (p : E) (r : ℝ) (hr : r ≠ 0) : E ≃ₜ E where
  toFun x := p + r • x
  invFun x := r⁻¹ • (x - p)
  left_inv x := by simp [smul_smul, hr]
  right_inv x := by simp [smul_smul, hr]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma hasCompactSupport_comp_scalarAffine {χ : E → ℂ} (hχ : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) : HasCompactSupport (fun x => χ (p + r • x)) :=
  hχ.comp_homeomorph (scalarAffineHomeomorph p r hr)

def affineSchwartz (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢(E, ℂ) :=
  (hasCompactSupport_comp_scalarAffine hχc p r hr).toSchwartzMap (hχ.comp (by fun_prop))
@[simp] lemma affineSchwartz_apply (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) (x : E) :
    affineSchwartz χ hχ hχc p r hr x = χ (p + r • x) := rfl



end YauCounterexamples
end

end OAI
