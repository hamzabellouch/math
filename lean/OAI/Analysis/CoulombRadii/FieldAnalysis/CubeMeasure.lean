import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CosineWeight

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
section TensorNeumann
variable {A ι : Type*} [MeasurableSpace A] {ν : Measure A} [SigmaFinite ν]

lemma tensorPair_inner {v v' : ℝ → ℂ} {w w' : A → ℂ} {b : ℝ}
    (_hv : MemLp v 2 (volume.restrict (Ioc 0 b)))
    (_hv' : MemLp v' 2 (volume.restrict (Ioc 0 b)))
    (_hw : MemLp w 2 ν) (_hw' : MemLp w' 2 ν) :
    (∫ z : A × ℝ, star (w z.1 * v z.2) * (w' z.1 * v' z.2)
      ∂(ν.prod (volume.restrict (Ioc 0 b)))) =
      (∫ a, star (w a) * w' a ∂ν) *
        (∫ x in Ioc 0 b, star (v x) * v' x) := by
  have he (z : A × ℝ) : star (w z.1 * v z.2) * (w' z.1 * v' z.2) =
      (star (w z.1) * w' z.1) * (star (v z.2) * v' z.2) := by
    rw [star_mul]; ring
  simp_rw [he]
  exact integral_prod_mul (fun a => star (w a) * w' a)
    (fun x => star (v x) * v' x)

lemma neumann_tensor_coefficient_derivative {b : ℝ} (hb : 0 < b)
    {f g : A × ℝ → ℂ} {w : A → ℂ}
    (hw : MemLp w 2 ν)
    (hf : MemLp f 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hg : MemLp g 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hd : ∀ᵐ a ∂ν, ∀ x ∈ Icc 0 b,
      HasDerivAt (fun t => f (a,t)) (g (a,x)) x) (n : ℕ) :
    (((((n : ℝ) + 1) * Real.pi / b : ℝ)) : ℂ) *
      (∫ z, star (w z.1 * neumannMode b (n+1) z.2) * f z
        ∂(ν.prod (volume.restrict (Ioc 0 b)))) =
      -(∫ z, star (w z.1 * dirichletMode b n z.2) * g z
        ∂(ν.prod (volume.restrict (Ioc 0 b)))) := by
  rw [integral_tensorPair hw (neumannMode_memLp b (n+1)) hf,
    integral_tensorPair hw (dirichletMode_memLp b n) hg,
    ← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hd, memLp_fiber_ae hg] with a hda hga
  have he := neumann_coefficient_derivative hb hda hga n
  dsimp only [fiberContract]
  calc
    _ = star (w a) * (((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) *
        (∫ t in Ioc 0 b, star (neumannMode b (n+1) t) * f (a,t))) := by ring
    _ = _ := by rw [he]; ring

theorem neumann_tensor_smooth_spectral_lower [DecidableEq ι] {b : ℝ} (hb : 0 < b)
    (w : ι → A → ℂ) (hw : ∀ i, MemLp (w i) 2 ν)
    (ho : ∀ i j, (∫ a, star (w i a) * w j a ∂ν) = if i = j then (1 : ℂ) else 0)
    {f g : A × ℝ → ℂ}
    (hf : MemLp f 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hg : MemLp g 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hd : ∀ᵐ a ∂ν, ∀ x ∈ Icc 0 b,
      HasDerivAt (fun t => f (a,t)) (g (a,x)) x) (s : Finset (ι × ℕ)) :
    ∑ q ∈ s, ((((q.2 : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ z, star (w q.1 z.1 * neumannMode b (q.2+1) z.2) * f z
        ∂(ν.prod (volume.restrict (Ioc 0 b)))‖^2) ≤
      ∫ z, ‖g z‖^2 ∂(ν.prod (volume.restrict (Ioc 0 b))) := by
  classical
  let u : (ι × ℕ) → Lp ℂ 2 (ν.prod (volume.restrict (Ioc 0 b))) :=
    fun q => (tensorPair_memLp (hw q.1) (dirichletMode_memLp b q.2)).toLp
      (fun z => w q.1 z.1 * dirichletMode b q.2 z.2)
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro q r
    rw [inner_toLp_complex, tensorPair_inner (dirichletMode_memLp b q.2)
      (dirichletMode_memLp b r.2) (hw q.1) (hw r.1), ho, dirichletMode_orthonormal hb]
    by_cases h1 : q.1 = r.1 <;> by_cases h2 : q.2 = r.2 <;>
      simp [h1, h2, Prod.ext_iff]
  have hB := hu.sum_inner_products_le (hg.toLp g) (s := s)
  rw [norm_toLp_sq_complex hg] at hB
  convert hB using 1
  apply Finset.sum_congr rfl
  intro q _
  rw [inner_toLp_complex]
  have he := neumann_tensor_coefficient_derivative hb (hw q.1) hf hg hd q.2
  have hnorm := congrArg (fun z : ℂ => ‖z‖^2) he
  simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs] using hnorm

end TensorNeumann

noncomputable def cubeMeasure (b : ℝ) (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => volume.restrict (Ioc 0 b)

instance cubeMeasure_isFiniteMeasure (b : ℝ) (d : ℕ) : IsFiniteMeasure (cubeMeasure b d) := by
  unfold cubeMeasure
  infer_instance

noncomputable def cubeMode {d : ℕ} (b : ℝ) (q : Fin d → ℕ) (x : Fin d → ℝ) : ℂ :=
  ∏ i, neumannMode b (q i) (x i)

noncomputable def splitCube {d : ℕ} (i : Fin (d+1)) :
    (Fin (d+1) → ℝ) ≃ᵐ ((Fin d → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).trans
    (MeasurableEquiv.prodComm (α := ℝ) (β := Fin d → ℝ))

lemma splitCube_measurePreserving {b : ℝ} {d : ℕ} (i : Fin (d+1)) :
    MeasurePreserving (splitCube i) (cubeMeasure b (d+1))
      ((cubeMeasure b d).prod (volume.restrict (Ioc 0 b))) := by
  exact Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => volume.restrict (Ioc 0 b)) i)

lemma splitCube_symm_apply {d : ℕ} (i : Fin (d+1)) (x : Fin d → ℝ) (t : ℝ) :
    (splitCube i).symm (x,t) = Fin.insertNth i t x := rfl

lemma splitCube_apply {d : ℕ} (i : Fin (d+1)) (x : Fin (d+1) → ℝ) :
    splitCube i x = ((fun j => x (i.succAbove j)), x i) := rfl

lemma cubeMode_insertNth {d : ℕ} (b : ℝ) (i : Fin (d+1))
    (q : Fin d → ℕ) (m : ℕ) (x : Fin (d+1) → ℝ) :
    cubeMode b (Fin.insertNth i m q) x =
      cubeMode b q ((splitCube i x).1) * neumannMode b m ((splitCube i x).2) := by
  rw [splitCube_apply, cubeMode, Fin.prod_univ_succAbove _ i]
  simp [cubeMode, mul_comm]

theorem cube_smooth_axis_spectral_lower {d : ℕ} {b : ℝ} (hb : 0 < b)
    (i : Fin (d+1)) {f g : (Fin (d+1) → ℝ) → ℂ}
    (hf : MemLp f 2 (cubeMeasure b (d+1)))
    (hg : MemLp g 2 (cubeMeasure b (d+1)))
    (hd : ∀ᵐ x ∂(cubeMeasure b d), ∀ t ∈ Icc 0 b,
      HasDerivAt (fun v => f (Fin.insertNth i v x)) (g (Fin.insertNth i t x)) t)
    (s : Finset ((Fin d → ℕ) × ℕ)) :
    ∑ q ∈ s, ((((q.2 : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b (Fin.insertNth i (q.2+1) q.1) x) * f x
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∫ x, ‖g x‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  have hp := splitCube_measurePreserving (b := b) i
  have hps := MeasurePreserving.symm (splitCube i) hp
  have hm : ∀ q : Fin d → ℕ, MemLp (cubeMode b q) 2 (cubeMeasure b d) :=
    fun q => scalarTensor_memLp (neumannMode b) (neumannMode_memLp b) q
  have ho : ∀ q r : Fin d → ℕ,
      (∫ x, star (cubeMode b q x) * cubeMode b r x ∂(cubeMeasure b d)) =
        if q = r then (1 : ℂ) else 0 :=
    by
      intro q r
      have h := scalarTensor_orthonormal (μ := volume.restrict (Ioc 0 b)) (neumannMode b)
        (by intro m n; by_cases h : m = n <;>
             simpa only [h, ite_true, ite_false] using neumannMode_orthonormal hb m n) q r
      by_cases he : q = r <;>
         simpa only [cubeMode, cubeMeasure, he, ite_true, ite_false] using h
  have H := neumann_tensor_smooth_spectral_lower hb (cubeMode b) hm ho
    (hf.comp_measurePreserving hps) (hg.comp_measurePreserving hps)
    (by simpa only [Function.comp_apply, splitCube_symm_apply] using hd) s
  have he (q : (Fin d → ℕ) × ℕ) :
      (∫ z, star (cubeMode b q.1 z.1 * neumannMode b (q.2+1) z.2) *
        f ((splitCube i).symm z) ∂((cubeMeasure b d).prod (volume.restrict (Ioc 0 b)))) =
      ∫ x, star (cubeMode b (Fin.insertNth i (q.2+1) q.1) x) * f x
        ∂(cubeMeasure b (d+1)) := by
    have hh := hp.integral_comp' (fun z => star (cubeMode b q.1 z.1 *
      neumannMode b (q.2+1) z.2) * f ((splitCube i).symm z))
    simpa only [(splitCube i).symm_apply_apply, ← cubeMode_insertNth] using hh.symm
  simp only [Function.comp_apply] at H
  simp_rw [he] at H
  rw [hps.integral_comp' (fun x => ‖g x‖^2)] at H
  exact H

open Filter
lemma inner_toLp_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

lemma norm_toLp_sq_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_real]
  simp only [pow_two]

lemma integral_mul_sq_le {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  rw [← inner_toLp_real hf hg, ← norm_toLp_sq_real hf, ← norm_toLp_sq_real hg,
    ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2

lemma integral_norm_sq_le_measure {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] {μ : Measure A} [IsFiniteMeasure μ]
    {f : A → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ)^2 ≤ (∫ x, ‖f x‖^2 ∂μ) * μ.real univ := by
  have h := integral_mul_sq_le hf.norm (memLp_const (1 : ℝ) : MemLp (fun _ : A => (1 : ℝ)) 2 μ)
  simpa using h

lemma unifIntegrable_of_sq_bound {A E ι : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] {μ : Measure A} [IsFiniteMeasure μ]
    {F : ι → A → E} (hF : ∀ i, MemLp (F i) 2 μ) {C : ℝ}
    (hC : 0 < C) (hb : ∀ i, (∫ x, ‖F i x‖^2 ∂μ) ≤ C) :
    UnifIntegrable F 1 μ := by
  apply unifIntegrable_iff'.2
  intro threshold hthreshold
  by_cases htop : threshold = ⊤
  · subst threshold
    exact ⟨1, by norm_num, fun _ _ _ _ => le_top⟩
  let epsilon := threshold.toReal
  have hepsilon : 0 < epsilon := ENNReal.toReal_pos hthreshold.ne' htop
  refine ⟨ENNReal.ofReal (epsilon^2 / C),
    ENNReal.ofReal_pos.mpr (div_pos (sq_pos_of_pos hepsilon) hC), ?_⟩
  intro i s _hs hμs
  rw [eLpNorm_one_eq_lintegral_enorm ((hF i).restrict s).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm ((hF i).restrict s |>.integrable (by norm_num)),
    ← ENNReal.ofReal_toReal htop]
  apply ENNReal.ofReal_le_ofReal
  have h := integral_norm_sq_le_measure ((hF i).restrict s)
  have hm : (μ.restrict s).real univ ≤ epsilon^2 / C := by
    rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hμs
  have hI : (∫ x in s, ‖F i x‖^2 ∂μ) ≤ C := by
    exact (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hF i).norm.integrable_sq).trans (hb i)
  have hn : 0 ≤ (μ.restrict s).real univ := ENNReal.toReal_nonneg
  have he : (∫ x in s, ‖F i x‖ ∂μ)^2 ≤ epsilon^2 := by
    calc
      _ ≤ (∫ x in s, ‖F i x‖^2 ∂μ) * (μ.restrict s).real univ := h
      _ ≤ C * (epsilon^2 / C) := mul_le_mul hI hm hn hC.le
      _ = epsilon^2 := by field_simp
  change (∫ x in s, ‖F i x‖ ∂μ) ≤ epsilon
  nlinarith [sq_nonneg ((∫ x in s, ‖F i x‖ ∂μ) - epsilon)]

lemma integral_le_of_ae_tendsto_of_frequently_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} {F : ℕ → X → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hF : ∀ n, Integrable (F n) μ)
    (hn : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x)))
    (hC : ∃ᶠ n in atTop, (∫ x, F n x ∂μ) ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  have hCn : 0 ≤ C := by
    obtain ⟨n, hn'⟩ := hC.exists
    exact (integral_nonneg (hn n)).trans hn'
  apply (ENNReal.ofReal_le_ofReal_iff hCn).1
  rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0)]
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le (hu_le := isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
      apply hC.mono
      intro n hn'
      rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Eventually.of_forall (hn n))]
      exact ENNReal.ofReal_le_ofReal hn'

theorem tendsto_integral_sq_sub_of_ae_of_sq_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} {F : ℕ → X → ℝ}
    (hf : MemLp f 2 μ) (hF : ∀ n, MemLp (F n) 2 μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x)))
    (hb : ∀ n, (∫ x, (F n x)^2 ∂μ) ≤ ∫ x, (f x)^2 ∂μ) :
    Tendsto (fun n => ∫ x, (F n x - f x)^2 ∂μ) atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun x => sq_nonneg _)
  · intro ε hε
    by_contra hh
    have hfreq : ∃ᶠ n in atTop, ε ≤ ∫ x, (F n x - f x)^2 ∂μ := by
      simpa only [not_lt] using (not_eventually.mp hh)
    have hI (n : ℕ) :
        (∫ x, (F n x + f x)^2 ∂μ) + (∫ x, (F n x - f x)^2 ∂μ) =
        2 * (∫ x, (F n x)^2 ∂μ) + 2 * (∫ x, (f x)^2 ∂μ) := by
      have hp : Integrable (fun x => (F n x + f x)^2) μ := ((hF n).add hf).integrable_sq
      have hm : Integrable (fun x => (F n x - f x)^2) μ := ((hF n).sub hf).integrable_sq
      rw [← integral_add hp hm, ← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hF n).integrable_sq.const_mul 2) (hf.integrable_sq.const_mul 2)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    have hlt := integral_le_of_ae_tendsto_of_frequently_le μ
      (f := fun x => (2 * f x)^2) (F := fun n x => (F n x + f x)^2)
      (C := 4 * (∫ x, (f x)^2 ∂μ) - ε)
      (hf.const_mul 2).integrable_sq (fun n => ((hF n).add hf).integrable_sq)
      (fun n x => sq_nonneg _) (fun x => sq_nonneg _) ?_ ?_
    · have he : (∫ x, (2 * f x)^2 ∂μ) = 4 * ∫ x, (f x)^2 ∂μ := by
        simp_rw [mul_pow]
        norm_num
        rw [integral_const_mul]
      rw [he] at hlt
      linarith
    · filter_upwards [ht] with x hx
      simpa only [two_mul] using (hx.add_const (f x)).pow 2
    · apply hfreq.mono
      intro n hn
      linarith [hI n, hb n]

open scoped Convolution
open ContinuousLinearMap

lemma euclidean_convolution_sq_le {I : Type*} [Fintype I] (κ u : EuclideanSpace ℝ I → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2))
    (x : EuclideanSpace ℝ I) :
    ((κ ⋆ u) x)^2 ≤ (κ ⋆ (fun x => (u x)^2)) x := by
  have h1 : Integrable (fun y => κ (x-y) * u y) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu hκ x
  have h2 : Integrable (fun y => κ (x-y) * (u y)^2) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu2.locallyIntegrable hκ x
  have h0 : Integrable (fun y => κ (x-y)) :=
    (hκ.integrable_of_hasCompactSupport hκC).comp_sub_left x
  have heq : (∫ y, κ (x-y) * u y) = (κ ⋆ u) x := by
    rw [convolution_eq_swap]
    rfl
  have heq0 : (∫ y, κ (x-y)) = 1 := by
    rw [integral_sub_left_eq_self, hκI]
  have hm : (∫ y, (2 * (κ ⋆ u) x) * (κ (x-y) * u y) -
      ((κ ⋆ u) x)^2 * κ (x-y)) ≤ ∫ y, κ (x-y) * (u y)^2 := by
    apply integral_mono ((h1.const_mul _).sub (h0.const_mul _)) h2
    intro y
    simp only [Pi.sub_apply]
    nlinarith [mul_nonneg (hκn (x-y)) (sq_nonneg (u y - (κ ⋆ u) x))]
  rw [integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
    integral_const_mul, heq, heq0] at hm
  have heq2 : (κ ⋆ (fun x => (u x)^2)) x = ∫ y, κ (x-y) * (u y)^2 := by
    rw [convolution_eq_swap]
    rfl
  rw [heq2]
  nlinarith

lemma euclidean_convolution_sq_integral_le {I : Type*} [Fintype I] (κ u : EuclideanSpace ℝ I → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2)) :
    Integrable (fun x => ((κ ⋆ u) x)^2) ∧
    (∫ x, ((κ ⋆ u) x)^2) ≤ ∫ x, (u x)^2 := by
  have hdom : Integrable (κ ⋆ (fun x => (u x)^2)) :=
    (hκ.integrable_of_hasCompactSupport hκC).integrable_convolution (lsmul ℝ ℝ) hu2
  have hcont : Continuous (κ ⋆ u) :=
    hκC.continuous_convolution_left (lsmul ℝ ℝ) hκ hu
  have hsq : Integrable (fun x => ((κ ⋆ u) x)^2) := by
    apply hdom.mono' (hcont.pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact euclidean_convolution_sq_le κ u hκ hκC hκn hκI hu hu2 x
  refine ⟨hsq, ?_⟩
  calc
    _ ≤ ∫ x, (κ ⋆ (fun x => (u x)^2)) x :=
      integral_mono hsq hdom (euclidean_convolution_sq_le κ u hκ hκC hκn hκI hu hu2)
    _ = _ := by
      rw [integral_convolution (lsmul ℝ ℝ)
        (hκ.integrable_of_hasCompactSupport hκC) hu2, hκI]
      simp

lemma euclidean_real_convolution_comm {I : Type*} [Fintype I] (u κ : EuclideanSpace ℝ I → ℝ) :
    u ⋆ κ = κ ⋆ u := by
  ext x
  rw [convolution_eq_swap, convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

lemma euclidean_fderiv_const_sub_comp {I : Type*} [Fintype I] (κ : EuclideanSpace ℝ I → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (x y v : EuclideanSpace ℝ I) :
    fderiv ℝ (fun z => κ (x - z)) y v = -(fderiv ℝ κ (x-y) v) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma euclidean_weak_convolution_partial {I : Type*} [Fintype I] (u g κ : EuclideanSpace ℝ I → ℝ)
    (v : EuclideanSpace ℝ I) (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκC : HasCompactSupport κ)
    (hw : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : EuclideanSpace ℝ I) :
    fderiv ℝ (κ ⋆ u) x v = (κ ⋆ g) x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hφC : HasCompactSupport (fun y => κ (x-y)) :=
    hκC.comp_homeomorph (Homeomorph.subLeft x)
  have ht := hw (fun y => κ (x-y)) hφ hφC
  simp_rw [euclidean_fderiv_const_sub_comp κ hκ x] at ht
  simp only [mul_neg, integral_neg, neg_inj] at ht
  rw [euclidean_real_convolution_comm κ u,
    (hκC.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hκ.of_le (by simp)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hκC.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x v]
  rw [euclidean_real_convolution_comm κ g]
  simpa only [convolution_def, lsmul_apply, smul_eq_mul] using ht

noncomputable def euclideanMollifier {I : Type*} [Fintype I] (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ I) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

lemma euclideanMollifier_tendsto {I : Type*} [Fintype I] :
    Filter.Tendsto (fun k => (euclideanMollifier (I := I) k).rOut) Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [euclideanMollifier, mul_one_div, mul_zero] using h

noncomputable def realMollify {I : Type*} [Fintype I] (k : ℕ)
    (u : EuclideanSpace ℝ I → ℝ) : EuclideanSpace ℝ I → ℝ :=
  (euclideanMollifier k).normed volume ⋆ u

lemma realMollify_contDiff {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    ContDiff ℝ (⊤ : ℕ∞) (realMollify k u) :=
  (euclideanMollifier k).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (euclideanMollifier k).contDiff_normed (hu.locallyIntegrable (by norm_num))

lemma realMollify_memLp {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    MemLp (realMollify k u) 2 := by
  apply (memLp_two_iff_integrable_sq (realMollify_contDiff k hu).continuous.aestronglyMeasurable).2
  exact (euclidean_convolution_sq_integral_le (I := I)
    ((euclideanMollifier (I := I) k).normed volume) u
    ((euclideanMollifier (I := I) k).contDiff_normed (n := (⊤ : ℕ∞))).continuous (euclideanMollifier k).hasCompactSupport_normed
    (euclideanMollifier k).nonneg_normed (euclideanMollifier k).integral_normed
    (hu.locallyIntegrable (by norm_num)) hu.integrable_sq).1

lemma realMollify_sq_integral_le {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    (∫ x, (realMollify k u x)^2) ≤ ∫ x, (u x)^2 :=
  (euclidean_convolution_sq_integral_le (I := I)
    ((euclideanMollifier (I := I) k).normed volume) u
    ((euclideanMollifier (I := I) k).contDiff_normed (n := (⊤ : ℕ∞))).continuous (euclideanMollifier k).hasCompactSupport_normed
    (euclideanMollifier k).nonneg_normed (euclideanMollifier k).integral_normed
    (hu.locallyIntegrable (by norm_num)) hu.integrable_sq).2

lemma realMollify_ae_tendsto {I : Type*} [Fintype I]
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    ∀ᵐ x ∂volume, Tendsto (fun k => realMollify k u x) atTop (nhds (u x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun k => euclideanMollifier k) (K := 2) euclideanMollifier_tendsto _
    (hu.locallyIntegrable (by norm_num))
  exact Eventually.of_forall fun k => by simp [euclideanMollifier, div_eq_mul_inv]

end Coulomb
end
end

end OAI
