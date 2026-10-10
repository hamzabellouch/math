import OAI.MeasureTheory.CompactFactors.ConditionalLimits

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma norm_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  let a := ∫ x, ‖f x‖ ∂μ
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hvar : 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - a^2 := by
    have h : (0 : ℝ) ≤ ∫ x, (‖f x‖-a)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (‖f x‖-a))
    have he : (fun x => (‖f x‖-a)^2) = fun x => ‖f x‖^2 - (2*a)*‖f x‖ + a^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => ‖f x‖^2 - (2*a)*‖f x‖) (g := fun _ => a^2) (hf₂.sub (hf.norm.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub (f := fun x => ‖f x‖^2) (g := fun x => (2*a)*‖f x‖) hf₂ (hf.norm.const_mul (2*a)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    change 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - (2*a)*a + a^2 at h
    nlinarith
  have hn : ‖∫ x, f x ∂μ‖ ≤ a := norm_integral_le_integral_norm f
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]

def fiberMean (κ : Kernel X Y) (F : X × Y → ℂ) (x : X) : ℂ :=
  ∫ y, F (x,y) ∂κ x

lemma measurable_fiberMean (κ : Kernel X Y) [IsSFiniteKernel κ]
    (F : X × Y → ℂ) (hF : Measurable F) : Measurable (fiberMean κ F) :=
  hF.stronglyMeasurable.integral_kernel_prod_right'.measurable

lemma fiberMean_bound (κ : Kernel X Y) [IsMarkovKernel κ]
    (F : X × Y → ℂ) (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (x : X) :
    ‖fiberMean κ F x‖ ≤ C := by
  simpa only [fiberMean, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ x)
      (Filter.Eventually.of_forall fun y => hC (x,y))

lemma fiberMean_l2_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] (F : X × Y → ℂ)
    (hF : Measurable F) (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) :
    (∫ x, ‖fiberMean κ F x‖^2 ∂μ) ≤ ∫ z, ‖F z‖^2 ∂(μ ⊗ₘ κ) := by
  have hsq (z : X × Y) : ‖F z‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) (hFC z) 2
  have hi : Integrable (fun z => ‖F z‖^2) (μ ⊗ₘ κ) :=
    Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_sq] using hsq z)
  rw [Measure.integral_compProd hi]
  apply integral_mono
  · exact Integrable.of_bound ((measurable_fiberMean κ F hF).norm.pow_const 2).aestronglyMeasurable
      (C^2) (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using
          pow_le_pow_left₀ (norm_nonneg _) (fiberMean_bound κ F C hFC x) 2)
  · have hm := (hF.norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
    exact Integrable.of_bound hm.aestronglyMeasurable (C^2) (Filter.Eventually.of_forall fun x => by
      have hb := norm_integral_le_of_norm_le_const (μ := κ x)
        (f := fun y => ‖F (x,y)‖^2) (C := C^2)
        (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs, abs_sq] using hsq (x,y))
      simpa only [probReal_univ, mul_one] using hb)

  · intro x
    apply norm_integral_sq
    · exact Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => hFC (x,y))
    · exact Integrable.of_bound ((hF.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
        (C^2) (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs, abs_sq] using hsq (x,y))

lemma kernel_apply_error_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] (L P : X × Y → ℂ)
    (hL : Measurable L) (hP : Measurable P) (C : ℝ)
    (hLC : ∀ z, ‖L z‖ ≤ C) (hPC : ∀ z, ‖P z‖ ≤ C)
    (f : Y → ℂ) (hf : Measurable f) (hfB : ∀ y, ‖f y‖ ≤ 1) :
    (∫ x, ‖fiberMean κ (fun z => L z * f z.2) x -
      fiberMean κ (fun z => P z * f z.2) x‖^2 ∂μ) ≤
        ∫ z, ‖L z - P z‖^2 ∂(μ ⊗ₘ κ) := by
  have hLP (z : X × Y) : ‖L z - P z‖ ≤ 2*C :=
    (norm_sub_le _ _).trans (by linarith [hLC z, hPC z])
  have hF : Measurable (fun z : X × Y => (L z - P z) * f z.2) :=
    (hL.sub hP).mul (hf.comp measurable_snd)
  have hFB (z : X × Y) : ‖(L z - P z) * f z.2‖ ≤ 2*C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hLP z)
  have he (x : X) : fiberMean κ (fun z => L z * f z.2) x -
      fiberMean κ (fun z => P z * f z.2) x =
        fiberMean κ (fun z => (L z - P z) * f z.2) x := by
    dsimp [fiberMean]
    simp_rw [sub_mul]
    rw [integral_sub]
    · exact Integrable.of_bound ((hL.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => by
          rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hfB y) (norm_nonneg _)).trans (by simpa using hLC (x,y)))
    · exact Integrable.of_bound ((hP.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => by
          rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hfB y) (norm_nonneg _)).trans (by simpa using hPC (x,y)))
  simp_rw [he]
  apply (fiberMean_l2_bound μ κ _ hF (2*C) hFB).trans
  apply integral_mono
  · exact Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hFB z) 2)
  · exact Integrable.of_bound ((hL.sub hP).norm.pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hLP z) 2)
  · intro z
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg (L z - P z))

end EuclideanFiveColor.KernelCompact

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/

namespace EuclideanFiveColor.RectangleDensity
open MeasureTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]

abbrev Code (n : ℕ) := Fin n → Bool

def code (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (n : ℕ) (x : X) : Code n := by
  classical
  exact fun i => if x ∈ MeasurableSpace.natGeneratingSequence X i then true else false

lemma measurable_code (n : ℕ) : Measurable (code X n) := by
  classical
  apply Measurable.of_eval
  intro i
  exact measurable_const.piecewise (MeasurableSpace.measurableSet_natGeneratingSequence (α := X) i) measurable_const

def pairCode (n : ℕ) (z : X × Y) : Code n × Code n := (code X n z.1, code Y n z.2)

lemma measurable_pairCode (n : ℕ) : Measurable (pairCode (X := X) (Y := Y) n) :=
  ((measurable_code n).comp measurable_fst).prodMk ((measurable_code n).comp measurable_snd)

lemma pairCode_mono : Monotone (fun n =>
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) := by
  intro n m hnm
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun z : Code m × Code m => (fun i : Fin n => z.1 (Fin.castLE hnm i), fun i : Fin n => z.2 (Fin.castLE hnm i)))
    (measurable_of_countable _)
  rfl

lemma pairCode_generates : (⨆ n,
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  classical
  apply le_antisymm (iSup_le fun n => (measurable_pairCode n).comap_le)
  let m := ⨆ n, (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)
  have hp (n : ℕ) : Measurable[m] (pairCode (X := X) (Y := Y) n) :=
    (comap_measurable _).mono (by exact le_iSup (fun n =>
      (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) n) le_rfl
  have hx : @Measurable (X × Y) X m _ Prod.fst := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).1 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    ext z
    simp [pairCode, code]
  have hy : @Measurable (X × Y) Y m _ Prod.snd := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence Y]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).2 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_snd.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    ext z
    simp [pairCode, code]
  have hi := (hx.prodMk hy).comap_le
  have hfun : (fun z : X × Y => (z.1, z.2)) = id := rfl
  rw [hfun] at hi
  simpa only [MeasurableSpace.comap_id] using hi

/-- Bounded finite rectangle approximation for any probability coupling, not
only a product measure. The common sup bound is twice the original bound. -/
theorem bounded_rectangles (ν : Measure (X × Y)) [IsProbabilityMeasure ν]
    (L : X × Y → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Code n × Code n → ℂ),
      (∀ z, ‖a z‖ ≤ 2*C) ∧
      Integrable (fun z => ‖L z - a (pairCode n z)‖^2) ν ∧
      (∫ z, ‖L z - a (pairCode n z)‖^2 ∂ν) < ε^2 := by
  let H : X × Y → Fin 1 → ℂ := fun z _ => L z
  have hH : Measurable H := Measurable.of_eval fun _ => hL
  have hHB (z : X × Y) : ‖H z‖ ≤ C := by
    rw [pi_norm_le_iff_of_nonneg hC]; intro i; exact hLC z
  obtain ⟨n, H₀, _, hB, hi, he⟩ := LimitDensity.generated_factor_approximation ν
    (fun n => pairCode (X := X) (Y := Y) n) measurable_pairCode
    pairCode_mono pairCode_generates 1 H hH C hC hHB ε hε
  have hd (z : X × Y) : dist (H z) (H₀ (pairCode n z)) = ‖L z - H₀ (pairCode n z) 0‖ := by
    rw [dist_eq_norm]
    have heq : H z - H₀ (pairCode n z) = fun _ : Fin 1 => L z - H₀ (pairCode n z) 0 := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    rw [heq, pi_norm_const]
  refine ⟨n, fun z => H₀ z 0, fun z => (norm_le_pi_norm (H₀ z) 0).trans (hB z), ?_, ?_⟩
  · simpa only [hd] using hi
  · simpa only [hd] using he

end EuclideanFiveColor.RectangleDensity

namespace EuclideanFiveColor.KernelCompact

section
open MeasureTheory ProbabilityTheory RectangleDensity
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X]

/-- Uniform finite bounded-module approximation to the image of the bounded
unit ball under an integral kernel. This is the compactness step of the
relative compact-factor construction, with no spectral decomposition. -/
theorem bounded_range_approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ) (B C₀ : ℝ) (Hf : Fin r → X → ℂ),
      0 ≤ B ∧ 0 ≤ C₀ ∧ (∀ i, Measurable (Hf i)) ∧ (∀ x, ∑ i, ‖Hf i x‖ ≤ C₀) ∧
      ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ 1) →
        ∃ a : Y → Fin r → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
          Integrable (fun x => dist (∫ x', L (x,x') * f x' ∂κ (q x))
            (∑ i, a (q x) i * Hf i x)^2) μ ∧
          (∫ x, dist (∫ x', L (x,x') * f x' ∂κ (q x))
            (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2 := by
  classical
  let κ₀ := κ.comap q hq
  obtain ⟨n, c, hB, _, he⟩ := bounded_rectangles (μ ⊗ₘ κ₀) L hL C hC hLC ε hε
  let r := Fintype.card (Code n)
  let e : Fin r ≃ Code n := (Fintype.equivFin (Code n)).symm
  let Hf : Fin r → X → ℂ := fun i x => if code X n x = e i then 1 else 0
  have hHf (i : Fin r) : Measurable (Hf i) :=
    measurable_const.piecewise ((measurable_code n) (measurableSet_singleton (e i))) measurable_const
  have hHfB (i : Fin r) (x : X) : ‖Hf i x‖ ≤ 1 := by
    dsimp only [Hf]
    split_ifs <;> norm_num
  have hsumB (x : X) : ∑ i, ‖Hf i x‖ ≤ r := by
    calc
      ∑ i, ‖Hf i x‖ ≤ ∑ _ : Fin r, (1 : ℝ) := Finset.sum_le_sum fun i _ => hHfB i x
      _ = r := by simp
  refine ⟨r, 2*C, r, Hf, by positivity, by positivity, hHf, hsumB, ?_⟩
  intro f hf hfB
  let a : Y → Fin r → ℂ := fun y i => ∫ x', c (e i, code X n x') * f x' ∂κ y
  have hm (i : Fin r) : Measurable (fun x' => c (e i, code X n x') * f x') :=
    ((measurable_of_countable c).comp (measurable_const.prodMk (measurable_code n))).mul hf
  have hbound (i : Fin r) (x' : X) : ‖c (e i, code X n x') * f x'‖ ≤ 2*C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB x') (norm_nonneg _)).trans (by simpa using hB (e i, code X n x'))
  have ha : Measurable a := by
    apply Measurable.of_eval
    intro i
    exact (hm i).stronglyMeasurable.integral_kernel.measurable
  have haB (y : Y) : ‖a y‖ ≤ 2*C := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa only [a, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := κ y) (Filter.Eventually.of_forall (hbound i))
  let P : X × X → ℂ := fun z => c (pairCode n z)
  have hP : Measurable P := (measurable_of_countable c).comp (measurable_pairCode n)
  have hPB (z : X × X) : ‖P z‖ ≤ 2*C := hB _
  have hs (x : X) : (∑ i, a (q x) i * Hf i x) = fiberMean κ₀ (fun z => P z * f z.2) x := by
    rw [Finset.sum_eq_single (e.symm (code X n x))]
    · simp [a, Hf, fiberMean, P, pairCode, κ₀]
    · intro b _ hb
      have hn : code X n x ≠ e b := by
        intro hz
        exact hb (e.injective (by simpa using hz.symm))
      simp [Hf, hn]
    · simp
  have hfm : Measurable (fiberMean κ₀ (fun z => L z * f z.2)) :=
    measurable_fiberMean κ₀ _ (hL.mul (hf.comp measurable_snd))
  have hgm : Measurable (fiberMean κ₀ (fun z => P z * f z.2)) :=
    measurable_fiberMean κ₀ _ (hP.mul (hf.comp measurable_snd))
  have hfb (x : X) : ‖fiberMean κ₀ (fun z => L z * f z.2) x‖ ≤ C := by
    apply fiberMean_bound
    intro z
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hLC z)
  have hgb (x : X) : ‖fiberMean κ₀ (fun z => P z * f z.2) x‖ ≤ 2*C := by
    apply fiberMean_bound
    intro z
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hPB z)
  have hdist : Integrable (fun x =>
      dist (fiberMean κ₀ (fun z => L z * f z.2) x) (fiberMean κ₀ (fun z => P z * f z.2) x)^2) μ :=
    Integrable.of_bound ((hfm.dist hgm).pow_const 2).aestronglyMeasurable ((3*C)^2)
      (Filter.Eventually.of_forall fun x => by
        have hd : dist (fiberMean κ₀ (fun z => L z * f z.2) x) (fiberMean κ₀ (fun z => P z * f z.2) x) ≤ 3*C :=
          (dist_le_norm_add_norm _ _).trans (by linarith [hfb x, hgb x])
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ dist_nonneg hd 2)
  refine ⟨a, ha, haB, ?_, ?_⟩
  · simpa only [hs, fiberMean, κ₀, Kernel.comap_apply] using hdist
  · simp_rw [hs, dist_eq_norm]
    change (∫ x, ‖fiberMean κ₀ (fun z => L z * f z.2) x - fiberMean κ₀ (fun z => P z * f z.2) x‖^2 ∂μ) < ε^2
    exact (kernel_apply_error_bound μ κ₀ L P hL hP (2*C)
      (fun z => (hLC z).trans (by linarith)) hPB f hf hfB).trans_lt he

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

def applyKernel (κ : Kernel Y X) (q : X → Y) (L : X × X → ℂ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ x', L (x,x') * f x' ∂κ (q x)

omit [MeasurableConstSMul K Y] in
lemma applyKernel_covariance (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z)
    (f : X → ℂ) (hfm : Measurable f) (k : K) :
    (fun x => applyKernel κ q L f (k • x)) =ᵐ[μ]
      applyKernel κ q L (fun x => f (k • x)) := by
  have hc : ∀ᵐ x ∂μ, κ (k • q x) = (κ (q x)).map (fun x => k • x) :=
    ae_of_ae_map (μ := μ) (p := fun y => κ (k • y) = (κ y).map (fun x => k • x))
      hq.aemeasurable (hκcov k)
  have hl₀ := Measure.ae_ae_of_ae_compProd (μ := μ) (κ := κ.comap q hq)
    (p := fun z => L (k • z.1, k • z.2) = L z) (hLcov k)
  have hl : ∀ᵐ x ∂μ, ∀ᵐ x' ∂κ (q x), L (k • x, k • x') = L (x,x') := by
    simpa only [Kernel.comap_apply] using hl₀
  filter_upwards [hqcov k, hc, hl] with x hqx hcx hlx
  dsimp [applyKernel]
  have hLf : Measurable (fun y => L (k • x,y) * f y) :=
    (hL.comp (measurable_const.prodMk measurable_id)).mul hfm
  rw [hqx, hcx, integral_map (measurable_const_smul k).aemeasurable hLf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hlx] with x' hxx
  simp only [hxx]

end
section
open MeasureTheory ProbabilityTheory RectangleDensity
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X]

lemma norm_sq_le_sub (z w : ℂ) : ‖z‖^2 ≤ ‖z-w‖^2 + 2*(z*star w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg w.re, sq_nonneg w.im]

/-- A nonzero bounded relative-product kernel has a nonzero image of a bounded
measurable function. Finite rectangle density replaces a spectral theorem. -/
theorem exists_nonzero_image (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (hne : ¬ L =ᵐ[μ ⊗ₘ κ.comap q hq] 0) :
    ∃ f : X → ℂ, Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      ¬ applyKernel κ q L f =ᵐ[μ] 0 := by
  classical
  by_contra h
  push Not at h
  let κ₀ := κ.comap q hq
  let ν := μ ⊗ₘ κ₀
  have hL₂ : Integrable (fun z => ‖L z‖^2) ν :=
    Integrable.of_bound (hL.norm.pow_const 2).aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hLC z) 2)
  have hsmall : ∀ ε : ℝ, 0 < ε → (∫ z, ‖L z‖^2 ∂ν) < ε := by
    intro ε hε
    obtain ⟨n, c, hc, hi, he⟩ := bounded_rectangles ν L hL C hC hLC
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    rw [Real.sq_sqrt hε.le] at he
    let P : X × X → ℂ := fun z => c (pairCode n z)
    have hP : Measurable P := (measurable_of_countable c).comp (measurable_pairCode n)
    let d : ℝ := 2*C+1
    have hd : 0 < d := by dsimp [d]; positivity
    let f : Code n → X → ℂ := fun i x => star (c (i,code X n x)) / (d : ℂ)
    have hfm (i : Code n) : Measurable (f i) :=
      (Complex.continuous_conj.measurable.comp ((measurable_of_countable c).comp (measurable_const.prodMk (measurable_code n)))).div_const _
    have hfb (i : Code n) (x : X) : ‖f i x‖ ≤ 1 := by
      dsimp only [f]
      rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      apply (div_le_one hd).mpr
      exact (hc _).trans (by dsimp [d]; linarith)
    have hzero : ∀ᵐ x ∂μ, ∀ i : Code n, applyKernel κ q L (f i) x = 0 :=
      ae_all_iff.mpr fun i => h (f i) (hfm i) (hfb i)
    have hLP : Integrable (fun z => L z * star (P z)) ν :=
      Integrable.of_bound (hL.mul (Complex.continuous_conj.measurable.comp hP)).aestronglyMeasurable (C*(2*C))
        (Filter.Eventually.of_forall fun z => by
          rw [norm_mul, norm_star]
          exact mul_le_mul (hLC z) (hc _) (norm_nonneg _) hC)
    have hz : (∫ z, L z * star (P z) ∂ν) = 0 := by
      rw [Measure.integral_compProd hLP]
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with x hx
      have heq : (fun x' => L (x,x') * star (P (x,x'))) =
          fun x' => (L (x,x') * f (code X n x) x') * (d : ℂ) := by
        funext x'
        dsimp [P,pairCode,f]
        have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp [hdc]
      rw [heq, integral_mul_const]
      change applyKernel κ q L (f (code X n x)) x * (d : ℂ) = 0
      rw [hx, zero_mul]
    have hr : (∫ z, RCLike.re (L z * star (P z)) ∂ν) = 0 := by
      rw [integral_re hLP, hz]; rfl
    have hb := integral_mono hL₂ (hi.add (hLP.re.const_mul 2))
      (fun z => norm_sq_le_sub (L z) (P z))
    dsimp only [Pi.add_apply] at hb
    rw [integral_add hi (hLP.re.const_mul 2), integral_const_mul, hr, mul_zero, add_zero] at hb
    exact hb.trans_lt he
  have hz : (∫ z, ‖L z‖^2 ∂ν) = 0 := by
    apply le_antisymm
    · exact le_of_forall_pos_le_add fun ε hε => le_of_lt (by simpa using hsmall ε hε)
    · exact integral_nonneg fun z => sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖L z‖) hL₂).mp hz
  apply hne
  filter_upwards [hae] with z hz
  apply norm_eq_zero.mp
  exact sq_eq_zero_iff.mp hz

end

section
open MeasureTheory ProbabilityTheory Filter
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma measurable_applyKernel (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (L : X × X → ℂ) (hL : Measurable L)
    (f : X → ℂ) (hf : Measurable f) : Measurable (applyKernel κ q L f) :=
  measurable_fiberMean (κ.comap q hq) _ (hL.mul (hf.comp measurable_snd))

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma applyKernel_bound (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (L : X × X → ℂ) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (f : X → ℂ) (hfB : ∀ x, ‖f x‖ ≤ 1) (x : X) : ‖applyKernel κ q L f x‖ ≤ C := by
  have hb (x' : X) : ‖L (x,x') * f x'‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)).trans (by simpa using hLC (x,x'))
  change ‖∫ x', L (x,x') * f x' ∂κ (q x)‖ ≤ C
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ (q x)) (C := C) (Eventually.of_forall hb)

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma exists_invariant_set (ν : Measure (X × X))
    [SMulInvariantMeasure K (X × X) ν] (hn : ¬ ErgodicSMul K (X × X) ν) :
    ∃ s : Set (X × X), MeasurableSet s ∧
      (∀ k : K, (fun z : X × X => k • z) ⁻¹' s =ᵐ[ν] s) ∧
      ¬ EventuallyConst s (ae ν) := by
  classical
  by_contra! h
  apply hn
  exact ⟨fun hs hi => h _ hs hi⟩

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma indicator_not_constant (ν : Measure (X × X)) (s : Set (X × X))
    (hn : ¬ EventuallyConst s (ae ν)) (c : ℂ) :
    ¬ s.indicator (fun _ => (1 : ℂ)) =ᵐ[ν] (fun _ => c) := by
  classical
  intro he
  apply hn
  change EventuallyEmptyOrUniv s (ae ν)
  rw [eventuallyEmptyOrUniv_iff]
  by_cases hc : c = 0
  · right
    filter_upwards [he] with x hx
    simpa [hc] using hx
  · left
    filter_upwards [he] with x hx
    by_contra hxs
    simp only [Set.indicator_of_notMem hxs] at hx
    exact hc hx.symm

end
open MeasureTheory ProbabilityTheory Filter
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma row_constant (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z) :
    (fun x => ∫ x', L (x,x') ∂κ (q x)) =ᵐ[μ]
      (fun _ => ∫ z, L z ∂μ ⊗ₘ κ.comap q hq) := by
  have hfm := measurable_applyKernel κ q hq L hL (fun _ => 1) measurable_const
  have hi : ∀ k : K, ∀ᵐ x ∂μ,
      applyKernel κ q L (fun _ => 1) (k • x) = applyKernel κ q L (fun _ => 1) x :=
    fun k => applyKernel_covariance μ κ q hq L hL hqcov hκcov hLcov _ measurable_const k
  obtain ⟨c, hc⟩ := ErgodicSupport.ae_eq_const_of_invariant hfm hi
  have hc' : (fun x => ∫ x', L (x,x') ∂κ (q x)) =ᵐ[μ] (fun _ => c) := by
    filter_upwards [hc] with x hx
    simpa only [applyKernel, mul_one] using hx
  have hLi : Integrable L (μ ⊗ₘ κ.comap q hq) :=
    Integrable.of_bound hL.aestronglyMeasurable C (Eventually.of_forall hLC)
  have he : (∫ z, L z ∂μ ⊗ₘ κ.comap q hq) = c := by
    rw [Measure.integral_compProd hLi]
    change (∫ x, (∫ x', L (x,x') ∂κ (q x)) ∂μ) = c
    rw [integral_congr_ae hc']
    simp
  simpa only [he] using hc'

omit [MeasurableConstSMul K Y] in
lemma centered_kernel (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (hswap : (μ ⊗ₘ κ.comap q hq).map Prod.swap = μ ⊗ₘ κ.comap q hq)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    [SMulInvariantMeasure K (X × X) (μ ⊗ₘ κ.comap q hq)]
    (hn : ¬ ErgodicSMul K (X × X) (μ ⊗ₘ κ.comap q hq)) :
    ∃ L : X × X → ℂ, Measurable L ∧ (∀ z, ‖L z‖ ≤ 2) ∧
      (∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z) ∧
      ¬ L =ᵐ[μ ⊗ₘ κ.comap q hq] 0 ∧
      (∀ᵐ x ∂μ, (∫ x', L (x,x') ∂κ (q x)) = 0) ∧
      (∀ᵐ x ∂μ, (∫ x', L (x',x) ∂κ (q x)) = 0) := by
  classical
  let ν := μ ⊗ₘ κ.comap q hq
  obtain ⟨s, hs, hscov, hsn⟩ := exists_invariant_set ν hn
  let F : X × X → ℂ := s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hFB (z : X × X) : ‖F z‖ ≤ 1 := by
    dsimp [F]; by_cases hz : z ∈ s <;> simp [hz]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall hFB)
  have hFc : ∀ k : K, ∀ᵐ z ∂ν, F (k • z.1,k • z.2) = F z := by
    intro k; filter_upwards [hscov k] with z hz
    change ((k • z.1,k • z.2) ∈ s) = (z ∈ s) at hz
    dsimp only [F]
    simp only [Set.indicator_apply, hz]
  let c : ℂ := ∫ z, F z ∂ν
  have hc : ‖c‖ ≤ 1 := by
    simpa [c] using norm_integral_le_of_norm_le_const (μ := ν) (f := F)
      (C := 1) (Eventually.of_forall hFB)
  let L : X × X → ℂ := fun z => F z - c
  have hLm : Measurable L := hF.sub measurable_const
  have hLB (z : X × X) : ‖L z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hFB z])
  have hLc : ∀ k : K, ∀ᵐ z ∂ν, L (k • z.1,k • z.2) = L z := by
    intro k; filter_upwards [hFc k] with z hz using congrArg (fun w => w-c) hz
  have hLn : ¬ L =ᵐ[ν] 0 := by
    intro h
    apply indicator_not_constant ν s hsn c
    filter_upwards [h] with z hz
    exact sub_eq_zero.mp hz
  have hL0 : (∫ z, L z ∂ν) = 0 := by
    rw [integral_sub hFi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, c, sub_self]
  have hr := row_constant μ κ q hq L hLm 2 hLB hqcov hκcov hLc
  have hswapP : MeasurePreserving Prod.swap ν ν := ⟨measurable_swap, hswap⟩
  have hLsc : ∀ k : K, ∀ᵐ z ∂ν, (L ∘ Prod.swap) (k • z.1,k • z.2) = (L ∘ Prod.swap) z := by
    intro k
    exact hswapP.quasiMeasurePreserving.ae (hLc k)
  have hc' := row_constant μ κ q hq (L ∘ Prod.swap) (hLm.comp measurable_swap) 2
    (fun z => hLB _) hqcov hκcov hLsc
  have hLs0 : (∫ z, (L ∘ Prod.swap) z ∂ν) = 0 := by
    change (∫ z, L (Prod.swap z) ∂ν) = 0
    rw [← integral_map measurable_swap.aemeasurable hLm.aestronglyMeasurable]
    exact (congrArg (fun ρ => ∫ z, L z ∂ρ) hswap).trans hL0
  refine ⟨L, hLm, hLB, hLc, hLn, ?_, ?_⟩
  · filter_upwards [hr] with x hx using hx.trans hL0
  · filter_upwards [hc'] with x hx using hx.trans hLs0

end EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

def law (μ : Measure X) [IsFiniteMeasure μ] (q : X → Y) (hq : Measurable q) : Measure (X × X) :=
  μ ⊗ₘ (condDistrib id q μ).comap q hq

lemma law_eq_mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    law μ q hq = ((condDistrib id q μ).prod (condDistrib id q μ)) ∘ₘ μ.map q := by
  let κ := condDistrib id q μ
  ext s hs
  rw [law, Measure.compProd_apply hs, Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  have he := ConditionalFiber.comp_identity_fiber μ q hq
  change κ ∘ₘ μ.map q = μ at he
  have hm : Measurable (fun x => (κ (q x)) (Prod.mk x ⁻¹' s)) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ.comap q hq) hs
  change (∫⁻ x, κ (q x) (Prod.mk x ⁻¹' s) ∂μ) = _
  conv_lhs => rw [← he]
  rw [Measure.lintegral_bind (Kernel.measurable κ).aemeasurable hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply, Measure.prod_apply hs]
  exact lintegral_congr_ae (hy.mono fun x hx => by change κ (q x) _ = _; rw [hx])

lemma law_swap (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    (law μ q hq).map Prod.swap = law μ q hq := by
  rw [law_eq_mixture]
  rw [Measure.map_comp _ _ measurable_swap, Kernel.map_prod_swap]

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

instance law_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) : IsProbabilityMeasure (law μ q hq) := by
  dsimp [law]; infer_instance

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k • y) =
      (condDistrib id q μ y).map (fun x => k • x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun x => k • x)
    (measurable_const_smul k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

lemma law_preserving (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    MeasurePreserving (fun z : X × X => (k • z.1,k • z.2)) (law μ q hq) (law μ q hq) := by
  let κ := condDistrib id q μ
  let ν := μ.map q
  have hS := measurable_const_smul (M := K) (α := X) k
  have hR := measurable_const_smul (M := K) (α := Y) k
  have hν : ν.map (fun y => k • y) = ν := by
    dsimp [ν]
    rw [Measure.map_map hR hq]
    calc
      _ = μ.map (q ∘ (fun x => k • x)) := Measure.map_congr (Filter.EventuallyEq.symm (hqcov k))
      _ = _ := by rw [← Measure.map_map hq hS, (hpres k).map_eq]
  have hc := conditional_covariance μ q hq hpres hqcov k
  refine ⟨hS.prodMap hS, ?_⟩
  change (law μ q hq).map (Prod.map (fun x => k • x) (fun x => k • x)) = _
  rw [law_eq_mixture, Measure.map_comp _ _ (hS.prodMap hS), ← Kernel.map_prod_map _ _ hS hS]
  change ((κ.map (fun x => k • x)).prod (κ.map (fun x => k • x))) ∘ₘ ν = _
  calc
    _ = ((κ.prod κ).comap (fun y => k • y) hR) ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hc] with y hy
      simp only [Kernel.prod_apply, Kernel.map_apply _ hS, Kernel.comap_apply]
      rw [hy]
    _ = (κ.prod κ) ∘ₘ ν.map (fun y => k • y) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        lintegral_map ((κ.prod κ).measurable_coe hs) hR]
      rfl
    _ = (κ.prod κ) ∘ₘ ν := by rw [hν]

lemma law_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) :
    SMulInvariantMeasure K (X × X) (law μ q hq) := by
  constructor
  intro k s hs
  exact (law_preserving μ q hq hpres hqcov k).measure_preimage hs.nullMeasurableSet

end EuclideanFiveColor.RelativeProduct
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory Filter ConditionalFiber
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

lemma image_conditional_mean_zero (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (f : X → ℂ) (hfm : Measurable f) (hfB : ∀ x, ‖f x‖ ≤ 1)
    (hcol : ∀ᵐ x ∂μ, (∫ x', L (x',x) ∂condDistrib id q μ (q x)) = 0) :
    ∀ᵐ y ∂μ.map q, (∫ x, applyKernel (condDistrib id q μ) q L f x
      ∂condDistrib id q μ y) = 0 := by
  let κ := condDistrib id q μ
  filter_upwards [ae_in_own_fiber μ q hq, ae_fiber_of_ae μ q hq hcol] with y hy hcy
  have hLF : Measurable (fun z : X × X => L z * f z.2) := hL.mul (hfm.comp measurable_snd)
  have hLFB (z : X × X) : ‖L z * f z.2‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)).trans (by simpa using hLC z)
  have hLFi : Integrable (fun z : X × X => L z * f z.2) ((κ y).prod (κ y)) :=
    Integrable.of_bound hLF.aestronglyMeasurable C (Eventually.of_forall hLFB)
  calc
    (∫ x, applyKernel κ q L f x ∂κ y) =
        ∫ x, (∫ x', L (x,x') * f x' ∂κ y) ∂κ y := by
      apply integral_congr_ae
      filter_upwards [hy] with x hx
      dsimp only [applyKernel]; rw [hx]
    _ = ∫ x', (∫ x, L (x,x') * f x' ∂κ y) ∂κ y := integral_integral_swap hLFi
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hy, hcy] with x' hx' hc'
      rw [integral_mul_const]
      change (∫ x, L (x,x') ∂κ (q x')) = 0 at hc'
      rw [hx'] at hc'
      change _ = 0
      rw [hc', zero_mul]

lemma nonzero_not_factorizable (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) (H : X → ℂ)
    (hn : ¬ H =ᵐ[μ] 0)
    (hc : ∀ᵐ y ∂μ.map q, (∫ x, H x ∂condDistrib id q μ y) = 0) :
    ¬ ∃ b : Y → ℂ, Measurable b ∧ H =ᵐ[μ] b ∘ q := by
  rintro ⟨b, _hb, he⟩
  have hb0 : ∀ᵐ y ∂μ.map q, b y = 0 := by
    filter_upwards [hc, ae_in_own_fiber μ q hq, ae_fiber_of_ae μ q hq he] with y hy hqy hey
    have hh : H =ᵐ[condDistrib id q μ y] (fun _ => b y) := by
      filter_upwards [hqy, hey] with x hx hx'
      simpa only [Function.comp_apply, hx] using hx'
    rw [integral_congr_ae hh] at hy
    simpa using hy
  apply hn
  have he0 : ∀ᵐ x ∂μ, b (q x) = 0 := ae_of_ae_map (p := fun y => b y = 0) hq.aemeasurable hb0
  filter_upwards [he, he0] with x hx hx' using hx.trans hx'

end EuclideanFiveColor.KernelCompact

end

end OAI
