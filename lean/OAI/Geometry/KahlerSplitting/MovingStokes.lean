import OAI.Geometry.KahlerSplitting.FormDerivatives

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set
open scoped Manifold ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory

namespace UniversalCoverSplitting

def alternatingEvalCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (v : Fin k → E) : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ where
  toFun B := B v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const v

abbrev Real3 := Fin 3 → ℝ

def realBasis3 (i : Fin 3) : Real3 := Pi.single i 1

def stokesCoefficient (B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ) (i : Fin 3) : Real3 → ℝ :=
  fun x ↦ (-1) ^ i.val * B x (i.removeNth realBasis3)

def stokesCoefficientDeriv (B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ) (i : Fin 3)
    (x : Real3) : Real3 →L[ℝ] ℝ :=
  (-1 : ℝ)^i.val • fderiv ℝ (fun y ↦ B y (i.removeNth realBasis3)) x

theorem stokesCoefficient_hasFDerivAt {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    {x : Real3} (hB : DifferentiableAt ℝ B x) (i : Fin 3) :
    HasFDerivAt (stokesCoefficient B i) (stokesCoefficientDeriv B i x) x := by
  have h := (alternatingEvalCLM (i.removeNth realBasis3)).differentiableAt.comp x hB
  exact h.hasFDerivAt.const_mul ((-1 : ℝ)^i.val)

theorem sum_stokesCoefficientDeriv_eq_extDeriv {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    {x : Real3} (hB : DifferentiableAt ℝ B x) :
    (∑ i : Fin 3, stokesCoefficientDeriv B i x (realBasis3 i)) =
      extDeriv B x realBasis3 := by
  rw [extDeriv_apply hB]
  simp [stokesCoefficientDeriv, zsmul_eq_mul]

theorem sum_faces_eq_zero_of_closed_twoForm
    {U : Set Real3} (hU : IsOpen U)
    {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    (hB : ContDiffOn ℝ 1 B U) (hc : ∀ x ∈ U, extDeriv B x = 0)
    (a b : Real3) (hab : a ≤ b) (hbox : Icc a b ⊆ U) :
    (∑ i : Fin 3,
      ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          stokesCoefficient B i (i.insertNth (b i) y)) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          stokesCoefficient B i (i.insertNth (a i) y))) = 0 := by
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ B x := fun x hx ↦
    (hB.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hzero : ∀ x ∈ Icc a b,
      (∑ i : Fin 3, stokesCoefficientDeriv B i x (Pi.single i 1)) = 0 := by
    intro x hx
    change (∑ i : Fin 3, stokesCoefficientDeriv B i x (realBasis3 i)) = 0
    rw [sum_stokesCoefficientDeriv_eq_extDeriv (hdiff x (hbox hx)), hc x (hbox hx)]
    rfl
  have hi : IntegrableOn (fun x ↦ ∑ i : Fin 3,
      stokesCoefficientDeriv B i x (Pi.single i 1)) (Icc a b) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : Real3 ↦ (0 : ℝ)) (Icc a b)).congr_fun ?_ measurableSet_Icc
    · intro x hx
      exact (hzero x hx).symm
  have hst := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (stokesCoefficient B) (stokesCoefficientDeriv B) ∅ Set.countable_empty
    (fun i ↦ (((alternatingEvalCLM (i.removeNth realBasis3)).continuous.comp_continuousOn
      hB.continuousOn).const_mul ((-1 : ℝ)^i.val)).mono hbox)
    (fun x hx i ↦ stokesCoefficient_hasFDerivAt (hdiff x (hbox ⟨
      fun j ↦ (hx.1 j (mem_univ j)).1.le, fun j ↦ (hx.1 j (mem_univ j)).2.le⟩)) i) hi
  rw [setIntegral_congr_fun measurableSet_Icc hzero, integral_zero] at hst
  exact hst.symm

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory

theorem first_face_integral_le_of_closed
    {U : Set Real3} (hU : IsOpen U)
    {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    (hB : ContDiffOn ℝ 1 B U) (hc : ∀ x ∈ U, extDeriv B x = 0)
    (a b : Real3) (hab : a ≤ b) (hbox : Icc a b ⊆ U)
    (hbottom : ∀ y ∈ Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      stokesCoefficient B 1 ((1 : Fin 3).insertNth (a 1) y) = 0)
    (htop : ∀ y ∈ Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      0 ≤ stokesCoefficient B 1 ((1 : Fin 3).insertNth (b 1) y))
    (hperiod : ∀ y ∈ Icc (a ∘ (2 : Fin 3).succAbove) (b ∘ (2 : Fin 3).succAbove),
      stokesCoefficient B 2 ((2 : Fin 3).insertNth (b 2) y) =
      stokesCoefficient B 2 ((2 : Fin 3).insertNth (a 2) y)) :
    (∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient B 0 ((0 : Fin 3).insertNth (b 0) y)) ≤
    ∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient B 0 ((0 : Fin 3).insertNth (a 0) y) := by
  have hs := sum_faces_eq_zero_of_closed_twoForm hU hB hc a b hab hbox
  have hb : (∫ y in Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      stokesCoefficient B 1 ((1 : Fin 3).insertNth (a 1) y)) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Icc hbottom, integral_zero]
  have ht : 0 ≤ (∫ y in Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      stokesCoefficient B 1 ((1 : Fin 3).insertNth (b 1) y)) :=
    setIntegral_nonneg measurableSet_Icc htop
  have hp := setIntegral_congr_fun (μ := volume) measurableSet_Icc hperiod
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  norm_num only [Fin.val_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hs
  rw [hb, hp] at hs
  linarith

end UniversalCoverSplitting

open scoped ContDiff
open Set
namespace UniversalCoverSplitting

def movingPolar (R : ℝ → ℝ) (x : Real3) : ℂ × ℂ :=
  ((x 0 : ℂ), ((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I))

theorem movingPolar_contDiffOn {R : ℝ → ℝ} {V : Set Real3} {J : Set ℝ}
    (hR : ContDiffOn ℝ ∞ R J) (hJ : MapsTo (fun x : Real3 ↦ x 0) V J) :
    ContDiffOn ℝ ∞ (movingPolar R) V := by
  have hr : ContDiffOn ℝ ∞ (fun x : Real3 ↦ R (x 0)) V :=
    hR.comp (by fun_prop) hJ
  have h0 : ContDiffOn ℝ ∞ (fun x : Real3 ↦ (x 0 : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (by fun_prop)
  have ha : ContDiffOn ℝ ∞ (fun x : Real3 ↦ ((R (x 0) * x 1 : ℝ) : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hr.mul (by fun_prop))
  have h2 : ContDiffOn ℝ ∞ (fun x : Real3 ↦ (x 2 : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (by fun_prop)
  exact h0.prodMk (ha.mul (Complex.contDiff_exp.comp_contDiffOn (h2.mul (contDiffOn_const (c := Complex.I)))))

theorem movingPolar_fderiv_apply {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) (v : Real3) :
    fderiv ℝ (movingPolar R) x v =
      ((v 0 : ℂ),
        (((deriv R (x 0) * v 0 * x 1 + R (x 0) * v 1 : ℝ) : ℂ) *
          Complex.exp ((x 2 : ℂ) * Complex.I)) +
        ((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I) *
          (v 2 : ℂ) * Complex.I) := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x
  have hr := hR.hasDerivAt.hasFDerivAt.comp x h0
  have ha := Complex.ofRealCLM.hasFDerivAt.comp x (hr.mul h1)
  have he := ((Complex.ofRealCLM.hasFDerivAt.comp x h2).mul_const Complex.I).cexp
  have hh := (Complex.ofRealCLM.hasFDerivAt.comp x h0).prodMk (ha.mul he)
  change HasFDerivAt (movingPolar R) _ x at hh
  rw [hh.fderiv]
  ext <;> simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

theorem movingPolar_deriv_zero {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 0) =
      (1, ((deriv R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_fderiv_apply hR]
  simp [realBasis3]

theorem movingPolar_deriv_one {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 1) =
      (0, (R (x 0) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_fderiv_apply hR]
  simp [realBasis3]

theorem movingPolar_deriv_two {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 2) =
      (0, ((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I) * Complex.I) := by
  rw [movingPolar_fderiv_apply hR]
  simp [realBasis3]

theorem movingPolar_deriv_zero' {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 0) =
      (1, 0) + (deriv R (x 0) * x 1) • (0, Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_deriv_zero hR]
  ext <;> simp [Complex.real_smul]

theorem movingPolar_deriv_one' {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 1) =
      R (x 0) • (0, Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_deriv_one hR]
  ext <;> simp [Complex.real_smul]

theorem movingPolar_deriv_two' {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 2) =
      (R (x 0) * x 1) • (Complex.I • (0, Complex.exp ((x 2 : ℂ) * Complex.I))) := by
  rw [movingPolar_deriv_two hR]
  ext <;> simp [Complex.real_smul, mul_comm, mul_left_comm]

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set MeasureTheory
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

def movingKahlerForm (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    (R : ℝ → ℝ) : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ :=
  realPullbackKahler g f (movingPolar R)

theorem movingKahlerForm_zero (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) :
    stokesCoefficient (movingKahlerForm g f R) 0 x =
      x 1 * R (x 0)^2 * g.metric (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
          (0, Complex.exp ((x 2 : ℂ) * Complex.I)))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
          (0, Complex.exp ((x 2 : ℂ) * Complex.I))) := by
  simp only [stokesCoefficient, Fin.val_zero, pow_zero, one_mul, movingKahlerForm,
    realPullbackKahler_apply]
  have h01 : (0 : Fin 3).removeNth realBasis3 0 = realBasis3 1 := rfl
  have h02 : (0 : Fin 3).removeNth realBasis3 1 = realBasis3 2 := rfl
  rw [h01, h02, movingPolar_deriv_one' hR, movingPolar_deriv_two' hR]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
    mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
  change g.metric _ (Complex.I • D (R (x 0) • (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
      (D ((R (x 0) * x 1) • (Complex.I • (0, Complex.exp ((x 2 : ℂ) * Complex.I))))) =
      x 1 * R (x 0)^2 * g.metric _
        (D (0, Complex.exp ((x 2 : ℂ) * Complex.I)))
        (D (0, Complex.exp ((x 2 : ℂ) * Complex.I)))
  simp only [ContinuousLinearMap.map_smul_of_tower, map_smul]
  simpa only [map_smul] using g.radial_angular_density (f (movingPolar R x))
    (D (0, Complex.exp ((x 2 : ℂ) * Complex.I))) (R (x 0)) (x 1)

theorem movingKahlerForm_one (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) :
    stokesCoefficient (movingKahlerForm g f R) 1 x =
      -g.metric (f (movingPolar R x))
        (Complex.I •
          (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1, 0) +
            (deriv R (x 0) * x 1) • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
              (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
        ((R (x 0) * x 1) •
          (Complex.I • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
            (0, Complex.exp ((x 2 : ℂ) * Complex.I)))) := by
  simp only [stokesCoefficient, Fin.val_one, pow_one, neg_one_mul, movingKahlerForm,
    realPullbackKahler_apply]
  have h10 : (1 : Fin 3).removeNth realBasis3 0 = realBasis3 0 := rfl
  have h12 : (1 : Fin 3).removeNth realBasis3 1 = realBasis3 2 := rfl
  rw [h10, h12, movingPolar_deriv_zero' hR, movingPolar_deriv_two' hR]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
    mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
  change -g.metric _
      (Complex.I • D ((1, 0) + (deriv R (x 0) * x 1) •
        (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
      (D ((R (x 0) * x 1) • (Complex.I • (0, Complex.exp ((x 2 : ℂ) * Complex.I))))) =
      -g.metric _ (Complex.I • (D (1, 0) +
        (deriv R (x 0) * x 1) • D (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
        ((R (x 0) * x 1) • (Complex.I • D (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
  simp only [map_add, ContinuousLinearMap.map_smul_of_tower, map_smul]

theorem movingKahlerForm_one_zero_radius (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) (hx : x 1 = 0) :
    stokesCoefficient (movingKahlerForm g f R) 1 x = 0 := by
  rw [movingKahlerForm_one g f hR, hx]
  simp

theorem movingKahlerForm_one_nonneg (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) (hx : x 1 = 1)
    (hpos : 0 ≤ R (x 0)) (C : ℝ) (hd : deriv R (x 0) ≤ -C)
    (hs : metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1, 0)) ≤
      C * metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0, 1))) :
    0 ≤ stokesCoefficient (movingKahlerForm g f R) 1 x := by
  have hvec : ((0, Complex.exp ((x 2 : ℂ) * Complex.I)) : ℂ × ℂ) =
      Complex.exp ((x 2 : ℂ) * Complex.I) • (0, 1) := by simp
  have hnorm : metricNorm g (f (movingPolar R x))
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
        (0, Complex.exp ((x 2 : ℂ) * Complex.I))) =
      metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0, 1)) := by
    let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
      mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
    change metricNorm g _ (D _) = metricNorm g _ (D _)
    rw [hvec, map_smul, metricNorm_complex_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [movingKahlerForm_one g f hR, hx, mul_one, mul_one, neg_nonneg]
  apply g.moving_flux_nonpos _ _ _ _ _ _ hpos hd
  rwa [hnorm]

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set MeasureTheory
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem movingKahlerForm_two_eq (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x y : Real3} (hR : DifferentiableAt ℝ R (x 0))
    (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (he : Complex.exp ((x 2 : ℂ) * Complex.I) =
      Complex.exp ((y 2 : ℂ) * Complex.I)) :
    stokesCoefficient (movingKahlerForm g f R) 2 x =
      stokesCoefficient (movingKahlerForm g f R) 2 y := by
  have hRy : DifferentiableAt ℝ R (y 0) := h0 ▸ hR
  have hp : movingPolar R x = movingPolar R y := by
    ext <;> simp only [movingPolar, h0, h1, he]
  have hv : (fun i : Fin 2 ↦ fderiv ℝ (movingPolar R) x
      ((2 : Fin 3).removeNth realBasis3 i)) =
      (fun i : Fin 2 ↦ fderiv ℝ (movingPolar R) y
      ((2 : Fin 3).removeNth realBasis3 i)) := by
    funext i
    fin_cases i
    · change fderiv ℝ (movingPolar R) x (realBasis3 0) =
        fderiv ℝ (movingPolar R) y (realBasis3 0)
      rw [movingPolar_deriv_zero hR, movingPolar_deriv_zero hRy, h0, h1, he]
    · change fderiv ℝ (movingPolar R) x (realBasis3 1) =
        fderiv ℝ (movingPolar R) y (realBasis3 1)
      rw [movingPolar_deriv_one hR, movingPolar_deriv_one hRy, h0, he]
  simp only [stokesCoefficient, movingKahlerForm, realPullbackKahler,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  rw [hp, hv]

theorem moving_disk_face_monotone (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ}
    {U : Set (ℂ × ℂ)} {V : Set Real3} {J : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hJ : IsOpen J)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hR : ContDiffOn ℝ ∞ R J) (hVJ : MapsTo (fun x : Real3 ↦ x 0) V J)
    (hmap : MapsTo (movingPolar R) V U)
    (a b : Real3) (hab : a ≤ b) (hbox : Icc a b ⊆ V)
    (ha1 : a 1 = 0) (hb1 : b 1 = 1) (ha2 : a 2 = 0) (hb2 : b 2 = 2 * Real.pi)
    (C : ℝ) (hpos : ∀ x ∈ Icc a b, 0 ≤ R (x 0))
    (hd : ∀ x ∈ Icc a b, deriv R (x 0) ≤ -C)
    (hs : ∀ x ∈ Icc a b, metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1, 0)) ≤
      C * metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0, 1))) :
    (∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth (b 0) y)) ≤
    ∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth (a 0) y) := by
  have hH := movingPolar_contDiffOn hR hVJ
  have hB := realPullbackKahler_smooth g hU hV hf hH hmap
  have hc := fun x hx ↦ realPullbackKahler_closed g hU hV hf hH hmap (x := x) hx
  have hRd (x : Real3) (hx : x ∈ Icc a b) : DifferentiableAt ℝ R (x 0) :=
    (hR.differentiableOn (by simp)).differentiableAt (hJ.mem_nhds (hVJ (hbox hx)))
  have hface (i : Fin 3) (t : ℝ) (ht : t ∈ Icc (a i) (b i))
      (y : Fin 2 → ℝ) (hy : y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      i.insertNth t y ∈ Icc a b := by
    constructor <;> intro j
    · obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
      · simpa using ht.1
      · simpa using hy.1 k
    · obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
      · simpa using ht.2
      · simpa using hy.2 k
  apply first_face_integral_le_of_closed hV (hB.of_le (by simp)) hc a b hab hbox
  · intro y hy
    have hx := hface 1 (a 1) ⟨le_rfl,hab 1⟩ y hy
    exact movingKahlerForm_one_zero_radius g f (hRd _ hx) (by simp [ha1])
  · intro y hy
    have hx := hface 1 (b 1) ⟨hab 1,le_rfl⟩ y hy
    exact movingKahlerForm_one_nonneg g f (hRd _ hx) (by simp [hb1])
      (hpos _ hx) C (hd _ hx) (hs _ hx)
  · intro y hy
    have hx := hface 2 (b 2) ⟨hab 2,le_rfl⟩ y hy
    apply movingKahlerForm_two_eq g f (hRd _ hx)
    · rfl
    · rfl
    · simp [ha2, hb2, Complex.exp_two_pi_mul_I]

end UniversalCoverSplitting

end

end OAI
