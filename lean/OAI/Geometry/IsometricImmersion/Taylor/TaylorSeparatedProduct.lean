import OAI.Geometry.IsometricImmersion.Taylor.TimeTaylorKernel
import OAI.Geometry.IsometricImmersion.Darboux.QSpatialJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def spatialStrip (I : Set ℝ) : Set Coord := {p | p 0 ∈ I}

theorem spatialStrip_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (spatialStrip I) :=
  hI.preimage (continuous_apply 0)

def separatedProduct (C f : ℝ → ℝ) (p : Coord) : ℝ := C (p 0) * f (p 1)

theorem separatedProduct_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (separatedProduct C f) (spatialStrip I) :=
  (hC.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
    (hf.comp (contDiff_apply ℝ ℝ 1)).contDiffOn

theorem initialPoint_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => (![y, t] : Coord)) (Pi.single 0 (1 : ℝ)) x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hasDerivAt_id x using 1 <;> rfl
  · simpa using hasDerivAt_const x t

theorem point_eta (p : Coord) : (![p 0, p 1] : Coord) = p := by
  ext i
  fin_cases i <;> rfl

theorem separatedProduct_partial_x {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (separatedProduct C f) p = deriv C (p 0) * f (p 1) := by
  have hd := (((separatedProduct_contDiffOn hC f hf).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (separatedProduct C f) (fderiv ℝ (separatedProduct C f) p)
      (![p 0, p 1] : Coord) := by simpa only [point_eta] using hd
  have hcurve := hd'.comp_hasDerivAt (p 0) (initialPoint_hasDerivAt (p 0) (p 1))
  have hCderiv := ((hC.contDiffAt (hI.mem_nhds hp)).differentiableAt (by simp)).hasDerivAt
  have hformula := hCderiv.mul_const (f (p 1))
  have heq : (fun y => separatedProduct C f ![y, p 1]) = (fun y => C y * f (p 1)) := rfl
  change HasDerivAt (fun y => separatedProduct C f ![y, p 1])
    (coordPartial 0 (separatedProduct C f) p) (p 0) at hcurve
  rw [heq] at hcurve
  exact hcurve.unique hformula

theorem separatedProduct_partial_t {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (separatedProduct C f) p = C (p 0) * deriv f (p 1) := by
  have hd := (((separatedProduct_contDiffOn hC f hf).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (separatedProduct C f) (fderiv ℝ (separatedProduct C f) p)
      (![p 0, p 1] : Coord) := by simpa only [point_eta] using hd
  have hcurve := hd'.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have hformula := (hf.differentiable (by simp) (p 1)).hasDerivAt.const_mul (C (p 0))
  have heq : (fun y => separatedProduct C f ![p 0, y]) = (fun y => C (p 0) * f y) := rfl
  change HasDerivAt (fun y => separatedProduct C f ![p 0, y])
    (coordPartial 1 (separatedProduct C f) p) (p 1) at hcurve
  rw [heq] at hcurve
  exact hcurve.unique hformula

def taylorCorrection (C : ℝ → ℝ) (a : ℝ) (n : ℕ) : Coord → ℝ :=
  separatedProduct C (normalizedTimePower a (n + 2))

theorem taylorCorrection_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (taylorCorrection C a n) (spatialStrip I) :=
  separatedProduct_contDiffOn hC _ (normalizedTimePower_contDiff a (n + 2))

theorem taylorCorrection_partial_x {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (taylorCorrection C a n) p =
      separatedProduct (deriv C) (normalizedTimePower a (n + 2)) p :=
  separatedProduct_partial_x hC hI _ (normalizedTimePower_contDiff a (n + 2)) hp

theorem taylorCorrection_partial_t {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (taylorCorrection C a n) p =
      separatedProduct C (normalizedTimePower a (n + 1)) p := by
  rw [taylorCorrection, separatedProduct_partial_t hC hI _
    (normalizedTimePower_contDiff a (n + 2)) hp]
  rw [show n + 2 = (n + 1) + 1 by omega, normalizedTimePower_deriv]
  rfl

theorem taylorCorrection_partial_xx {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (coordPartial 0 (taylorCorrection C a n)) p =
      separatedProduct (deriv (deriv C)) (normalizedTimePower a (n + 2)) p := by
  have heq : coordPartial 0 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct (deriv C) (normalizedTimePower a (n + 2)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_x hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 0]
  exact separatedProduct_partial_x (hC.deriv_of_isOpen hI (by simp)) hI _
    (normalizedTimePower_contDiff a (n + 2)) hp

theorem taylorCorrection_partial_xt {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (coordPartial 1 (taylorCorrection C a n)) p =
      separatedProduct (deriv C) (normalizedTimePower a (n + 1)) p := by
  have heq : coordPartial 1 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct C (normalizedTimePower a (n + 1)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_t hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 0]
  exact separatedProduct_partial_x hC hI _ (normalizedTimePower_contDiff a (n + 1)) hp

theorem taylorCorrection_partial_tt {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (coordPartial 1 (taylorCorrection C a n)) p =
      separatedProduct C (normalizedTimePower a n) p := by
  have heq : coordPartial 1 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct C (normalizedTimePower a (n + 1)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_t hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 1,
    separatedProduct_partial_t hC hI _ (normalizedTimePower_contDiff a (n + 1)) hp,
    normalizedTimePower_deriv]
  rfl

theorem taylorCorrection_tt_time_jet {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n k : ℕ)
    {x : ℝ} (hx : x ∈ I) :
    iteratedDeriv k (fun t => coordPartial 1 (coordPartial 1 (taylorCorrection C a n)) ![x, t]) a =
      if k = n then C x else 0 := by
  have heq : (fun t => coordPartial 1 (coordPartial 1 (taylorCorrection C a n)) ![x, t]) =
      (fun t => C x * normalizedTimePower a n t) := by
    funext t
    exact taylorCorrection_partial_tt hC hI a n (p := ![x, t]) hx
  rw [heq]
  exact coefficient_timePower_jet a (C x) n k

end SmoothLocal.Taylor

end

end OAI
