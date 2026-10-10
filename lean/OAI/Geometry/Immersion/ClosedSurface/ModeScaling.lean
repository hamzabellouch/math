import OAI.Geometry.Immersion.ClosedSurface.FreeMean
import OAI.Geometry.Immersion.ClosedSurface.FreeCharts

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_const_smul {n : ℕ} (a : ℂ) {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v : Base) :
    coordDeriv v (fun q => a • Z q) p = a • coordDeriv v Z p := by
  rw [partial_smul (differentiableAt_const a) hZ]
  simp [coordDeriv]

lemma reducedKx_smul {n : ℕ} (a : ℂ) (G V : Field n) (f g : Scalar) :
    reducedKx G (fun p => a • V p) (fun p => a * f p) (fun p => a * g p) =
      fun p => a * reducedKx G V f g p := by
  funext p
  simp only [reducedKx, dotProduct_smul, smul_eq_mul]
  ring

lemma reducedKy_smul {n : ℕ} (a : ℂ) (G V : Field n) (f g : Scalar) :
    reducedKy G (fun p => a • V p) (fun p => a * f p) (fun p => a * g p) =
      fun p => a * reducedKy G V f g p := by
  funext p
  simp only [reducedKy, dotProduct_smul, smul_eq_mul]
  ring

lemma component_const_smul (a : ℂ) (f : Tensor) (i : Fin 3) :
    component (fun p => a • f p) i = fun p => a * component f i p := rfl

lemma amplitudeCorrection_smul {n : ℕ} (a : ℂ) {G V : Field n} {f : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hf : ContDiffAt ℝ ∞ f p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    amplitudeCorrection G (fun q => a • V q) (fun q => a • f q) p =
      a • amplitudeCorrection G V f p := by
  have hy := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hf 1) (contDiffAt_pi.mp hf 2) hD hb
  change ContDiffAt ℝ ∞ (reducedKy G V (component f 1) (component f 2)) p at hy
  simp only [amplitudeCorrection, component_const_smul]
  rw [reducedKx_smul, reducedKy_smul, partial_const_mul (a := a) (hy.differentiableAt (by simp)) dy,
    connectionTerm_mul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma initialAmplitude_smul {n : ℕ} (τ : ℝ) (a : ℂ) {G V : Field n} {f : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hf : ContDiffAt ℝ ∞ f p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G (fun q => a • V q) (fun q => a • f q) p =
      a • initialAmplitude τ G V f p := by
  rw [initialAmplitude_expansion τ hG (hV.const_smul a) (hf.const_smul a) hD hb,
    initialAmplitude_expansion τ hG hV hf hD hb,
    amplitudeCorrection_smul a hG hV hf hD hb]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma conjugatedMetric_smul {n : ℕ} (τ : ℝ) (a : ℂ) (G : Field n) {Z : Field n}
    {p : Base} (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    conjugatedMetric τ G (fun q => a • Z q) v w p = a * conjugatedMetric τ G Z v w p := by
  simp only [conjugatedMetric, linearizedMetric, partial_const_smul a hZ,
    covector, dotProduct_smul, smul_eq_mul]
  ring

lemma conjugatedD_smul {n : ℕ} (τ : ℝ) (a : ℂ) (G : Field n) {Z : Field n}
    {p : Base} (hZ : DifferentiableAt ℝ Z p) :
    conjugatedD τ G (fun q => a • Z q) p = a • conjugatedD τ G Z p := by
  ext i
  fin_cases i <;> simp [conjugatedD, tensorOf, conjugatedMetric_smul τ a G hZ]



theorem modeApprox_smul {n : ℕ} (τ : ℝ) (a : ℂ) {G V : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U) (hV : ContDiffOn ℝ ∞ V U)
    {f : Tensor} (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    EqOn (modeApprox τ G (fun p => a • V p) (fun p => a • f p) q)
      (fun p => a • modeApprox τ G V f q p) U := by
  have atU {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {b : Base → E} (hb : ContDiffOn ℝ ∞ b U) {p : Base} (hp : p ∈ U) :
      ContDiffAt ℝ ∞ b p := (hb p hp).contDiffAt (h.isOpen.mem_nhds hp)
  induction q with
  | zero =>
    intro p hp
    exact initialAmplitude_smul τ a hG.contDiffAt (atU hV hp) (atU hf hp)
      (h.determinant p hp) (h.good p hp)
  | succ q ih =>
    have hZ := contDiffOn_modeApprox τ h hV hf q
    have he : EqOn
        (residual τ G (fun p => a • f p)
          (modeApprox τ G (fun p => a • V p) (fun p => a • f p) q))
        (fun p => a • residual τ G f (modeApprox τ G V f q) p) U := by
      intro p hp
      have hei := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => ih hz)
      unfold residual
      rw [conjugatedD_congr τ G hei,
        conjugatedD_smul τ a G ((atU hZ hp).differentiableAt (by simp))]
      exact (smul_sub a _ _).symm
    intro p hp
    have hee := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => he hz)
    change modeApprox τ G _ _ q p - initialAmplitude τ G (fun _ => 0) _ p = _
    rw [ih hp, initialAmplitude_congr τ G (Filter.EventuallyEq.refl _ _) hee]
    have hh := initialAmplitude_smul τ a hG.contDiffAt (contDiffAt_const (c := (0 : Ambient n)))
      (contDiffAt_residual τ hG.contDiffAt (atU hZ hp) (atU hf hp))
      (h.determinant p hp) (h.good p hp)
    simp only [smul_zero] at hh
    rw [hh]
    simp only [modeApprox, zeroParametrix, smul_sub]

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude zeroPair)

lemma freeSeed_scale (δ τ : ℝ) (b : Base → ℝ) (F : RField 4) :
    freeSeed δ τ b F = fun p => (δ : ℂ) • freeSeed 1 τ b F p := by
  funext p
  ext i
  simp only [freeSeed, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_one]
  ring

lemma chartFreeAmplitude_scale {F : RField 4} {U V : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V) {b : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b V) {χ : Base → Base} (hχV : MapsTo χ U V)
    (δ τ : ℝ) (q : ℕ) :
    EqOn (chartFreeAmplitude δ τ F b q χ)
      (fun p => δ • chartFreeAmplitude 1 τ F b q χ p) U := by
  have hseed := freeSeed_isFree hF h 1 τ hb
  have hFc : ContDiff ℝ ∞ (fun p => complexify (F p)) := (complexifyCLM 4).contDiff.comp hF
  have hh := modeApprox_smul τ (δ : ℂ) hFc
    (h.complexDomain hF) hseed.smooth (f := fun _ => 0) contDiffOn_const q
  intro p hp
  change modeApprox τ _ (freeSeed δ τ b F) _ q (χ p) = _
  rw [freeSeed_scale]
  have he := hh (hχV hp)
  simpa only [smul_zero, chartFreeAmplitude, Function.comp_apply, Complex.coe_smul] using he


lemma phaseFreeFamily_scale {ι : Type*} (a : Finset ι)
    {U V : ι → Set Base} {s r ρ R : ℝ} {reference A : Base → PhaseMean.Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (hρ : 0 < ρ) (hA : ContDiff ℝ ∞ A) (hball : InTrialBall univ reference r A)
    (δ τ : ℝ) (q : ℕ) (i : ι) (hi : i ∈ a) :
    phaseFreeFamily U δ τ F ψ Q χ e q A i =
      fun p => δ • phaseFreeFamily U 1 τ F ψ Q χ e q A i p := by
  funext p
  by_cases hp : p ∈ U i
  · simp only [phaseFreeFamily, indicator_of_mem hp]
    exact chartFreeAmplitude_scale (h i hi).smoothF (h i hi).domain
      ((h i hi).amplitude_smooth hρ hA.contDiffOn (fun p _ => hball p (mem_univ p)))
      (h i hi).chiInto δ τ q hp
  · simp [phaseFreeFamily, hp]

lemma derivativeAmplitude_real_smul {n : ℕ} {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (τ a : ℝ) (φ : Base → ℝ) (v : Base) :
    derivativeAmplitude τ φ (fun p => a • Z p) v p = a • derivativeAmplitude τ φ Z v p := by
  have hh := fderiv_const_smul hZ a
  change fderiv ℝ (fun p => a • Z p) p = _ at hh
  rw [derivativeAmplitude, hh]
  simp only [smul_apply, derivativeAmplitude, smul_add]
  congr 1
  exact smul_comm _ _ _

lemma phaseZeroTensor_real_smul {n : ℕ} {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (τ a : ℝ) (φ : Base → ℝ) :
    phaseZeroTensor τ φ (fun p => a • Z p) p = a ^ 2 • phaseZeroTensor τ φ Z p := by
  ext i
  simp only [phaseZeroTensor, derivativeAmplitude_real_smul hZ,
    QuadraticMean.zeroPair_smul_left, QuadraticMean.zeroPair_smul_right, Pi.smul_apply, smul_eq_mul]
  ring


lemma phaseFreeZero_scale {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r ρ R : ℝ} {reference A : Base → PhaseMean.Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (hρ : 0 < ρ) (hA : ContDiff ℝ ∞ A) (hball : InTrialBall univ reference r A)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    (δ τ : ℝ) (q : ℕ) :
    (fun p => ∑ i ∈ a, phaseZeroTensor τ (fun p => (χ i p).1)
      (phaseFreeFamily U δ τ F ψ Q χ e q A i) p) =
    fun p => δ ^ 2 • (∑ i ∈ a, phaseZeroTensor τ (fun p => (χ i p).1)
      (phaseFreeFamily U 1 τ F ψ Q χ e q A i) p) := by
  funext p
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [phaseFreeFamily_scale a h hρ hA hball δ τ q i hi]
  exact phaseZeroTensor_real_smul
    (((phaseFreeFamily_smooth a h hρ hA hball hS hSU hsp 1 τ q i hi).1).differentiable (by simp) p)
    τ δ _

end ClosedSurfaceR4.RealModes

end

end OAI
