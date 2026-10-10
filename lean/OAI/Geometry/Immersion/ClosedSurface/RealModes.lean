import OAI.Geometry.Immersion.ClosedSurface.MeanError
import OAI.Geometry.Immersion.ClosedSurface.NormalFrame

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates
abbrev RVec (n : ℕ) := Fin n → ℝ
abbrev RField (n : ℕ) := Base → RVec n

def complexifyCLM (n : ℕ) : RVec n →L[ℝ] Ambient n :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

def complexify {n : ℕ} (X : RVec n) : Ambient n := complexifyCLM n X

@[simp] lemma complexify_apply {n : ℕ} (X : RVec n) (i : Fin n) : complexify X i = (X i : ℂ) := rfl

lemma complexify_dot {n : ℕ} (X Y : RVec n) :
    complexify X ⬝ᵥ complexify Y = (X ⬝ᵥ Y : ℝ) := by
  simp [dotProduct, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

lemma complexify_gram (X Y : RVec 4) :
    gramDet (complexify X) (complexify Y) = (NormalFrame.gramDet X Y : ℝ) := by
  simp [gramDet, NormalFrame.gramDet, complexify_dot]

def realNormalPart (X Y W : RVec 4) : RVec 4 :=
  W - (((Y ⬝ᵥ Y) * (X ⬝ᵥ W) - (X ⬝ᵥ Y) * (Y ⬝ᵥ W)) /
    NormalFrame.gramDet X Y) • X -
    (((X ⬝ᵥ X) * (Y ⬝ᵥ W) - (X ⬝ᵥ Y) * (X ⬝ᵥ W)) /
    NormalFrame.gramDet X Y) • Y

lemma complexify_normalPart (X Y W : RVec 4) :
    complexify (realNormalPart X Y W) = normalPart (complexify X) (complexify Y) (complexify W) := by
  ext i
  simp [realNormalPart, normalPart, tangentLift, liftX, liftY, complexify_dot, complexify_gram]
  ring

lemma realNormalPart_perp (X Y W : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    X ⬝ᵥ realNormalPart X Y W = 0 ∧ Y ⬝ᵥ realNormalPart X Y W = 0 := by
  have hd : gramDet (complexify X) (complexify Y) ≠ 0 := by
    rw [complexify_gram]; exact Complex.ofReal_ne_zero.mpr hD
  constructor
  · exact Complex.ofReal_injective (by
      rw [← complexify_dot, complexify_normalPart]; exact dot_normalPart_left _ _ _ hd)
  · exact Complex.ofReal_injective (by
      rw [← complexify_dot, complexify_normalPart]; exact dot_normalPart_right _ _ _ hd)

lemma coordDeriv_complexify {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (v : Base) :
    coordDeriv v (fun q => complexify (F q)) p = complexify (coordDeriv v F p) := by
  exact congrArg (fun A : Base →L[ℝ] Ambient n => A v)
    (((complexifyCLM n).hasFDerivAt.comp p hF.hasFDerivAt).fderiv)

lemma contDiff_complexify {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p => complexify (F p)) := (complexifyCLM n).contDiff.comp hF

lemma contDiff_real_coordDeriv {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v F) := by
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

def realSecond (F : RField 4) : RField 4 := fun p =>
  realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv dy (coordDeriv dy F) p)

lemma complexify_realSecond {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    complexify (realSecond F p) = goodSecond (fun p => complexify (F p)) p := by
  have hd (v : Base) : coordDeriv v (fun q => complexify (F q)) =
      fun q => complexify (coordDeriv v F q) := by
    funext q; exact coordDeriv_complexify (hF.differentiable (by simp) q) v
  unfold realSecond goodSecond secondForm
  rw [hd dx, hd dy, coordDeriv_complexify ((contDiff_real_coordDeriv hF dy).differentiable (by simp) p)]
  exact complexify_normalPart _ _ _


structure RealModeDomain (F : RField 4) (U : Set Base) : Prop where
  isOpen : IsOpen U
  determinant : ∀ p ∈ U, NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0
  good : ∀ p ∈ U, realSecond F p ≠ 0

lemma RealModeDomain.complexDomain {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) :
    ModeDomain (fun p => complexify (F p)) U := by
  refine ⟨h.isOpen, (contDiff_complexify hF).contDiffOn, ?_, ?_⟩
  · intro p hp
    rw [coordDeriv_complexify (hF.differentiable (by simp) p),
      coordDeriv_complexify (hF.differentiable (by simp) p), complexify_gram]
    exact Complex.ofReal_ne_zero.mpr (h.determinant p hp)
  · intro p hp
    rw [← complexify_realSecond hF, complexify_dot]
    exact Complex.ofReal_ne_zero.mpr ((dotProduct_self_eq_zero).not.mpr (h.good p hp))

def freeNormal (F : RField 4) : RField 4 := fun p =>
  NormalFrame.unitPerp (coordDeriv dx F p) (coordDeriv dy F p) (realSecond F p)

lemma freeNormal_perp (F : RField 4) (p : Base) :
    coordDeriv dx F p ⬝ᵥ freeNormal F p = 0 ∧
    coordDeriv dy F p ⬝ᵥ freeNormal F p = 0 ∧ realSecond F p ⬝ᵥ freeNormal F p = 0 :=
  NormalFrame.unitPerp_orthogonal _ _ _

lemma freeNormal_unit {F : RField 4} {U : Set Base} (h : RealModeDomain F U)
    {p : Base} (hp : p ∈ U) : freeNormal F p ⬝ᵥ freeNormal F p = 1 := by
  have hn := realNormalPart_perp (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dy (coordDeriv dy F) p) (h.determinant p hp)
  exact NormalFrame.unitPerp_unit (h.determinant p hp) (h.good p hp) hn.1 hn.2

lemma contDiffOn_realSecond {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) : ContDiffOn ℝ ∞ (realSecond F) U := by
  have hb := (h.complexDomain hF).secondForm dy dy
  apply contDiffOn_pi.mpr
  intro i
  have hi := Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hb i)
  convert hi using 1
  funext p
  exact congrArg Complex.re (congrFun (complexify_realSecond hF p) i)

lemma contDiffOn_freeNormal {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) : ContDiffOn ℝ ∞ (freeNormal F) U := by
  intro p hp
  have hn := realNormalPart_perp (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dy (coordDeriv dy F) p) (h.determinant p hp)
  have hb := ((contDiffOn_realSecond hF h) p hp).contDiffAt (h.isOpen.mem_nhds hp)
  exact (NormalFrame.contDiffAt_unitPerp (contDiff_real_coordDeriv hF dx).contDiffAt
    (contDiff_real_coordDeriv hF dy).contDiffAt hb (h.determinant p hp) (h.good p hp)
    hn.1 hn.2).contDiffWithinAt


def freeSeed (δ τ : ℝ) (b : Base → ℝ) (F : RField 4) : Field 4 := fun p =>
  ((Real.sqrt 2 * δ * τ * b p : ℝ) : ℂ) • complexify (freeNormal F p)

lemma freeSeed_isFree {F : RField 4} {U : Set Base} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F U) (δ τ : ℝ) {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b U) :
    FreeCoefficient (fun p => complexify (F p)) U (freeSeed δ τ b F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha := Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_const (c := Real.sqrt 2 * δ * τ)).mul hb)
    have hn := (complexifyCLM 4).contDiff.comp_contDiffOn (contDiffOn_freeNormal hF h)
    exact ha.smul hn
  · intro p hp
    rw [coordDeriv_complexify (hF.differentiable (by simp) p)]
    simp only [freeSeed, dotProduct_smul, smul_eq_mul, complexify_dot, (freeNormal_perp F p).1,
      Complex.ofReal_zero, mul_zero]
  · intro p hp
    rw [coordDeriv_complexify (hF.differentiable (by simp) p)]
    simp only [freeSeed, dotProduct_smul, smul_eq_mul, complexify_dot, (freeNormal_perp F p).2.1,
      Complex.ofReal_zero, mul_zero]
  · intro p hp
    rw [← complexify_realSecond hF]
    simp only [freeSeed, dotProduct_smul, smul_eq_mul, complexify_dot, (freeNormal_perp F p).2.2,
      Complex.ofReal_zero, mul_zero]

lemma leadingDerivative_freeSeed {τ : ℝ} (hτ : τ ≠ 0) (δ : ℝ) (b : Base → ℝ)
    (F : RField 4) (v p : Base) :
    leadingDerivative τ (freeSeed δ τ b F) v p =
      ClosedSurfaceR4.QuadraticMean.leadingAmplitude δ (b p) v.1 (freeNormal F p) := by
  ext i
  have htc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  simp only [leadingDerivative, freeSeed, Pi.smul_apply, smul_eq_mul, complexify_apply,
    ClosedSurfaceR4.QuadraticMean.leadingAmplitude, Complex.ofReal_mul]
  field_simp



theorem freeSeed_zeroPair {F : RField 4} {U : Set Base} (h : RealModeDomain F U)
    {τ : ℝ} (hτ : τ ≠ 0) (δ : ℝ) (b : Base → ℝ) (v w : Base) {p : Base} (hp : p ∈ U) :
    ClosedSurfaceR4.QuadraticMean.zeroPair (leadingDerivative τ (freeSeed δ τ b F) v p)
      (leadingDerivative τ (freeSeed δ τ b F) w p) = δ ^ 2 * b p ^ 2 * v.1 * w.1 := by
  rw [leadingDerivative_freeSeed hτ, leadingDerivative_freeSeed hτ]
  exact ClosedSurfaceR4.QuadraticMean.leadingAmplitude_zeroPair _ _ _ _ _ (freeNormal_unit h hp)



theorem finiteMode_mean_identity {F : RField 4} {U : Set Base} (h : RealModeDomain F U)
    {τ : ℝ} (hτ : τ ≠ 0) (δ : ℝ) (b : Base → ℝ) (q : ℕ) (v w : Base)
    {p : Base} (hp : p ∈ U) :
    ClosedSurfaceR4.QuadraticMean.zeroPair
      (gradientAmplitude τ (modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ b F)
        (fun _ => 0) q) v p)
      (gradientAmplitude τ (modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ b F)
        (fun _ => 0) q) w p) = δ ^ 2 * b p ^ 2 * v.1 * w.1 +
      modeMeanError τ (fun p => complexify (F p)) (freeSeed δ τ b F) (freeSeed δ τ b F) q v w p := by
  unfold modeMeanError
  rw [freeSeed_zeroPair h hτ δ b v w hp]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
