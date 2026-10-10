import Mathlib

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

abbrev Base := ℝ × ℝ
abbrev Ambient (n : ℕ) := Fin n → ℂ
abbrev Field (n : ℕ) := Base → Ambient n
abbrev Scalar := Base → ℂ

def dx : Base := (1, 0)
def dy : Base := (0, 1)

def coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Base) (F : Base → E) (p : Base) : E := fderiv ℝ F p v

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

lemma partial_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q - G q) p = coordDeriv v F p - coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_sub hF hG, sub_apply]

lemma partial_dot {n : ℕ} {F G : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q ⬝ᵥ G q) p = coordDeriv v F p ⬝ᵥ G p + F p ⬝ᵥ coordDeriv v G p := by
  have hf (i : Fin n) := ((ContinuousLinearMap.proj i : Ambient n →L[ℝ] ℂ).hasFDerivAt.comp p
    hF.hasFDerivAt)
  have hg (i : Fin n) := ((ContinuousLinearMap.proj i : Ambient n →L[ℝ] ℂ).hasFDerivAt.comp p
    hG.hasFDerivAt)
  have hs := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hf i).fun_mul (hg i)).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at hs
  unfold coordDeriv dotProduct
  rw [hs]
  simp only [sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma partial_smul {n : ℕ} {a : Scalar} {F : Field n} {p : Base}
    (ha : DifferentiableAt ℝ a p) (hF : DifferentiableAt ℝ F p) (v : Base) :
    coordDeriv v (fun q => a q • F q) p = a p • coordDeriv v F p + coordDeriv v a p • F p := by
  have hs := (ha.hasFDerivAt.fun_smul hF.hasFDerivAt).fderiv
  simp only [coordDeriv, hs, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]



def metric {n : ℕ} (G : Field n) (v w : Base) (p : Base) : ℂ :=
  coordDeriv v G p ⬝ᵥ coordDeriv w G p


def linearizedMetric {n : ℕ} (G Z : Field n) (v w : Base) (p : Base) : ℂ :=
  coordDeriv v G p ⬝ᵥ coordDeriv w Z p + coordDeriv w G p ⬝ᵥ coordDeriv v Z p

lemma metric_add {n : ℕ} {G Z : Field n} {p : Base}
    (hG : DifferentiableAt ℝ G p) (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    metric (fun q => G q + Z q) v w p =
      metric G v w p + linearizedMetric G Z v w p + metric Z v w p := by
  simp only [metric, partial_add hG hZ, add_dotProduct, dotProduct_add, linearizedMetric]
  rw [dotProduct_comm (coordDeriv v Z p) (coordDeriv w G p)]
  ring

section Gram
variable {n : ℕ}

def gramDet (X Y : Ambient n) : ℂ := (X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) ^ 2

def liftX (X Y : Ambient n) (ux uy : ℂ) : ℂ :=
  ((Y ⬝ᵥ Y) * ux - (X ⬝ᵥ Y) * uy) / gramDet X Y

def liftY (X Y : Ambient n) (ux uy : ℂ) : ℂ :=
  ((X ⬝ᵥ X) * uy - (X ⬝ᵥ Y) * ux) / gramDet X Y


def tangentLift (X Y : Ambient n) (ux uy : ℂ) : Ambient n :=
  liftX X Y ux uy • X + liftY X Y ux uy • Y

lemma dot_tangentLift_left (X Y : Ambient n) (hD : gramDet X Y ≠ 0) (ux uy : ℂ) :
    X ⬝ᵥ tangentLift X Y ux uy = ux := by
  simp only [tangentLift, dotProduct_add, dotProduct_smul, smul_eq_mul, liftX, liftY]
  field_simp
  simp only [gramDet] at *
  ring

lemma dot_tangentLift_right (X Y : Ambient n) (hD : gramDet X Y ≠ 0) (ux uy : ℂ) :
    Y ⬝ᵥ tangentLift X Y ux uy = uy := by
  simp only [tangentLift, dotProduct_add, dotProduct_smul, smul_eq_mul, liftX, liftY,
    dotProduct_comm Y X]
  field_simp
  simp only [gramDet] at *
  ring


def normalPart (X Y W : Ambient n) : Ambient n :=
  W - tangentLift X Y (X ⬝ᵥ W) (Y ⬝ᵥ W)

lemma dot_normalPart_left (X Y W : Ambient n) (hD : gramDet X Y ≠ 0) :
    X ⬝ᵥ normalPart X Y W = 0 := by
  simp only [normalPart, dotProduct_sub, dot_tangentLift_left X Y hD, sub_self]

lemma dot_normalPart_right (X Y W : Ambient n) (hD : gramDet X Y ≠ 0) :
    Y ⬝ᵥ normalPart X Y W = 0 := by
  simp only [normalPart, dotProduct_sub, dot_tangentLift_right X Y hD, sub_self]

lemma second_dot_split (X Y W Z : Ambient n) :
    W ⬝ᵥ Z = liftX X Y (X ⬝ᵥ W) (Y ⬝ᵥ W) * (X ⬝ᵥ Z) +
      liftY X Y (X ⬝ᵥ W) (Y ⬝ᵥ W) * (Y ⬝ᵥ Z) + normalPart X Y W ⬝ᵥ Z := by
  simp only [normalPart, tangentLift, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

lemma dot_normal_tangentLift (X Y B : Ambient n) (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0)
    (ux uy : ℂ) : B ⬝ᵥ tangentLift X Y ux uy = 0 := by
  simp only [tangentLift, dotProduct_add, dotProduct_smul, smul_eq_mul,
    dotProduct_comm B X, dotProduct_comm B Y, hX, hY, mul_zero, add_zero]

lemma normalPart_dot_reconstruct (X Y W Z V : Ambient n) (hD : gramDet X Y ≠ 0)
    (ux uy : ℂ) (hZ : Z = tangentLift X Y ux uy + V) :
    normalPart X Y W ⬝ᵥ Z = normalPart X Y W ⬝ᵥ V := by
  rw [hZ, dotProduct_add, dot_normal_tangentLift X Y _
    (dot_normalPart_left X Y W hD) (dot_normalPart_right X Y W hD), zero_add]

end Gram

section CoordinateCalculus
variable {n : ℕ}

lemma contDiff_coordDeriv {G : Field n} (hG : ContDiff ℝ ∞ G) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma second_coordDeriv {G : Field n} {p : Base}
    (hG : DifferentiableAt ℝ (fderiv ℝ G) p) (v w : Base) :
    coordDeriv v (coordDeriv w G) p = fderiv ℝ (fderiv ℝ G) p v w := by
  have h := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ G q) w) p) v = _
  rw [h]
  simp

lemma second_coordDeriv_comm {G : Field n} (hG : ContDiff ℝ ∞ G)
    (p v w : Base) : coordDeriv v (coordDeriv w G) p = coordDeriv w (coordDeriv v G) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) p :=
    ((hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  rw [second_coordDeriv hd, second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hG.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w



def secondForm (G : Field n) (v w : Base) (p : Base) : Ambient n :=
  normalPart (coordDeriv dx G p) (coordDeriv dy G p) (coordDeriv v (coordDeriv w G) p)

def connectionX (G : Field n) (v w : Base) (p : Base) : ℂ :=
  liftX (coordDeriv dx G p) (coordDeriv dy G p)
    (coordDeriv dx G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)
    (coordDeriv dy G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)

def connectionY (G : Field n) (v w : Base) (p : Base) : ℂ :=
  liftY (coordDeriv dx G p) (coordDeriv dy G p)
    (coordDeriv dx G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)
    (coordDeriv dy G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)

def covector (G Z : Field n) (v : Base) (p : Base) : ℂ := coordDeriv v G p ⬝ᵥ Z p

lemma linearizedMetric_covector {G Z : Field n} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    linearizedMetric G Z v w p =
      coordDeriv v (covector G Z w) p + coordDeriv w (covector G Z v) p -
        2 * (coordDeriv v (coordDeriv w G) p ⬝ᵥ Z p) := by
  unfold covector
  rw [partial_dot (((contDiff_coordDeriv hG w).differentiable (by simp)).differentiableAt) hZ,
    partial_dot (((contDiff_coordDeriv hG v).differentiable (by simp)).differentiableAt) hZ,
    second_coordDeriv_comm hG p w v]
  unfold linearizedMetric
  ring

lemma linearizedMetric_connection {G Z : Field n} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    linearizedMetric G Z v w p =
      coordDeriv v (covector G Z w) p + coordDeriv w (covector G Z v) p -
      2 * (connectionX G v w p * covector G Z dx p +
        connectionY G v w p * covector G Z dy p) - 2 * (secondForm G v w p ⬝ᵥ Z p) := by
  rw [linearizedMetric_covector hG hZ]
  unfold connectionX connectionY secondForm covector
  rw [second_dot_split (coordDeriv dx G p) (coordDeriv dy G p)
    (coordDeriv v (coordDeriv w G) p) (Z p)]
  ring

lemma covector_reconstruct {G V : Field n} {ux uy : Scalar} {p : Base}
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hX : coordDeriv dx G p ⬝ᵥ V p = 0) (hY : coordDeriv dy G p ⬝ᵥ V p = 0) :
    let Z : Field n := fun q => tangentLift (coordDeriv dx G q) (coordDeriv dy G q) (ux q) (uy q) + V q
    covector G Z dx p = ux p ∧ covector G Z dy p = uy p := by
  simp only [covector, dotProduct_add, dot_tangentLift_left _ _ hD,
    dot_tangentLift_right _ _ hD, hX, hY, add_zero, and_self]

end CoordinateCalculus

section Phase
variable {n : ℕ}


def unitMode (τ : ℝ) (p : Base) : ℂ :=
  Complex.exp (Complex.I / (τ : ℂ) * (p.1 : ℂ))

def oscillate (τ : ℝ) (Z : Field n) : Field n := fun p => unitMode τ p • Z p

lemma unitMode_hasFDerivAt (τ : ℝ) (p : Base) :
    HasFDerivAt (unitMode τ)
      (unitMode τ p • ((Complex.I / (τ : ℂ)) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)))) p := by
  exact ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasFDerivAt.const_mul
    (Complex.I / (τ : ℂ))).cexp

lemma coordDeriv_unitMode (τ : ℝ) (p v : Base) :
    coordDeriv v (unitMode τ) p = unitMode τ p * (Complex.I / (τ : ℂ)) * (v.1 : ℂ) := by
  unfold coordDeriv
  rw [(unitMode_hasFDerivAt τ p).fderiv]
  simp [mul_assoc]

lemma coordDeriv_oscillate (τ : ℝ) {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v : Base) :
    coordDeriv v (oscillate τ Z) p = unitMode τ p •
      (coordDeriv v Z p + ((Complex.I / (τ : ℂ)) * (v.1 : ℂ)) • Z p) := by
  change coordDeriv v (fun q => unitMode τ q • Z q) p = _
  rw [partial_smul (unitMode_hasFDerivAt τ p).differentiableAt hZ, coordDeriv_unitMode]
  simp only [smul_add, smul_smul]
  rw [mul_assoc, add_comm]


def conjugatedMetric (τ : ℝ) (G Z : Field n) (v w : Base) (p : Base) : ℂ :=
  linearizedMetric G Z v w p + (Complex.I / (τ : ℂ)) *
    ((v.1 : ℂ) * covector G Z w p + (w.1 : ℂ) * covector G Z v p)

lemma linearizedMetric_oscillate (τ : ℝ) {G Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    linearizedMetric G (oscillate τ Z) v w p =
      unitMode τ p * conjugatedMetric τ G Z v w p := by
  unfold conjugatedMetric linearizedMetric covector
  rw [coordDeriv_oscillate τ hZ w, coordDeriv_oscillate τ hZ v]
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul]
  ring

lemma conjugatedMetric_connection (τ : ℝ) {G Z : Field n}
    (hG : ContDiff ℝ ∞ G) {p : Base} (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    conjugatedMetric τ G Z v w p =
      coordDeriv v (covector G Z w) p + coordDeriv w (covector G Z v) p -
      2 * (connectionX G v w p * covector G Z dx p +
        connectionY G v w p * covector G Z dy p) + (Complex.I / (τ : ℂ)) *
      ((v.1 : ℂ) * covector G Z w p + (w.1 : ℂ) * covector G Z v p) -
      2 * (secondForm G v w p ⬝ᵥ Z p) := by
  unfold conjugatedMetric
  rw [linearizedMetric_connection hG hZ]
  ring

end Phase

section Elimination
variable {n : ℕ}


def reconstruct (G : Field n) (ux uy : Scalar) (V : Field n) : Field n :=
  fun p => tangentLift (coordDeriv dx G p) (coordDeriv dy G p) (ux p) (uy p) + V p

def connectionTerm (G : Field n) (ux uy : Scalar) (v w : Base) (p : Base) : ℂ :=
  connectionX G v w p * ux p + connectionY G v w p * uy p

lemma covector_reconstruct_eventually {G V : Field n} {ux uy : Scalar} {p : Base}
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    covector G (reconstruct G ux uy V) dx =ᶠ[nhds p] ux ∧
      covector G (reconstruct G ux uy V) dy =ᶠ[nhds p] uy := by
  have hh : ∀ᶠ q in nhds p, covector G (reconstruct G ux uy V) dx q = ux q ∧
      covector G (reconstruct G ux uy V) dy q = uy q := by
    filter_upwards [hD, hX, hY] with q hDq hXq hYq
    exact covector_reconstruct hDq hXq hYq
  exact ⟨hh.mono fun _ h => h.1, hh.mono fun _ h => h.2⟩

lemma secondForm_dot_reconstruct {G V : Field n} {ux uy : Scalar} {p : Base}
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    secondForm G v w p ⬝ᵥ reconstruct G ux uy V p = secondForm G v w p ⬝ᵥ V p := by
  exact normalPart_dot_reconstruct _ _ _ _ _ hD (ux p) (uy p) rfl

lemma conjugatedMetric_reconstruct_xx (τ : ℝ) {G V : Field n} {ux uy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy V) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    conjugatedMetric τ G (reconstruct G ux uy V) dx dx p =
      2 * ((Complex.I / (τ : ℂ)) * ux p + coordDeriv dx ux p -
        connectionTerm G ux uy dx dx p - secondForm G dx dx p ⬝ᵥ V p) := by
  obtain ⟨hx, hy⟩ := covector_reconstruct_eventually hD hX hY (ux := ux) (uy := uy)
  rw [conjugatedMetric_connection τ hG hZ, secondForm_dot_reconstruct hD.self_of_nhds]
  simp only [coordDeriv, hx.fderiv_eq, hx.self_of_nhds,
    hy.self_of_nhds, connectionTerm]
  simp only [dx, Complex.ofReal_one, one_mul]
  ring

lemma conjugatedMetric_reconstruct_xy (τ : ℝ) {G V : Field n} {ux uy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy V) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    conjugatedMetric τ G (reconstruct G ux uy V) dx dy p =
      (Complex.I / (τ : ℂ)) * uy p + coordDeriv dx uy p + coordDeriv dy ux p -
        2 * connectionTerm G ux uy dx dy p - 2 * (secondForm G dx dy p ⬝ᵥ V p) := by
  obtain ⟨hx, hy⟩ := covector_reconstruct_eventually hD hX hY (ux := ux) (uy := uy)
  rw [conjugatedMetric_connection τ hG hZ, secondForm_dot_reconstruct hD.self_of_nhds]
  simp only [coordDeriv, hx.fderiv_eq, hy.fderiv_eq, hx.self_of_nhds,
    hy.self_of_nhds, connectionTerm]
  simp only [dx, dy, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
  ring

lemma conjugatedMetric_reconstruct_yy (τ : ℝ) {G V : Field n} {ux uy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy V) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    conjugatedMetric τ G (reconstruct G ux uy V) dy dy p =
      2 * (coordDeriv dy uy p - connectionTerm G ux uy dy dy p -
        secondForm G dy dy p ⬝ᵥ V p) := by
  obtain ⟨hx, hy⟩ := covector_reconstruct_eventually hD hX hY (ux := ux) (uy := uy)
  rw [conjugatedMetric_connection τ hG hZ, secondForm_dot_reconstruct hD.self_of_nhds]
  simp only [coordDeriv, hy.fderiv_eq, hx.self_of_nhds,
    hy.self_of_nhds, connectionTerm]
  simp only [dy, Complex.ofReal_zero, zero_mul, add_zero, mul_zero]
  ring


def goodSecond (G : Field n) : Field n := secondForm G dy dy

def secondRatio (G : Field n) (v w : Base) (p : Base) : ℂ :=
  (secondForm G v w p ⬝ᵥ goodSecond G p) / (goodSecond G p ⬝ᵥ goodSecond G p)


def normalElimination (G V₀ : Field n) (ux uy hyy : Scalar) : Field n := fun p =>
  V₀ p + ((coordDeriv dy uy p - connectionTerm G ux uy dy dy p - hyy p / 2) /
    (goodSecond G p ⬝ᵥ goodSecond G p)) • goodSecond G p

lemma dot_normalElimination (G V₀ : Field n) (ux uy hyy : Scalar) (p v w : Base) :
    secondForm G v w p ⬝ᵥ normalElimination G V₀ ux uy hyy p =
      secondForm G v w p ⬝ᵥ V₀ p + secondRatio G v w p *
        (coordDeriv dy uy p - connectionTerm G ux uy dy dy p - hyy p / 2) := by
  simp only [normalElimination, dotProduct_add, dotProduct_smul, smul_eq_mul, secondRatio]
  ring

lemma dot_normalElimination_yy (G V₀ : Field n) (ux uy hyy : Scalar) (p : Base)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V₀ p = 0) :
    secondForm G dy dy p ⬝ᵥ normalElimination G V₀ ux uy hyy p =
      coordDeriv dy uy p - connectionTerm G ux uy dy dy p - hyy p / 2 := by
  rw [dot_normalElimination]
  change goodSecond G p ⬝ᵥ V₀ p +
    (goodSecond G p ⬝ᵥ goodSecond G p) / (goodSecond G p ⬝ᵥ goodSecond G p) * _ = _
  rw [hV, div_self hb, one_mul, zero_add]

lemma normalElimination_perp {G V₀ : Field n} {ux uy hyy : Scalar} {p : Base}
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hX : coordDeriv dx G p ⬝ᵥ V₀ p = 0)
    (hY : coordDeriv dy G p ⬝ᵥ V₀ p = 0) :
    coordDeriv dx G p ⬝ᵥ normalElimination G V₀ ux uy hyy p = 0 ∧
    coordDeriv dy G p ⬝ᵥ normalElimination G V₀ ux uy hyy p = 0 := by
  simp only [normalElimination, dotProduct_add, dotProduct_smul, smul_eq_mul, hX, hY,
    goodSecond, secondForm, dot_normalPart_left _ _ _ hD, dot_normalPart_right _ _ _ hD,
    mul_zero, zero_add, and_self]

lemma normalElimination_perp_eventually {G V₀ : Field n} {ux uy hyy : Scalar} {p : Base}
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V₀ q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V₀ q = 0) :
    (∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0) ∧
    (∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0) := by
  have hh : ∀ᶠ q in nhds p,
      coordDeriv dx G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0 ∧
      coordDeriv dy G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0 := by
    filter_upwards [hD, hX, hY] with q hd hx hy
    exact normalElimination_perp hd hx hy
  exact ⟨hh.mono fun _ h => h.1, hh.mono fun _ h => h.2⟩


def reducedLx (G : Field n) (ux uy : Scalar) (p : Base) : ℂ :=
  coordDeriv dx ux p - connectionTerm G ux uy dx dx p -
    secondRatio G dx dx p * (coordDeriv dy uy p - connectionTerm G ux uy dy dy p)

def reducedLy (G : Field n) (ux uy : Scalar) (p : Base) : ℂ :=
  coordDeriv dx uy p + coordDeriv dy ux p - 2 * connectionTerm G ux uy dx dy p -
    2 * secondRatio G dx dy p * (coordDeriv dy uy p - connectionTerm G ux uy dy dy p)


def reducedKx (G V₀ : Field n) (hxx hyy : Scalar) (p : Base) : ℂ :=
  hxx p / 2 + secondForm G dx dx p ⬝ᵥ V₀ p - secondRatio G dx dx p * hyy p / 2

def reducedKy (G V₀ : Field n) (hxy hyy : Scalar) (p : Base) : ℂ :=
  hxy p + 2 * (secondForm G dx dy p ⬝ᵥ V₀ p) - secondRatio G dx dy p * hyy p



theorem normalElimination_residual (τ : ℝ) {G V₀ : Field n} {ux uy hxx hxy hyy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy (normalElimination G V₀ ux uy hyy)) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V₀ q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V₀ q = 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V₀ p = 0) :
    let Z := reconstruct G ux uy (normalElimination G V₀ ux uy hyy)
    (conjugatedMetric τ G Z dx dx p - hxx p =
      2 * ((Complex.I / (τ : ℂ)) * ux p + reducedLx G ux uy p - reducedKx G V₀ hxx hyy p)) ∧
    (conjugatedMetric τ G Z dx dy p - hxy p =
      (Complex.I / (τ : ℂ)) * uy p + reducedLy G ux uy p - reducedKy G V₀ hxy hyy p) ∧
    conjugatedMetric τ G Z dy dy p = hyy p := by
  obtain ⟨hx, hy⟩ := normalElimination_perp_eventually hD hX hY
    (ux := ux) (uy := uy) (hyy := hyy)
  constructor
  · rw [conjugatedMetric_reconstruct_xx τ hG hZ hD hx hy, dot_normalElimination]
    unfold reducedLx reducedKx
    ring
  constructor
  · rw [conjugatedMetric_reconstruct_xy τ hG hZ hD hx hy, dot_normalElimination]
    unfold reducedLy reducedKy
    ring
  · rw [conjugatedMetric_reconstruct_yy τ hG hZ hD hx hy,
      dot_normalElimination_yy G V₀ ux uy hyy p hb hV]
    ring

end Elimination

section Parametrix
variable {n : ℕ}


def firstCovectorX (τ : ℝ) (G V₀ : Field n) (hxx hyy : Scalar) : Scalar :=
  fun p => ((τ : ℂ) / Complex.I) * reducedKx G V₀ hxx hyy p

def firstCovectorY (τ : ℝ) (G V₀ : Field n) (hxy hyy : Scalar) : Scalar :=
  fun p => ((τ : ℂ) / Complex.I) * reducedKy G V₀ hxy hyy p

def firstParametrix (τ : ℝ) (G V₀ : Field n) (hxx hxy hyy : Scalar) : Field n :=
  let ux := firstCovectorX τ G V₀ hxx hyy
  let uy := firstCovectorY τ G V₀ hxy hyy
  reconstruct G ux uy (normalElimination G V₀ ux uy hyy)

lemma conjugating_inverse {τ : ℝ} (hτ : τ ≠ 0) :
    (Complex.I / (τ : ℂ)) * ((τ : ℂ) / Complex.I) = 1 := by
  have htc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  field_simp

lemma firstParametrix_residual {τ : ℝ} (hτ : τ ≠ 0) {G V₀ : Field n}
    {hxx hxy hyy : Scalar} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (firstParametrix τ G V₀ hxx hxy hyy) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V₀ q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V₀ q = 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V₀ p = 0) :
    let ux := firstCovectorX τ G V₀ hxx hyy
    let uy := firstCovectorY τ G V₀ hxy hyy
    let Z := firstParametrix τ G V₀ hxx hxy hyy
    (conjugatedMetric τ G Z dx dx p - hxx p = 2 * reducedLx G ux uy p) ∧
    (conjugatedMetric τ G Z dx dy p - hxy p = reducedLy G ux uy p) ∧
    conjugatedMetric τ G Z dy dy p = hyy p := by
  obtain ⟨hxx', hxy', hyy'⟩ := normalElimination_residual τ hG hZ hD hX hY hb hV
    (hxx := hxx) (hxy := hxy) (hyy := hyy)
  refine ⟨hxx'.trans ?_, hxy'.trans ?_, hyy'⟩
  · simp only [firstCovectorX, ← mul_assoc, conjugating_inverse hτ, one_mul]
    ring
  · simp only [firstCovectorY, ← mul_assoc, conjugating_inverse hτ, one_mul]
    ring

end Parametrix

section SmoothFormulas
variable {n : ℕ}

lemma contDiffAt_dot {F G : Field n} {p : Base}
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p) :
    ContDiffAt ℝ ∞ (fun q => F q ⬝ᵥ G q) p := by
  unfold dotProduct
  exact ContDiffAt.sum fun i _ => (contDiffAt_pi.mp hF i).mul (contDiffAt_pi.mp hG i)

lemma contDiffAt_cdiv {a b : Scalar} {p : Base}
    (ha : ContDiffAt ℝ ∞ a p) (hb : ContDiffAt ℝ ∞ b p) (hne : b p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => a q / b q) p := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.fun_inv hne)

lemma contDiffAt_coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Base → E} {p : Base} (hG : ContDiffAt ℝ ∞ G p) (v : Base) :
    ContDiffAt ℝ ∞ (coordDeriv v G) p :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contDiffAt_gramDet {X Y : Field n} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) :
    ContDiffAt ℝ ∞ (fun q => gramDet (X q) (Y q)) p :=
  ((contDiffAt_dot hX hX).mul (contDiffAt_dot hY hY)).sub ((contDiffAt_dot hX hY).pow 2)

lemma contDiffAt_liftX {X Y : Field n} {ux uy : Scalar} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftX (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hY hY).mul hx).sub ((contDiffAt_dot hX hY).mul hy))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_liftY {X Y : Field n} {ux uy : Scalar} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftY (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hX hX).mul hy).sub ((contDiffAt_dot hX hY).mul hx))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_tangentLift {X Y : Field n} {ux uy : Scalar} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => tangentLift (X q) (Y q) (ux q) (uy q)) p :=
  ((contDiffAt_liftX hX hY hx hy hD).smul hX).add ((contDiffAt_liftY hX hY hx hy hD).smul hY)

lemma contDiffAt_normalPart {X Y W : Field n} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) (hW : ContDiffAt ℝ ∞ W p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => normalPart (X q) (Y q) (W q)) p :=
  hW.sub (contDiffAt_tangentLift hX hY (contDiffAt_dot hX hW) (contDiffAt_dot hY hW) hD)

lemma contDiffAt_secondForm {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (secondForm G v w) p :=
  contDiffAt_normalPart (contDiffAt_coordDeriv hG dx) (contDiffAt_coordDeriv hG dy)
    (contDiffAt_coordDeriv (contDiffAt_coordDeriv hG w) v) hD

lemma contDiffAt_connectionX {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (connectionX G v w) p := by
  have hX := contDiffAt_coordDeriv hG dx
  have hY := contDiffAt_coordDeriv hG dy
  have hSec := contDiffAt_coordDeriv (contDiffAt_coordDeriv hG w) v
  exact contDiffAt_liftX hX hY (contDiffAt_dot hX hSec) (contDiffAt_dot hY hSec) hD

lemma contDiffAt_connectionY {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (connectionY G v w) p := by
  have hX := contDiffAt_coordDeriv hG dx
  have hY := contDiffAt_coordDeriv hG dy
  have hSec := contDiffAt_coordDeriv (contDiffAt_coordDeriv hG w) v
  exact contDiffAt_liftY hX hY (contDiffAt_dot hX hSec) (contDiffAt_dot hY hSec) hD

lemma contDiffAt_connectionTerm {G : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (connectionTerm G ux uy v w) p :=
  ((contDiffAt_connectionX hG hD v w).mul hx).add ((contDiffAt_connectionY hG hD v w).mul hy)

lemma contDiffAt_secondRatio {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (secondRatio G v w) p :=
  contDiffAt_cdiv (contDiffAt_dot (contDiffAt_secondForm hG hD v w)
    (contDiffAt_secondForm hG hD dy dy))
    (contDiffAt_dot (contDiffAt_secondForm hG hD dy dy) (contDiffAt_secondForm hG hD dy dy)) hb

lemma contDiffAt_reconstruct {G V : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) :
    ContDiffAt ℝ ∞ (reconstruct G ux uy V) p :=
  (contDiffAt_tangentLift (contDiffAt_coordDeriv hG dx) (contDiffAt_coordDeriv hG dy) hx hy hD).add hV

lemma contDiffAt_normalElimination {G V : Field n} {ux uy hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p) (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (normalElimination G V ux uy hyy) p := by
  have hB := contDiffAt_secondForm hG hD dy dy
  exact hV.add ((contDiffAt_cdiv
    (((contDiffAt_coordDeriv hy dy).sub (contDiffAt_connectionTerm hG hx hy hD dy dy)).sub
      (hyy'.div_const 2)) (contDiffAt_dot hB hB) hb).smul hB)

lemma contDiffAt_reducedKx {G V : Field n} {hxx hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hxx' : ContDiffAt ℝ ∞ hxx p) (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedKx G V hxx hyy) p :=
  ((hxx'.div_const 2).add (contDiffAt_dot (contDiffAt_secondForm hG hD dx dx) hV)).sub
    (((contDiffAt_secondRatio hG hD hb dx dx).mul hyy').div_const 2)

lemma contDiffAt_reducedKy {G V : Field n} {hxy hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hxy' : ContDiffAt ℝ ∞ hxy p) (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedKy G V hxy hyy) p :=
  (hxy'.add (contDiffAt_const.mul (contDiffAt_dot (contDiffAt_secondForm hG hD dx dy) hV))).sub
    ((contDiffAt_secondRatio hG hD hb dx dy).mul hyy')

lemma contDiffAt_firstParametrix (τ : ℝ) {G V : Field n} {hxx hxy hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hxx' : ContDiffAt ℝ ∞ hxx p) (hxy' : ContDiffAt ℝ ∞ hxy p)
    (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (firstParametrix τ G V hxx hxy hyy) p := by
  have hx : ContDiffAt ℝ ∞ (firstCovectorX τ G V hxx hyy) p :=
    contDiffAt_const.mul (contDiffAt_reducedKx hG hV hxx' hyy' hD hb)
  have hy : ContDiffAt ℝ ∞ (firstCovectorY τ G V hxy hyy) p :=
    contDiffAt_const.mul (contDiffAt_reducedKy hG hV hxy' hyy' hD hb)
  exact contDiffAt_reconstruct hG
    (contDiffAt_normalElimination hG hV hx hy hyy' hD hb) hx hy hD

end SmoothFormulas

section LinearStructure
variable {n : ℕ}

lemma partial_const_mul {a : ℂ} {f : Scalar} {p : Base}
    (hf : DifferentiableAt ℝ f p) (v : Base) :
    coordDeriv v (fun q => a * f q) p = a * coordDeriv v f p := by
  have hh := (hf.hasFDerivAt.const_mul a).fderiv
  simp only [coordDeriv, hh, smul_apply, smul_eq_mul]

lemma tangentLift_mul (X Y : Ambient n) (a ux uy : ℂ) :
    tangentLift X Y (a * ux) (a * uy) = a • tangentLift X Y ux uy := by
  have hx : liftX X Y (a * ux) (a * uy) = a * liftX X Y ux uy := by
    unfold liftX
    ring
  have hy : liftY X Y (a * ux) (a * uy) = a * liftY X Y ux uy := by
    unfold liftY
    ring
  simp only [tangentLift, hx, hy, smul_add, smul_smul]

lemma connectionTerm_mul (G : Field n) (ux uy : Scalar) (p v w : Base) (a : ℂ) :
    connectionTerm G (fun q => a * ux q) (fun q => a * uy q) v w p =
      a * connectionTerm G ux uy v w p := by
  unfold connectionTerm
  ring

lemma reducedLx_mul (G : Field n) {ux uy : Scalar} {p : Base}
    (hx : DifferentiableAt ℝ ux p) (hy : DifferentiableAt ℝ uy p) (a : ℂ) :
    reducedLx G (fun q => a * ux q) (fun q => a * uy q) p = a * reducedLx G ux uy p := by
  unfold reducedLx
  rw [partial_const_mul hx, partial_const_mul hy, connectionTerm_mul, connectionTerm_mul]
  ring

lemma reducedLy_mul (G : Field n) {ux uy : Scalar} {p : Base}
    (hx : DifferentiableAt ℝ ux p) (hy : DifferentiableAt ℝ uy p) (a : ℂ) :
    reducedLy G (fun q => a * ux q) (fun q => a * uy q) p = a * reducedLy G ux uy p := by
  unfold reducedLy
  rw [partial_const_mul hx, partial_const_mul hy, partial_const_mul hy,
    connectionTerm_mul, connectionTerm_mul]
  ring

lemma conjugatedMetric_sub (τ : ℝ) (G : Field n) {Z W : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (v w : Base) :
    conjugatedMetric τ G (fun q => Z q - W q) v w p =
      conjugatedMetric τ G Z v w p - conjugatedMetric τ G W v w p := by
  unfold conjugatedMetric linearizedMetric covector
  rw [partial_sub hZ hW, partial_sub hZ hW]
  simp only [dotProduct_sub]
  ring

lemma contDiffAt_conjugatedMetric (τ : ℝ) {G Z : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hZ : ContDiffAt ℝ ∞ Z p) (v w : Base) :
    ContDiffAt ℝ ∞ (conjugatedMetric τ G Z v w) p := by
  have hX := contDiffAt_coordDeriv hG v
  have hY := contDiffAt_coordDeriv hG w
  have hZv := contDiffAt_coordDeriv hZ v
  have hZw := contDiffAt_coordDeriv hZ w
  exact ((contDiffAt_dot hX hZw).add (contDiffAt_dot hY hZv)).add
    (contDiffAt_const.mul ((contDiffAt_const.mul (contDiffAt_dot hY hZ)).add
      (contDiffAt_const.mul (contDiffAt_dot hX hZ))))


abbrev Tensor := Base → Fin 3 → ℂ

def tensorOf (hxx hxy hyy : Scalar) : Tensor := fun p => ![hxx p, hxy p, hyy p]

def component (h : Tensor) (i : Fin 3) : Scalar := fun p => h p i

def conjugatedD (τ : ℝ) (G Z : Field n) : Tensor :=
  tensorOf (conjugatedMetric τ G Z dx dx) (conjugatedMetric τ G Z dx dy)
    (conjugatedMetric τ G Z dy dy)

def initialAmplitude (τ : ℝ) (G V : Field n) (h : Tensor) : Field n :=
  firstParametrix τ G V (component h 0) (component h 1) (component h 2)

def zeroParametrix (τ : ℝ) (G : Field n) (h : Tensor) : Field n :=
  initialAmplitude τ G (fun _ => 0) h

def residual (τ : ℝ) (G : Field n) (h : Tensor) (Z : Field n) : Tensor :=
  fun p => conjugatedD τ G Z p - h p



def modeApprox (τ : ℝ) (G V : Field n) (h : Tensor) : ℕ → Field n
  | 0 => initialAmplitude τ G V h
  | j + 1 => fun p => modeApprox τ G V h j p -
      zeroParametrix τ G (residual τ G h (modeApprox τ G V h j)) p

lemma contDiffAt_initialAmplitude (τ : ℝ) {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (initialAmplitude τ G V h) p :=
  contDiffAt_firstParametrix τ hG hV (contDiffAt_pi.mp hh 0) (contDiffAt_pi.mp hh 1)
    (contDiffAt_pi.mp hh 2) hD hb

lemma contDiffAt_zeroParametrix (τ : ℝ) {G : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (zeroParametrix τ G h) p :=
  contDiffAt_initialAmplitude τ hG contDiffAt_const hh hD hb

lemma contDiffAt_conjugatedD (τ : ℝ) {G Z : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hZ : ContDiffAt ℝ ∞ Z p) :
    ContDiffAt ℝ ∞ (conjugatedD τ G Z) p := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_conjugatedMetric τ hG hZ dx dx
  · exact contDiffAt_conjugatedMetric τ hG hZ dx dy
  · exact contDiffAt_conjugatedMetric τ hG hZ dy dy

lemma contDiffAt_residual (τ : ℝ) {G Z : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hZ : ContDiffAt ℝ ∞ Z p) (hh : ContDiffAt ℝ ∞ h p) :
    ContDiffAt ℝ ∞ (residual τ G h Z) p :=
  (contDiffAt_conjugatedD τ hG hZ).sub hh

lemma contDiffAt_modeApprox (τ : ℝ) {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (j : ℕ) :
    ContDiffAt ℝ ∞ (modeApprox τ G V h j) p := by
  induction j with
  | zero => exact contDiffAt_initialAmplitude τ hG hV hh hD hb
  | succ j ih => exact ih.sub (contDiffAt_zeroParametrix τ hG (contDiffAt_residual τ hG ih hh) hD hb)

lemma conjugatedD_sub (τ : ℝ) (G : Field n) {Z W : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) :
    conjugatedD τ G (fun q => Z q - W q) p = conjugatedD τ G Z p - conjugatedD τ G W p := by
  ext i
  fin_cases i <;> simp [conjugatedD, tensorOf, conjugatedMetric_sub τ G hZ hW]


theorem residual_modeApprox_succ (τ : ℝ) {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (j : ℕ) :
    residual τ G h (modeApprox τ G V h (j + 1)) p =
      - residual τ G (residual τ G h (modeApprox τ G V h j))
        (zeroParametrix τ G (residual τ G h (modeApprox τ G V h j))) p := by
  have hZ := contDiffAt_modeApprox τ hG hV hh hD hb j
  have hW := contDiffAt_zeroParametrix τ hG (contDiffAt_residual τ hG hZ hh) hD hb
  simp only [modeApprox, residual,
    conjugatedD_sub τ G (hZ.differentiableAt (by simp)) (hW.differentiableAt (by simp))]
  abel



def errorGenerator (G V : Field n) (h : Tensor) : Tensor :=
  let kx := reducedKx G V (component h 0) (component h 2)
  let ky := reducedKy G V (component h 1) (component h 2)
  tensorOf (fun p => 2 * reducedLx G kx ky p) (reducedLy G kx ky) (fun _ => 0)

lemma contDiffAt_reducedLx {G : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedLx G ux uy) p := by
  exact ((contDiffAt_coordDeriv hx dx).sub (contDiffAt_connectionTerm hG hx hy hD dx dx)).sub
    ((contDiffAt_secondRatio hG hD hb dx dx).mul
      ((contDiffAt_coordDeriv hy dy).sub (contDiffAt_connectionTerm hG hx hy hD dy dy)))

lemma contDiffAt_reducedLy {G : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedLy G ux uy) p := by
  exact (((contDiffAt_coordDeriv hy dx).add (contDiffAt_coordDeriv hx dy)).sub
    (contDiffAt_const.mul (contDiffAt_connectionTerm hG hx hy hD dx dy))).sub
    ((contDiffAt_const.mul (contDiffAt_secondRatio hG hD hb dx dy)).mul
      ((contDiffAt_coordDeriv hy dy).sub (contDiffAt_connectionTerm hG hx hy hD dy dy)))

lemma contDiffAt_errorGenerator {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (errorGenerator G V h) p := by
  have hx := contDiffAt_reducedKx hG hV (contDiffAt_pi.mp hh 0) (contDiffAt_pi.mp hh 2) hD hb
  have hy := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hh 1) (contDiffAt_pi.mp hh 2) hD hb
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_const.mul (contDiffAt_reducedLx hG hx hy hD hb)
  · exact contDiffAt_reducedLy hG hx hy hD hb
  · exact contDiffAt_const



theorem residual_initialAmplitude {τ : ℝ} (hτ : τ ≠ 0) {G V : Field n}
    {h : Tensor} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hVsm : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V p = 0) :
    residual τ G h (initialAmplitude τ G V h) p =
      ((τ : ℂ) / Complex.I) • errorGenerator G V h p := by
  have hs := contDiffAt_initialAmplitude τ hG.contDiffAt hVsm hh hD.self_of_nhds hb
  have hx := contDiffAt_reducedKx hG.contDiffAt hVsm (contDiffAt_pi.mp hh 0)
    (contDiffAt_pi.mp hh 2) hD.self_of_nhds hb
  have hy := contDiffAt_reducedKy hG.contDiffAt hVsm (contDiffAt_pi.mp hh 1)
    (contDiffAt_pi.mp hh 2) hD.self_of_nhds hb
  obtain ⟨hxx, hxy, hyy⟩ := firstParametrix_residual hτ hG
    (hs.differentiableAt (by simp)) hD hX hY hb hV
  have hlx := reducedLx_mul G (hx.differentiableAt (by simp))
    (hy.differentiableAt (by simp)) ((τ : ℂ) / Complex.I)
  have hly := reducedLy_mul G (hx.differentiableAt (by simp))
    (hy.differentiableAt (by simp)) ((τ : ℂ) / Complex.I)
  unfold firstCovectorX firstCovectorY component at hxx hxy
  rw [hlx] at hxx
  rw [hly] at hxy
  unfold component at hyy
  unfold residual conjugatedD initialAmplitude errorGenerator component
  ext i
  fin_cases i
  · simpa [residual, conjugatedD, tensorOf, initialAmplitude, errorGenerator,
      mul_assoc, mul_left_comm] using hxx
  · simpa [residual, conjugatedD, tensorOf, initialAmplitude, errorGenerator] using hxy
  · simp [tensorOf, hyy]

lemma reducedKx_zero_mul (G : Field n) (hxx hyy : Scalar) (a : ℂ) :
    reducedKx G (fun _ => 0) (fun q => a * hxx q) (fun q => a * hyy q) =
      fun q => a * reducedKx G (fun _ => 0) hxx hyy q := by
  funext q
  simp only [reducedKx, dotProduct_zero]
  ring

lemma reducedKy_zero_mul (G : Field n) (hxy hyy : Scalar) (a : ℂ) :
    reducedKy G (fun _ => 0) (fun q => a * hxy q) (fun q => a * hyy q) =
      fun q => a * reducedKy G (fun _ => 0) hxy hyy q := by
  funext q
  simp only [reducedKy, dotProduct_zero]
  ring

lemma errorGenerator_zero_mul (G : Field n) {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (a : ℂ) :
    errorGenerator G (fun _ => 0) (fun q => a • h q) p =
      a • errorGenerator G (fun _ => 0) h p := by
  have hx := contDiffAt_reducedKx (V := fun _ => 0) hG contDiffAt_const (contDiffAt_pi.mp hh 0)
    (contDiffAt_pi.mp hh 2) hD hb
  have hy := contDiffAt_reducedKy (V := fun _ => 0) hG contDiffAt_const (contDiffAt_pi.mp hh 1)
    (contDiffAt_pi.mp hh 2) hD hb
  have hcx (i : Fin 3) : component (fun q => a • h q) i = fun q => a * component h i q := rfl
  simp only [errorGenerator, hcx, reducedKx_zero_mul, reducedKy_zero_mul]
  ext i
  fin_cases i
  · simp [tensorOf]
    unfold component
    rw [reducedLx_mul G (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp)) a]
    ring
  · simp [tensorOf]
    exact reducedLy_mul G (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp)) a
  · simp [tensorOf]

lemma reducedLx_congr (G : Field n) {ux uy vx vy : Scalar} {p : Base}
    (hx : ux =ᶠ[nhds p] vx) (hy : uy =ᶠ[nhds p] vy) :
    reducedLx G ux uy p = reducedLx G vx vy p := by
  simp only [reducedLx, coordDeriv, hx.fderiv_eq, hy.fderiv_eq, connectionTerm,
    hx.self_of_nhds, hy.self_of_nhds]

lemma reducedLy_congr (G : Field n) {ux uy vx vy : Scalar} {p : Base}
    (hx : ux =ᶠ[nhds p] vx) (hy : uy =ᶠ[nhds p] vy) :
    reducedLy G ux uy p = reducedLy G vx vy p := by
  simp only [reducedLy, coordDeriv, hx.fderiv_eq, hy.fderiv_eq, connectionTerm,
    hx.self_of_nhds, hy.self_of_nhds]


lemma errorGenerator_congr (G V : Field n) {h k : Tensor} {p : Base}
    (he : h =ᶠ[nhds p] k) : errorGenerator G V h p = errorGenerator G V k p := by
  have hx : reducedKx G V (component h 0) (component h 2) =ᶠ[nhds p]
      reducedKx G V (component k 0) (component k 2) := by
    filter_upwards [he] with q hq
    simp only [reducedKx, component, hq]
  have hy : reducedKy G V (component h 1) (component h 2) =ᶠ[nhds p]
      reducedKy G V (component k 1) (component k 2) := by
    filter_upwards [he] with q hq
    simp only [reducedKy, component, hq]
  unfold errorGenerator tensorOf
  dsimp only
  rw [reducedLx_congr G hx hy, reducedLy_congr G hx hy]


def errorHierarchy (G V : Field n) (h : Tensor) : ℕ → Tensor
  | 0 => errorGenerator G V h
  | j + 1 => errorGenerator G (fun _ => 0) (errorHierarchy G V h j)

lemma contDiffAt_errorHierarchy {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (j : ℕ) :
    ContDiffAt ℝ ∞ (errorHierarchy G V h j) p := by
  induction j with
  | zero => exact contDiffAt_errorGenerator hG hV hh hD hb
  | succ j ih => exact contDiffAt_errorGenerator hG contDiffAt_const ih hD hb





theorem residual_modeApprox_power {τ : ℝ} (hτ : τ ≠ 0) {G V : Field n}
    {h : Tensor} (hG : ContDiff ℝ ∞ G) {U : Set Base} (hU : IsOpen U)
    (hVsm : ContDiffOn ℝ ∞ V U) (hh : ContDiffOn ℝ ∞ h U)
    (hD : ∀ q ∈ U, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ q ∈ U, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ q ∈ U, coordDeriv dy G q ⬝ᵥ V q = 0)
    (hb : ∀ q ∈ U, goodSecond G q ⬝ᵥ goodSecond G q ≠ 0)
    (hV : ∀ q ∈ U, goodSecond G q ⬝ᵥ V q = 0) (j : ℕ) :
    ∀ p ∈ U, residual τ G h (modeApprox τ G V h j) p =
      ((-((τ : ℂ) / Complex.I)) ^ j * ((τ : ℂ) / Complex.I)) • errorHierarchy G V h j p := by
  have hDe (p : Base) (hp : p ∈ U) : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0 :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hD q hq
  have hXe (p : Base) (hp : p ∈ U) : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0 :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hX q hq
  have hYe (p : Base) (hp : p ∈ U) : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0 :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hY q hq
  have hvAt (p : Base) (hp : p ∈ U) : ContDiffAt ℝ ∞ V p := (hVsm p hp).contDiffAt (hU.mem_nhds hp)
  have hhAt (p : Base) (hp : p ∈ U) : ContDiffAt ℝ ∞ h p := (hh p hp).contDiffAt (hU.mem_nhds hp)
  induction j with
  | zero =>
    intro p hp
    simpa only [modeApprox, errorHierarchy, pow_zero, one_mul] using
      residual_initialAmplitude hτ hG (hvAt p hp) (hhAt p hp) (hDe p hp)
        (hXe p hp) (hYe p hp) (hb p hp) (hV p hp)
  | succ j ih =>
    intro p hp
    let a : ℂ := (-((τ : ℂ) / Complex.I)) ^ j * ((τ : ℂ) / Complex.I)
    have hre : residual τ G h (modeApprox τ G V h j) =ᶠ[nhds p]
        fun q => a • errorHierarchy G V h j q := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact ih q hq
    have hs := contDiffAt_modeApprox τ hG.contDiffAt (hvAt p hp) (hhAt p hp) (hD p hp) (hb p hp) j
    have hr := contDiffAt_residual τ hG.contDiffAt hs (hhAt p hp)
    have hzeroX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ (0 : Ambient n) = 0 :=
      Filter.Eventually.of_forall fun q => dotProduct_zero _
    have hzeroY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ (0 : Ambient n) = 0 :=
      Filter.Eventually.of_forall fun q => dotProduct_zero _
    rw [residual_modeApprox_succ τ hG.contDiffAt (hvAt p hp) (hhAt p hp) (hD p hp) (hb p hp)]
    rw [show zeroParametrix τ G (residual τ G h (modeApprox τ G V h j)) =
      initialAmplitude τ G (fun _ => 0) (residual τ G h (modeApprox τ G V h j)) from rfl]
    rw [residual_initialAmplitude hτ hG contDiffAt_const hr (hDe p hp)
      hzeroX hzeroY (hb p hp) (dotProduct_zero _)]
    rw [errorGenerator_congr G (fun _ => 0) hre]
    rw [errorGenerator_zero_mul G hG.contDiffAt
      (contDiffAt_errorHierarchy hG.contDiffAt (hvAt p hp) (hhAt p hp) (hD p hp) (hb p hp) j)
      (hD p hp) (hb p hp) a]
    simp only [smul_smul, ← neg_smul, errorHierarchy]
    congr 1
    dsimp [a]
    ring


def freeCorrection (G V : Field n) : Field n :=
  let kx := reducedKx G V (fun _ => 0) (fun _ => 0)
  let ky := reducedKy G V (fun _ => 0) (fun _ => 0)
  fun p => tangentLift (coordDeriv dx G p) (coordDeriv dy G p) (kx p) (ky p) +
    ((coordDeriv dy ky p - connectionTerm G kx ky dy dy p) /
      (goodSecond G p ⬝ᵥ goodSecond G p)) • goodSecond G p

lemma initialAmplitude_free (τ : ℝ) {G V : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G V (fun _ => 0) p =
      V p + ((τ : ℂ) / Complex.I) • freeCorrection G V p := by
  have hy : ContDiffAt ℝ ∞ (reducedKy G V (fun _ => 0) (fun _ => 0)) p :=
    contDiffAt_reducedKy hG hV contDiffAt_const contDiffAt_const hD hb
  unfold initialAmplitude firstParametrix firstCovectorX firstCovectorY
    reconstruct normalElimination freeCorrection component
  dsimp only [Pi.zero_apply]
  rw [partial_const_mul (hy.differentiableAt (by simp)), connectionTerm_mul, tangentLift_mul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma initialAmplitude_congr (τ : ℝ) (G : Field n) {V W : Field n} {h k : Tensor} {p : Base}
    (hv : V =ᶠ[nhds p] W) (hh : h =ᶠ[nhds p] k) :
    initialAmplitude τ G V h p = initialAmplitude τ G W k p := by
  have hx : firstCovectorX τ G V (component h 0) (component h 2) =ᶠ[nhds p]
      firstCovectorX τ G W (component k 0) (component k 2) := by
    filter_upwards [hv, hh] with q hvq hhq
    simp only [firstCovectorX, reducedKx, component, hvq, hhq]
  have hy : firstCovectorY τ G V (component h 1) (component h 2) =ᶠ[nhds p]
      firstCovectorY τ G W (component k 1) (component k 2) := by
    filter_upwards [hv, hh] with q hvq hhq
    simp only [firstCovectorY, reducedKy, component, hvq, hhq]
  unfold initialAmplitude firstParametrix reconstruct normalElimination
  simp only [coordDeriv, hx.self_of_nhds, hy.self_of_nhds, hy.fderiv_eq,
    connectionTerm, hv.self_of_nhds, component, hh.self_of_nhds]

lemma initialAmplitude_zero (τ : ℝ) (G : Field n) :
    initialAmplitude τ G (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  unfold initialAmplitude firstParametrix reconstruct normalElimination
    firstCovectorX firstCovectorY reducedKx reducedKy connectionTerm
    tangentLift liftX liftY component coordDeriv
  simp

lemma conjugatedD_congr (τ : ℝ) (G : Field n) {Z W : Field n} {p : Base}
    (he : Z =ᶠ[nhds p] W) : conjugatedD τ G Z p = conjugatedD τ G W p := by
  unfold conjugatedD tensorOf conjugatedMetric linearizedMetric covector
  simp only [coordDeriv, he.fderiv_eq, he.self_of_nhds]

lemma conjugatedD_zero (τ : ℝ) (G : Field n) :
    conjugatedD τ G (fun _ => 0) = fun _ => 0 := by
  unfold conjugatedD tensorOf conjugatedMetric linearizedMetric covector coordDeriv
  simp
  ext p i
  fin_cases i <;> simp




theorem modeApprox_vanishes (τ : ℝ) (G V : Field n) (h : Tensor)
    {U : Set Base} (hU : IsOpen U) (hV : ∀ p ∈ U, V p = 0) (hh : ∀ p ∈ U, h p = 0)
    (j : ℕ) : ∀ p ∈ U, modeApprox τ G V h j p = 0 := by
  have hVe (p : Base) (hp : p ∈ U) : V =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hV q hq
  have hhe (p : Base) (hp : p ∈ U) : h =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hh q hq
  induction j with
  | zero =>
    intro p hp
    change initialAmplitude τ G V h p = 0
    rw [initialAmplitude_congr τ G (hVe p hp) (hhe p hp), initialAmplitude_zero]
  | succ j ih =>
    have hr : ∀ p ∈ U, residual τ G h (modeApprox τ G V h j) p = 0 := by
      intro p hp
      have he : modeApprox τ G V h j =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih q hq
      rw [residual, conjugatedD_congr τ G he, conjugatedD_zero, hh p hp, sub_self]
    intro p hp
    have hre : residual τ G h (modeApprox τ G V h j) =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hr q hq
    change modeApprox τ G V h j p - zeroParametrix τ G (residual τ G h (modeApprox τ G V h j)) p = 0
    rw [ih p hp, zeroParametrix,
      initialAmplitude_congr τ G (Filter.Eventually.of_forall fun _ => rfl) hre, initialAmplitude_zero, sub_self]

end LinearStructure

end ClosedSurfaceR4.SmallModes

end

end OAI
