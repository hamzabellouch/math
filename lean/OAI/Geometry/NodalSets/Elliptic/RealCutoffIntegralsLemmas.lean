import OAI.Geometry.NodalSets.Elliptic.RealDerivativeErrorBounds

namespace OAI

noncomputable section

namespace Yau.Geometry

open MeasureTheory
open scoped ContDiff

def realCutoffWeight (eta : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  eta x^2+realGradientSquare eta x

lemma realCutoffWeight_nonneg (eta : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ realCutoffWeight eta x := add_nonneg (sq_nonneg _) (realGradientSquare_nonneg eta x)

lemma realCutoffWeight_smooth (eta : Yau.Jets.Coord → ℝ) (h : ContDiff ℝ ∞ eta) :
    ContDiff ℝ ∞ (realCutoffWeight eta) := (h.pow 2).add (realGradientSquare_smooth eta h)

lemma realCutoffWeight_compact (eta : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport eta) :
    HasCompactSupport (realCutoffWeight eta) := by
  have hsq : HasCompactSupport (fun x ↦ eta x^2) := by
    convert hc.mul_right (f' := eta) using 1
    first | rfl | (ext x; simp [pow_two])
  exact hsq.add (realGradientSquare_compact eta hc)

lemma realCutoffWeight_zero_off_support (eta : Yau.Jets.Coord → ℝ)
    {x : Yau.Jets.Coord} (hx : x ∉ tsupport eta) : realCutoffWeight eta x=0 := by
  have hz : eta x=0 := image_eq_zero_of_notMem_tsupport hx
  have hd := realCoordGradient_zero_off_support eta hx
  have hi (i : Fin 4) : Yau.coordPartial eta x i=0 := congrFun hd i
  simp [realCutoffWeight,realGradientSquare,hz,hi]

lemma realCutoffWeight_integrable_mul (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H) :
    Integrable (fun x ↦ realCutoffWeight eta x*H x) :=
  ((realCutoffWeight_smooth eta heta).continuous.mul hH).integrable_of_hasCompactSupport
    (realCutoffWeight_compact eta hc).mul_right

lemma real_cutoff_first_jet_majorants (eta W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    eta x^2*W x^2 ≤ realCutoffWeight eta x*(W x^2+realGradientSquare W x) ∧
    eta x^2*realGradientSquare W x ≤ realCutoffWeight eta x*(W x^2+realGradientSquare W x) ∧
    realCutoffWeight eta x*realGradientSquare W x ≤ realCutoffWeight eta x*(W x^2+realGradientSquare W x) := by
  have he := realGradientSquare_nonneg eta x
  have hw := realGradientSquare_nonneg W x
  dsimp [realCutoffWeight]
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (eta x)) hw,mul_nonneg he (sq_nonneg (W x)),mul_nonneg he hw]
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (eta x)) (sq_nonneg (W x)),mul_nonneg he (sq_nonneg (W x)),mul_nonneg he hw]
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (add_nonneg (sq_nonneg _) he)

lemma real_coordDiv_sub (F G : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (hG : ∀ i, ContDiff ℝ ∞ (fun x ↦ G x i))
    (x : Yau.Jets.Coord) :
    Yau.coordDiv (fun y i ↦ F y i-G y i) x=Yau.coordDiv F x-Yau.coordDiv G x := by
  simp only [sub_eq_add_neg,real_coordDiv_add _ _ hF (fun i ↦ (hG i).neg),real_coordDiv_neg _ hG]

theorem real_inhomogeneous_differentiation
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W f : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i))
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x)
    (k : Fin 4) :
    ∀ x, Yau.coordDiv (realMatrixFlux C (fun y ↦ Yau.coordPartial W y k)) x+
      V x*Yau.coordPartial W x k =
      Yau.coordDiv (fun y i ↦ Yau.coordPartial (fun z ↦ F z i) y k-realDerivativeErrorFlux C W k y i) x+
        (Yau.coordPartial f x k-Yau.coordPartial V x k*W x) := by
  have hflux := realMatrixFlux_smooth C W hC hW
  have hdiv : ContDiff ℝ ∞ (Yau.coordDiv (realMatrixFlux C W)) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hflux i) i)
  have hdivF : ContDiff ℝ ∞ (Yau.coordDiv F) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hF i) i)
  intro x
  have hd := congrArg (fun H : Yau.Jets.Coord → ℝ ↦ Yau.coordPartial H x k) (funext he)
  rw [Yau.real_coordPartial_add _ _ hdiv (hV.mul hW),Yau.real_coordPartial_mul _ _ hV hW,
    Yau.real_coordPartial_add _ _ hdivF hf,real_coordDiv_partial _ hflux,real_coordDiv_partial _ hF] at hd
  have hpart : (fun y i ↦ Yau.coordPartial (fun z ↦ realMatrixFlux C W z i) y k) =
      fun y i ↦ realDerivativeErrorFlux C W k y i+realMatrixFlux C (fun z ↦ Yau.coordPartial W z k) y i := by
    funext y i; exact realMatrixFlux_partial C W hC hW y i k
  rw [hpart,real_coordDiv_add _ _ (realDerivativeErrorFlux_smooth C W k hC hW)
    (realMatrixFlux_smooth C _ hC (Yau.real_coordPartial_smooth W hW k))] at hd
  rw [real_coordDiv_sub _ _ (fun i ↦ Yau.real_coordPartial_smooth _ (hF i) k)
    (realDerivativeErrorFlux_smooth C W k hC hW)]
  linarith only [hd]

end Yau.Geometry

end

end OAI
