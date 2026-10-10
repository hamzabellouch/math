import OAI.Geometry.SurfaceImmersion.Primitive.JetVelocityLoop
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetChainRule

namespace OAI

/-! Translate the geometric surface jets to the coordinates used by the
quantitative finite-polynomial construction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceJetCoordinates
open RealModes SmallModes WeightedEstimates

def baseEquiv : JetPolynomial.Base ≃L[ℝ] Base :=
  (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv

@[simp] lemma baseEquiv_apply (p : JetPolynomial.Base) : baseEquiv p = (p 0, p 1) := rfl

@[simp] lemma baseEquiv_zero : baseEquiv (JetPolynomial.coordinateVector 0) = dx := by
  simp [baseEquiv_apply, JetPolynomial.coordinateVector, dx]

@[simp] lemma baseEquiv_one : baseEquiv (JetPolynomial.coordinateVector 1) = dy := by
  simp [baseEquiv_apply, JetPolynomial.coordinateVector, dy]

def decode (J : JetPolynomial.LowJet) : CollarVelocity.JetBase :=
  ((J (.inl 0), J (.inl 1)), fun i a =>
    J (.inr (![1, 2, 3, 4, 6] i, a)))

lemma decode_smooth : ContDiff ℝ ∞ decode := by
  apply ContDiff.prodMk
  · exact (ContinuousLinearMap.proj (.inl 0) : JetPolynomial.LowJet →L[ℝ] ℝ).contDiff.prodMk
      (ContinuousLinearMap.proj (.inl 1) : JetPolynomial.LowJet →L[ℝ] ℝ).contDiff
  · apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro a
    exact (ContinuousLinearMap.proj (.inr (![1, 2, 3, 4, 6] i, a)) :
      JetPolynomial.LowJet →L[ℝ] ℝ).contDiff

lemma directional_chart (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (w : List (Fin 2)) :
    iteratedDirectional (w.map JetPolynomial.coordinateVector) (f ∘ baseEquiv) =
      (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) ∘ baseEquiv := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞
        (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn _)
    rw [fderiv_comp p (hs.differentiable (by simp) _) baseEquiv.differentiableAt,
      baseEquiv.fderiv, ContinuousLinearMap.comp_apply]
    rfl

lemma directional_component {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (w : List Base) (a : Fin 4) :
    iteratedDirectional w (fun p => F p a) = fun p => iteratedDirectional w F p a := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞ (iteratedDirectional w F) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hF.contDiffOn w)
    rw [fderiv_apply (hs.differentiable (by simp) p) a]
    rfl

theorem decode_lowJet {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : JetPolynomial.Base) :
    decode (JetPolynomial.lowJet (F ∘ baseEquiv) p) = CollarVelocity.jetSection F (baseEquiv p) := by
  apply Prod.ext
  · rfl
  · funext i a
    change JetPolynomial.jet (F ∘ baseEquiv) (JetPolynomial.lowWord (![1, 2, 3, 4, 6] i)) a p =
      realTwoJet F (baseEquiv p) i a
    have he (w : List (Fin 2)) : JetPolynomial.jet (F ∘ baseEquiv) w a p =
        iteratedDirectional (w.map (fun j => baseEquiv (JetPolynomial.coordinateVector j))) F (baseEquiv p) a := by
      change iteratedDirectional (w.map JetPolynomial.coordinateVector)
        ((fun q => F q a) ∘ baseEquiv) p = _
      rw [directional_chart _ (contDiff_pi.mp hF a) w, Function.comp_apply, directional_component hF]
    rw [he]
    fin_cases i <;> simp [JetPolynomial.lowWord, realTwoJet, iteratedDirectional, coordDeriv,
      JetPolynomial.coordinateVector, dx, dy] <;> rfl

end ClosedSurfaceR4.SurfaceJetCoordinates

end

end OAI
