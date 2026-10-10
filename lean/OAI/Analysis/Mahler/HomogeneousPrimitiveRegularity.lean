import OAI.Analysis.Mahler.PrimitiveRegularity
import OAI.Analysis.Mahler.SphereFlux

namespace OAI

open Complex ContinuousAlternatingMap Set

noncomputable section
namespace Mahler

/-- Evaluation at a fixed tuple preserves finite-order regularity. -/
lemma contDiffAt_form_eval {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {x : X} (q : ℕ)
    (ha : ContDiffAt ℝ q a x) (v : ι → E) :
    ContDiffAt ℝ q (fun y => a y v) x := by
  let ev : (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    { toFun := fun A => A v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_eval_const v }
  exact ev.contDiff.contDiffAt.comp x ha

lemma contDiffAt_extDeriv_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {a : E → E [⋀^Fin p]→L[ℝ] ℂ} {x : E} (q : ℕ)
    (ha : ContDiffAt ℝ (q+1) a x) :
    ContDiffAt ℝ q (extDeriv a) x := by
  have hd : ContDiffAt ℝ q (fderiv ℝ a) x := ha.fderiv_right (by norm_cast)
  exact (alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x hd

/-- The order alpha, beta, followed by k ordered d-alpha factors. -/
def sourcePrimitiveSlots (k : ℕ) :
    (Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k)) ≃ Fin (2*(k+1)) :=
  (sphereFrameSlots k).trans (powerFinEquiv (k+1))

def sourcePrimitiveFin {k : ℕ}
    (a b : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+2)) :
    ComplexEuclidean (k+2) [⋀^Fin (2*(k+1))]→ₗ[ℝ] ℂ :=
  (wedge (oneForm a x).toAlternatingMap
    (wedge (oneForm b x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k))).domDomCongr
        (sourcePrimitiveSlots k)

/-- The literal homogeneous primitive, continuously bundled by exact finite
basis expansion. No exterior differentiation identity is assumed here. -/
def sourceHomogeneousPrimitive {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ)
    (x : ComplexEuclidean (k+2)) :
    ComplexEuclidean (k+2) [⋀^Fin (2*(k+1))]→L[ℝ] ℂ :=
  bundleFiniteForm (sphereFrame (k+1)).toBasis
    (sourcePrimitiveFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x)

theorem sourceHomogeneousPrimitive_eq {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ)
    (x : ComplexEuclidean (k+2)) :
    (sourceHomogeneousPrimitive (m := m) G t x).toAlternatingMap =
      sourcePrimitiveFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x :=
  bundleFiniteForm_eq _ _

theorem MassHypotheses.sourceHomogeneousPrimitive_contDiffAt {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (sourceHomogeneousPrimitive (m := m) G t) x := by
  apply contDiffAt_bundleFiniteForm
  intro v
  have hs := h.alpha_beta_contDiffAt hx t q
  have hs1 := h.alpha_beta_contDiffAt hx t (q+1)
  apply contDiffAt_wedge_eval q
  · intro w
    exact contDiffAt_form_eval q (contDiffAt_oneForm_order q hs.1) w
  · apply contDiffAt_wedge_eval q
    · intro w
      exact contDiffAt_form_eval q (contDiffAt_oneForm_order q hs.2) w
    · apply contDiffAt_wedgePower_eval q
      intro w
      exact contDiffAt_form_eval q (contDiffAt_extDeriv_order q
        (contDiffAt_oneForm_order (q+1) hs1.1)) w

theorem MassHypotheses.sourceHomogeneousPrimitive_C2 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ) : ContDiffOn ℝ 2 (sourceHomogeneousPrimitive (m := m) G t) ({0}ᶜ) := by
  intro x hx
  exact (h.sourceHomogeneousPrimitive_contDiffAt (by simpa using hx) t 2).contDiffWithinAt

end Mahler

end

end OAI
