import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapDoubleRay

namespace OAI

/-! Explicit invertible linear coordinates adapted to the kernel of a crosscap. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crosscapSourceLinear (b : Bool) (t : ℝ) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj (0 : Fin 2)).smulRight (tangentRayVelocity b) +
    (ContinuousLinearMap.proj (1 : Fin 2)).smulRight (tangentRay b t)

lemma crosscapSourceLinear_apply (b : Bool) (t : ℝ) (x : Base) :
    crosscapSourceLinear b t x = x 0 • tangentRayVelocity b + x 1 • tangentRay b t := rfl

lemma crosscapSourceLinear_coordinates (b : Bool) (t : ℝ) (x : Base) :
    tangentTransverseCoefficient b t (crosscapSourceLinear b t x) = x 0 ∧
      tangentRayCoefficient b (crosscapSourceLinear b t x) = x 1 := by
  cases b <;> simp [crosscapSourceLinear_apply,tangentTransverseCoefficient,
    tangentRayCoefficient,tangentRayVelocity,tangentRay] <;> ring

lemma crosscapSourceLinear_bijective (b : Bool) (t : ℝ) :
    Function.Bijective (crosscapSourceLinear b t) := by
  constructor
  · intro x y h
    have h0 := congrArg (tangentTransverseCoefficient b t) h
    have h1 := congrArg (tangentRayCoefficient b) h
    rw [(crosscapSourceLinear_coordinates b t x).1,
      (crosscapSourceLinear_coordinates b t y).1] at h0
    rw [(crosscapSourceLinear_coordinates b t x).2,
      (crosscapSourceLinear_coordinates b t y).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  · intro x
    refine ⟨![tangentTransverseCoefficient b t x,tangentRayCoefficient b x],?_⟩
    simpa only [crosscapSourceLinear_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using
      (tangentRay_decomposition b t x).symm

def crosscapSourceEquiv (b : Bool) (t : ℝ) : Base ≃L[ℝ] Base :=
  ContinuousLinearEquiv.ofBijective (crosscapSourceLinear b t)
    (LinearMap.ker_eq_bot.mpr (crosscapSourceLinear_bijective b t).1)
    (LinearMap.range_eq_top.mpr (crosscapSourceLinear_bijective b t).2)

/-- Reorder the linearized direction variables into the standard crosscap target coordinates. -/
def crosscapParameterLinear (b : Bool) (t : ℝ) :
    (Base × ℝ) →L[ℝ] (Base × ℝ) :=
  (((ContinuousLinearMap.proj (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ Base ℝ)).smulRight
      (tangentRayVelocity b) +
    ((1/2 : ℝ) • ((ContinuousLinearMap.proj (1 : Fin 2)).comp
      (ContinuousLinearMap.fst ℝ Base ℝ))).smulRight (tangentRay b t)).prod
    (ContinuousLinearMap.snd ℝ Base ℝ)

lemma crosscapParameterLinear_apply (b : Bool) (t : ℝ) (z : Base × ℝ) :
    crosscapParameterLinear b t z =
      (z.1 0 • tangentRayVelocity b + (z.1 1/2) • tangentRay b t,z.2) := by
  change (z.1 0 • tangentRayVelocity b + ((1/2 : ℝ)*z.1 1) • tangentRay b t,z.2) = _
  congr 2
  congr 1
  ring

lemma crosscapParameterLinear_bijective (b : Bool) (t : ℝ) :
    Function.Bijective (crosscapParameterLinear b t) := by
  have hcoord (z : Base × ℝ) :
      tangentTransverseCoefficient b t (crosscapParameterLinear b t z).1 = z.1 0 ∧
      tangentRayCoefficient b (crosscapParameterLinear b t z).1 = z.1 1/2 := by
    have h := crosscapSourceLinear_coordinates b t (![z.1 0,z.1 1/2] : Base)
    simpa only [crosscapParameterLinear_apply,crosscapSourceLinear_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one] using h
  constructor
  · intro z w h
    have he := congrArg Prod.fst h
    have h0 := congrArg (tangentTransverseCoefficient b t) he
    have h1 := congrArg (tangentRayCoefficient b) he
    rw [(hcoord z).1,(hcoord w).1] at h0
    rw [(hcoord z).2,(hcoord w).2] at h1
    apply Prod.ext
    · ext i
      fin_cases i
      · exact h0
      · change z.1 1 = w.1 1
        linarith
    · simpa only [crosscapParameterLinear_apply] using congrArg Prod.snd h
  · intro z
    refine ⟨(![tangentTransverseCoefficient b t z.1,2*tangentRayCoefficient b z.1],z.2),?_⟩
    rw [crosscapParameterLinear_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
    apply Prod.ext
    · convert (tangentRay_decomposition b t z.1).symm using 1
    · rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
