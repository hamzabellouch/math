import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFamilies

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

def fastValue (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) (p : A) : E :=
  U.val p ((ℓ p / z : ℝ) : Period)

lemma fastValue_smooth (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiffOn ℝ ∞ (U.fastValue ℓ z) O :=
  U.smooth.comp (contDiffOn_id.prodMk (ℓ.contDiff.div_const z).contDiffOn)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

lemma fastValue_fderiv (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ)
    {p : A} (hp : p ∈ O) (v : A) :
    fderiv ℝ (U.fastValue ℓ z) p v =
      (U.slow v).val p ((ℓ p / z : ℝ) : Period) +
        (ℓ v / z) • U.angle.val p ((ℓ p / z : ℝ) : Period) := by
  let T : A →L[ℝ] A × ℝ := (ContinuousLinearMap.id ℝ A).prod (z⁻¹ • ℓ)
  have hT (p : A) : T p = (p, ℓ p / z) := by simp [T, div_eq_mul_inv, mul_comm]
  have hEq : U.fastValue ℓ z =
      (fun w : A × ℝ => U.val w.1 (w.2 : Period)) ∘ T := by
    funext p
    simp only [Function.comp_apply, hT, fastValue]
  have hd : DifferentiableAt ℝ (fun w : A × ℝ => U.val w.1 (w.2 : Period)) (T p) := by
    rw [hT]
    exact (U.smooth.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds
      ⟨hp, Set.mem_univ _⟩)).differentiableAt (by simp)
  rw [hEq, fderiv_comp p hd T.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, hT]
  change fderiv ℝ (fun w : A × ℝ => U.val w.1 (w.2 : Period)) (p, ℓ p / z) (v, ℓ v / z) = _
  have hv : (v, ℓ v / z) = (v, 0) + (ℓ v / z) • ((0 : A), (1 : ℝ)) := by simp
  rw [hv, map_add, map_smul, slow_apply _ _ hp, angle_apply _ hp]
  rfl

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
