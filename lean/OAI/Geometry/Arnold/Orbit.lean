import OAI.Geometry.Arnold.Differentiation

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample

namespace CriticalBound
open Matrix

/-- Complexification of a real matrix, with the actual complex-linear action. -/
def complexMat (A : RM) : Matrix (Fin 5) (Fin 5) ℂ := A.map Complex.ofReal

def act (A : RM) (z : CV) : CV := (complexMat A).mulVec z

lemma complexMat_mul (A B : RM) : complexMat (A * B) = complexMat A * complexMat B := by
  ext i j
  simp [complexMat, Matrix.mul_apply]

lemma complexMat_star (A : RM) : complexMat (star A) = star (complexMat A) := by
  ext i j
  simp [complexMat, Matrix.star_apply]

lemma complexMat_one : complexMat 1 = 1 := by
  ext i j
  simp [complexMat, Matrix.one_apply, apply_ite Complex.ofReal]

lemma act_mul (A B : RM) (z : CV) : act (A * B) z = act A (act B z) := by
  simp [act, complexMat_mul, Matrix.mulVec_mulVec]

lemma act_smul (A : RM) (a : ℂ) (z : CV) : act A (a • z) = a • act A z := by
  exact Matrix.mulVec_smul _ _ _

lemma act_sub_left (A B : RM) (z : CV) : act (A - B) z = act A z - act B z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul]

lemma act_preserves_hermitian (A : O5) (z w : CV) :
    star (act A z) ⬝ᵥ act A w = star z ⬝ᵥ w := by
  have hA : star (complexMat A) * complexMat A = 1 := by
    rw [← complexMat_star, ← complexMat_mul, A.property.1, complexMat_one]
  calc
    star (act A z) ⬝ᵥ act A w = (star z ᵥ* star (complexMat A)) ⬝ᵥ (complexMat A *ᵥ w) := by
      simp only [act, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    _ = star z ⬝ᵥ (star (complexMat A) *ᵥ (complexMat A *ᵥ w)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = star z ⬝ᵥ w := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

lemma omega_act (A : O5) (v w : CV) : omega (act A v) (act A w) = omega v w := by
  unfold omega
  exact congrArg (fun a : ℂ ↦ 2 * a.im) (act_preserves_hermitian A v w)

/-- Elementary skew matrix rotating the `(a,b)` coordinate plane. -/
def rotGen (a b : Fin 5) : RM := Matrix.single b a 1 - Matrix.single a b 1

lemma rotGen_skew (a b : Fin 5) : star (rotGen a b) = -rotGen a b := by
  ext i j
  simp [rotGen, Matrix.star_apply, Matrix.single_apply, sub_eq_add_neg, and_comm]

lemma rotGen_act (a b : Fin 5) (z : CV) :
    act (rotGen a b) z = Pi.single b (z a) - Pi.single a (z b) := by
  change (complexMat (Matrix.single b a 1 - Matrix.single a b 1)).mulVec z = _
  have h : complexMat (Matrix.single b a 1 - Matrix.single a b 1) =
      Matrix.single b a (1 : ℂ) - Matrix.single a b 1 := by
    ext i j
    simp [complexMat, Matrix.single_apply, apply_ite Complex.ofReal]
  rw [h, Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec]
  ext i
  simp [Function.update_apply, Pi.single_apply, eq_comm]

end CriticalBound
end ArnoldCounterexample

namespace ArnoldCounterexample.CriticalBound

noncomputable def baseScale : ℝ := Real.sqrt (1 / 2)

lemma baseScale_sq : baseScale ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

lemma baseScale_pos : 0 < baseScale := Real.sqrt_pos.2 (by norm_num)

def base : CV := ![(baseScale : ℂ), baseScale * Complex.I, 0, 0, 0]

lemma base_unit : IsUnitQuadric base := by
  constructor
  · simp [normSquared, base, Fin.sum_univ_succ, Complex.normSq_mul,
      Complex.normSq_ofReal, ← sq, baseScale_sq]
    norm_num
  · simp [quadricPolynomial, base, Fin.sum_univ_succ, mul_pow, Complex.I_sq]

def generators : Fin 6 → RM :=
  ![rotGen 0 2, rotGen 1 2, rotGen 0 3, rotGen 1 3, rotGen 0 4, rotGen 1 4]

def velocities : Fin 6 → CV :=
  ![Pi.single 2 (baseScale : ℂ), Pi.single 2 (baseScale * Complex.I),
    Pi.single 3 (baseScale : ℂ), Pi.single 3 (baseScale * Complex.I),
    Pi.single 4 (baseScale : ℂ), Pi.single 4 (baseScale * Complex.I)]

lemma generators_skew (i : Fin 6) : star (generators i) = -generators i := by
  fin_cases i <;> exact rotGen_skew _ _

lemma generators_base (i : Fin 6) : act (generators i) base = velocities i := by
  fin_cases i <;> simp [generators, velocities, rotGen_act, base]

def bracketCoefficient : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0]

lemma generators_bracket_base (i j : Fin 6) :
    act (generators i * generators j - generators j * generators i) base =
      (bracketCoefficient i j : ℂ) • (Complex.I • base) := by
  rw [act_sub_left, act_mul, act_mul, generators_base, generators_base]
  fin_cases i <;> fin_cases j <;>
    ext k <;> fin_cases k <;>
    simp [generators, velocities, rotGen_act, bracketCoefficient, base,
      ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

lemma act_add_left (A B : RM) (z : CV) : act (A + B) z = act A z + act B z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

lemma act_real_smul_left (c : ℝ) (A : RM) (z : CV) :
    act (c • A) z = c • act A z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
    Complex.real_smul]

local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The orbit map at the literal unit isotropic vector, extended linearly. -/
def orbitProjection : RM →L[ℝ] CV :=
  ({ toFun := fun A ↦ act A base
     map_add' := fun A B ↦ act_add_left A B base
     map_smul' := fun c A ↦ act_real_smul_left c A base } : RM →ₗ[ℝ] CV).toContinuousLinearMap

@[simp] lemma orbitProjection_apply (A : RM) : orbitProjection A = act A base := rfl

lemma act_star (A : RM) (z : CV) : act A (star z) = star (act A z) := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct]

lemma act_preserves_bilinear (A : O5) (z w : CV) :
    act A z ⬝ᵥ act A w = z ⬝ᵥ w := by
  simpa only [act_star, star_star] using act_preserves_hermitian A (star z) w

lemma act_preserves_quadricPolynomial (A : O5) (z : CV) :
    quadricPolynomial (act A z) = quadricPolynomial z := by
  simpa only [quadricPolynomial, dotProduct, pow_two] using act_preserves_bilinear A z z

lemma normSquared_eq_re (z : CV) : normSquared z = (star z ⬝ᵥ z).re := by
  simp [normSquared, dotProduct, Complex.normSq, Complex.mul_re]

lemma act_preserves_normSquared (A : O5) (z : CV) :
    normSquared (act A z) = normSquared z := by
  rw [normSquared_eq_re, normSquared_eq_re, act_preserves_hermitian]

lemma act_unit (A : O5) (z : UnitQuadric) : IsUnitQuadric (act A z) := by
  exact ⟨(act_preserves_normSquared A z).trans z.property.1,
    (act_preserves_quadricPolynomial A z).trans z.property.2⟩

lemma orbitProjection_unit (A : O5) : IsUnitQuadric (orbitProjection A) :=
  act_unit A ⟨base, base_unit⟩

/-- A basic form annihilates the genuine circle-fiber direction. -/
def IsBasic {n : ℕ} (η : CV → CV [⋀^Fin (n + 1)]→L[ℝ] ℝ) : Prop :=
  ∀ z : UnitQuadric, ∀ a : ℝ, ∀ v : Fin n → CV,
    η z (Matrix.vecCons ((a : ℂ) • (Complex.I • (z : CV))) v) = 0

/-- Stokes evaluation for basic 5-forms on Q^3, proved by Haar integration
rather than assuming a manifold integration or cohomology theorem. -/
theorem integral_extDeriv_basic_eq_zero
    (η : CV → CV [⋀^Fin 5]→L[ℝ] ℝ) (hη : ContDiff ℝ ∞ η) (hbasic : IsBasic η) :
    ∫ A : O5, extDeriv η (orbitProjection A) (fun i ↦ act A (velocities i)) ∂haar = 0 := by
  let W : RM → MatForm 5 := fun A ↦ (η (orbitProjection A)).compContinuousLinearMap orbitProjection
  have hW : ContDiff ℝ ∞ W := by
    let : TopologicalSpace RM :=
      (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let P : (CV [⋀^Fin 5]→L[ℝ] ℝ) →L[ℝ] MatForm 5 :=
      (ContinuousAlternatingMap.compContinuousLinearMapₗ (ι := Fin 5) (N := ℝ)
        orbitProjection).mkContinuous (‖orbitProjection‖ ^ 5) (by
          intro θ
          simpa only [ContinuousAlternatingMap.compContinuousLinearMapₗ,
            LinearMap.coe_mk, AddHom.coe_mk, Fintype.card_fin, mul_comm] using
            θ.norm_compContinuousLinearMap_le orbitProjection)
    exact P.contDiff.comp (hη.comp orbitProjection.contDiff)
  have hv (A : O5) (i j : Fin 5) :
      W A (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
        generators j.succ * generators i.castSucc))
        (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0 := by
    change η (orbitProjection A) (orbitProjection ∘ _) = 0
    simp only [Matrix.vecCons, Fin.comp_cons]
    simp only [orbitProjection_apply, act_mul, generators_bracket_base, act_smul]
    exact hbasic ⟨orbitProjection A, orbitProjection_unit A⟩ _ _
  have hz := integral_extDeriv_rightMul_eq_zero W hW generators generators_skew hv
  convert! hz using 1
  congr 1
  funext A
  have hp := extDeriv_pullback (hη.differentiable (by simp) (orbitProjection A))
    (orbitProjection.contDiff.contDiffAt : ContDiffAt ℝ 2 orbitProjection (A : RM)) (by simp)
  simp only [ContinuousLinearMap.fderiv] at hp
  have heval := congrArg (fun f : MatForm 6 ↦ f (fun i ↦ (A : RM) * generators i)) hp
  simpa only [W, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, orbitProjection_apply, act_mul, generators_base] using heval.symm

end ArnoldCounterexample.CriticalBound

end

end OAI
