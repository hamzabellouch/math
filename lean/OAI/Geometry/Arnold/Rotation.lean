import OAI.Geometry.Arnold.Projective

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

/-- Two simultaneous identical planar rotations. -/
def rotation (c s : ℝ) (z : CV) : CV :=
  ![z 0, (c : ℂ) * z 1 - (s : ℂ) * z 2, (s : ℂ) * z 1 + (c : ℂ) * z 2,
    (c : ℂ) * z 3 - (s : ℂ) * z 4, (s : ℂ) * z 3 + (c : ℂ) * z 4]

lemma rotation_quadricPolynomial (c s : ℝ) (z : CV) (hcs : c ^ 2 + s ^ 2 = 1) :
    quadricPolynomial (rotation c s z) = quadricPolynomial z := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  simp [quadricPolynomial, rotation, Fin.sum_univ_succ]
  linear_combination (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2) * hc

lemma rotation_normSquared (c s : ℝ) (z : CV) (hcs : c ^ 2 + s ^ 2 = 1) :
    normSquared (rotation c s z) = normSquared z := by
  simp [normSquared, rotation, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  linear_combination
    ((z 1).re ^ 2 + (z 1).im ^ 2 + (z 2).re ^ 2 + (z 2).im ^ 2 +
     (z 3).re ^ 2 + (z 3).im ^ 2 + (z 4).re ^ 2 + (z 4).im ^ 2) * hcs

lemma rotation_inverse (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (z : CV) :
    rotation c (-s) (rotation c s z) = z := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  funext j
  fin_cases j <;> dsimp [rotation]
  all_goals simp only [Complex.ofReal_neg]
  · linear_combination z 1 * hc
  · linear_combination z 2 * hc
  · linear_combination z 3 * hc
  · linear_combination z 4 * hc

lemma rotation_phase (c s : ℝ) (a : ℂ) (z : CV) :
    rotation c s (a • z) = a • rotation c s z := by
  funext j
  fin_cases j <;> simp [rotation] <;> ring

@[simp] lemma rotation_start (z : CV) : rotation 1 0 z = z := by
  funext j
  fin_cases j <;> simp [rotation]

@[simp] lemma rotation_finish (z : CV) : rotation (-1) 0 z = involutionLinear z := by
  funext j
  fin_cases j <;> simp [rotation]

@[fun_prop] lemma contDiff_ofReal (n : WithTop ℕ∞) : ContDiff ℝ n Complex.ofReal :=
  Complex.ofRealCLM.contDiff

@[fun_prop] lemma contDiff_re (n : WithTop ℕ∞) : ContDiff ℝ n Complex.re :=
  Complex.reCLM.contDiff

@[fun_prop] lemma contDiff_im (n : WithTop ℕ∞) : ContDiff ℝ n Complex.im :=
  Complex.imCLM.contDiff

def rotationPath (p : ℝ × CV) : CV := rotation (Real.cos (Real.pi * p.1))
  (Real.sin (Real.pi * p.1)) p.2

lemma rotationPath_smooth : ContDiff ℝ ∞ rotationPath := by
  unfold rotationPath rotation
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp <;> fun_prop

lemma rotationPath_preserves (t : ℝ) (z : UnitQuadric) :
    IsUnitQuadric (rotationPath (t, z)) := by
  have hcs : Real.cos (Real.pi * t) ^ 2 + Real.sin (Real.pi * t) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  exact ⟨(rotation_normSquared _ _ _ hcs).trans z.property.1,
    (rotation_quadricPolynomial _ _ _ hcs).trans z.property.2⟩

lemma rotationPath_inverse (t : ℝ) (z : CV) :
    rotationPath (-t, rotationPath (t, z)) = z := by
  simpa only [rotationPath, mul_neg, Real.cos_neg, Real.sin_neg] using
    rotation_inverse _ _ (Real.cos_sq_add_sin_sq (Real.pi * t)) z

@[simp] lemma rotationPath_start (z : CV) : rotationPath (0, z) = z := by
  simp [rotationPath]

@[simp] lemma rotationPath_finish (z : CV) : rotationPath (1, z) = involutionLinear z := by
  simp [rotationPath]

lemma rotationPath_phase (t : ℝ) (a : ℂ) (z : CV) :
    rotationPath (t, a • z) = a • rotationPath (t, z) := rotation_phase _ _ _ _

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

/-- The ambient vector field generating the prescribed rotations. -/
def rotationGenerator (z : CV) : CV :=
  ![0, -(Real.pi : ℂ) * z 2, (Real.pi : ℂ) * z 1,
    -(Real.pi : ℂ) * z 4, (Real.pi : ℂ) * z 3]

/-- Minus alpha(Z), exactly the sign convention i_X omega = dH. -/
def rotationHamiltonian (z : CV) : ℝ :=
  2 * Real.pi * ((z 1).re * (z 2).im - (z 1).im * (z 2).re +
    (z 3).re * (z 4).im - (z 3).im * (z 4).re)

lemma rotationHamiltonian_smooth : ContDiff ℝ ∞ rotationHamiltonian := by
  unfold rotationHamiltonian
  fun_prop

lemma rotationHamiltonian_smul (a : ℂ) (z : CV) :
    rotationHamiltonian (a • z) = Complex.normSq a * rotationHamiltonian z := by
  simp only [rotationHamiltonian, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.mul_im, Complex.normSq_apply]
  ring

def realCoord (j : Fin 5) : CV →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj j)

def imagCoord (j : Fin 5) : CV →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj j)

@[simp] lemma realCoord_apply (j : Fin 5) (z : CV) : realCoord j z = (z j).re := rfl
@[simp] lemma imagCoord_apply (j : Fin 5) (z : CV) : imagCoord j z = (z j).im := rfl

def rotationHamiltonianDiff (z : CV) : CV →L[ℝ] ℝ :=
  (2 * Real.pi) • ((z 1).re • imagCoord 2 + (z 2).im • realCoord 1 -
    ((z 1).im • realCoord 2 + (z 2).re • imagCoord 1) +
    ((z 3).re • imagCoord 4 + (z 4).im • realCoord 3) -
    ((z 3).im • realCoord 4 + (z 4).re • imagCoord 3))

lemma rotationHamiltonian_hasFDerivAt (z : CV) :
    HasFDerivAt rotationHamiltonian (rotationHamiltonianDiff z) z := by
  have hr (j : Fin 5) := (realCoord j).hasFDerivAt (x := z)
  have hi (j : Fin 5) := (imagCoord j).hasFDerivAt (x := z)
  have h := ((((hr 1).mul (hi 2)).sub ((hi 1).mul (hr 2))).add
    ((hr 3).mul (hi 4))).sub ((hi 3).mul (hr 4))
  convert! h.const_mul (2 * Real.pi) using 1

lemma rotationHamiltonian_equation (z v : CV) :
    omega (rotationGenerator z) v = fderiv ℝ rotationHamiltonian z v := by
  rw [(rotationHamiltonian_hasFDerivAt z).fderiv]
  simp [omega, rotationGenerator, rotationHamiltonianDiff, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im]
  ring

lemma horizontal_finrank_real (z : UnitQuadric) :
    Module.finrank ℝ (LinearMap.ker (tangentConstraint z)) = 6 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, horizontal_finrank]

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

lemma rotationPath_hasDerivAt (t : ℝ) (z : CV) :
    HasDerivAt (fun s : ℝ ↦ rotationPath (s, z))
      (rotationGenerator (rotationPath (t, z))) t := by
  have hc := ((hasDerivAt_id t).const_mul Real.pi).cos.ofReal_comp
  have hs := ((hasDerivAt_id t).const_mul Real.pi).sin.ofReal_comp
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [rotationPath, rotation, rotationGenerator]
  · exact hasDerivAt_const t (z 0)
  · convert! (hc.mul_const (z 1)).sub (hs.mul_const (z 2)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  · convert! (hs.mul_const (z 1)).add (hc.mul_const (z 2)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  · convert! (hc.mul_const (z 3)).sub (hs.mul_const (z 4)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  · convert! (hs.mul_const (z 3)).add (hc.mul_const (z 4)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

/-- A complete explicit Hamiltonian witness for the actual quadric involution.
No flow existence, moment-map theorem, or descent theorem is assumed. -/
def involutionHamiltonianPath : HamiltonianPath involution where
  forward := rotationPath
  backward p := rotationPath (-p.1, p.2)
  hamiltonian p := rotationHamiltonian p.2
  forward_smooth := rotationPath_smooth
  backward_smooth := rotationPath_smooth.comp (contDiff_fst.neg.prodMk contDiff_snd)
  hamiltonian_smooth := rotationHamiltonian_smooth.comp contDiff_snd
  forward_preserves t _ z := rotationPath_preserves t z
  backward_preserves t _ z := rotationPath_preserves (-t) z
  forward_phase t _ z a _ := rotationPath_phase t a z
  backward_phase t _ z a _ := rotationPath_phase (-t) a z
  hamiltonian_phase t _ z a ha := by rw [rotationHamiltonian_smul, ha, one_mul]
  left_inverse t _ z := rotationPath_inverse t z
  right_inverse t _ z := by simpa only [neg_neg] using rotationPath_inverse (-t) z
  start z := rotationPath_start z
  finish z := by
    rw [involution_project]
    apply congrArg project
    apply Subtype.ext
    exact rotationPath_finish z
  equation t _ z v _ := by
    rw [(rotationPath_hasDerivAt t (z : CV)).deriv]
    exact rotationHamiltonian_equation _ v

/-- The explicit involution is Hamiltonian for the fixed
Fubini--Study normalization. -/
theorem involution_isHamiltonian : IsHamiltonian involution :=
  ⟨involutionHamiltonianPath⟩

end ArnoldCounterexample.Quadric

end

end OAI
