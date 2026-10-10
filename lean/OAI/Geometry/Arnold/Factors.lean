import OAI.Geometry.Arnold.Hessian

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints

/-- Oriented-plane coordinates of a unit isotropic vector. -/
def moment (a b : Fin 5) (z : CV) : ℝ := 2 * (star (z a) * z b).im

def planeMatrix (z : CV) : Matrix (Fin 5) (Fin 5) ℝ := fun a b ↦ moment a b z

lemma moment_real (a b : Fin 5) (z : CV) :
    moment a b z = 2 * ((z a).re * (z b).im - (z a).im * (z b).re) := by
  simp [moment, Complex.mul_im, sub_eq_add_neg]

lemma moment_skew (a b : Fin 5) (z : CV) : moment a b z = -moment b a z := by
  rw [moment_real, moment_real]
  ring

lemma moment_phase (a b : Fin 5) (z : CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    moment a b (c • z) = moment a b z := by
  have hn : star c * c = 1 := by
    change (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self, hc, Complex.ofReal_one]
  simp only [moment, Pi.smul_apply, smul_eq_mul, star_mul]
  rw [show star (z a) * star c * (c * z b) = (star c * c) * (star (z a) * z b) by ring, hn, one_mul]

lemma moment_smooth (a b : Fin 5) : ContDiff ℝ ∞ (moment a b) := by
  unfold moment
  fun_prop

/-- The two sphere factors, in self-dual / anti-self-dual plane coordinates. -/
def leftSphere (z : CV) : R3 :=
  ![moment 1 2 z + moment 3 4 z, moment 1 3 z - moment 2 4 z,
    moment 1 4 z + moment 2 3 z]

def rightSphere (z : CV) : R3 :=
  ![moment 1 2 z - moment 3 4 z, moment 1 3 z + moment 2 4 z,
    moment 1 4 z - moment 2 3 z]

def sphereFactors (z : CV) : Pair := (leftSphere z, rightSphere z)

def fourNorm (z : CV) : ℝ := ∑ i : Fin 4, Complex.normSq (z i.succ)
def fourPolynomial (z : CV) : ℂ := ∑ i : Fin 4, z i.succ ^ 2

lemma sphere_norm_identity (z : CV) :
    sqNorm (leftSphere z) + (fourPolynomial z).re ^ 2 + (fourPolynomial z).im ^ 2 = fourNorm z ^ 2 ∧
    sqNorm (rightSphere z) + (fourPolynomial z).re ^ 2 + (fourPolynomial z).im ^ 2 = fourNorm z ^ 2 := by
  change (((moment 1 2 z + moment 3 4 z)^2 + (moment 1 3 z - moment 2 4 z)^2 +
    (moment 1 4 z + moment 2 3 z)^2) + _ + _ = _) ∧
    (((moment 1 2 z - moment 3 4 z)^2 + (moment 1 3 z + moment 2 4 z)^2 +
    (moment 1 4 z - moment 2 3 z)^2) + _ + _ = _)
  norm_num [ moment_real, fourPolynomial, fourNorm,
    Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  constructor <;> ring!

lemma sphereFactors_mem (z : UnitQuadric) (hz : (z : CV) 0 = 0) :
    sphereFactors z ∈ sphereProduct := by
  have hn : fourNorm z = 1 := by
    have h := z.property.1
    simpa only [normSquared, Fin.sum_univ_succ, hz, Complex.normSq_zero, zero_add, fourNorm] using h
  have hp : fourPolynomial z = 0 := by
    have h := z.property.2
    simpa only [quadricPolynomial, Fin.sum_univ_succ, hz, zero_pow (by decide : 2 ≠ 0), zero_add,
      fourPolynomial] using h
  have h := sphere_norm_identity z
  simpa only [sphereFactors, sphereProduct, Set.mem_ofPred_eq, hp, Complex.zero_re,
    Complex.zero_im, zero_pow (by decide : 2 ≠ 0), add_zero, hn, one_pow] using h

lemma sphereFactors_smooth : ContDiff ℝ ∞ sphereFactors := by
  apply ContDiff.prodMk
  all_goals
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [leftSphere, rightSphere]
    all_goals first | exact (moment_smooth _ _).add (moment_smooth _ _) | exact (moment_smooth _ _).sub (moment_smooth _ _)

lemma planeMatrix_of_sphereFactors (z w : CV) (hz : z 0 = 0) (hw : w 0 = 0)
    (h : sphereFactors z = sphereFactors w) : planeMatrix z = planeMatrix w := by
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hl0 := congrFun hl 0
  have hl1 := congrFun hl 1
  have hl2 := congrFun hl 2
  have hr0 := congrFun hr 0
  have hr1 := congrFun hr 1
  have hr2 := congrFun hr 2
  simp [sphereFactors, leftSphere, rightSphere] at hl0 hl1 hl2 hr0 hr1 hr2
  have h12 : moment 1 2 z = moment 1 2 w := by linarith
  have h34 : moment 3 4 z = moment 3 4 w := by linarith
  have h13 : moment 1 3 z = moment 1 3 w := by linarith
  have h24 : moment 2 4 z = moment 2 4 w := by linarith
  have h14 : moment 1 4 z = moment 1 4 w := by linarith
  have h23 : moment 2 3 z = moment 2 3 w := by linarith
  have hzero (i : Fin 5) (v : CV) : moment i i v = 0 := by rw [moment_real]; ring
  have h0z (i : Fin 5) : moment 0 i z = 0 := by simp [moment, hz]
  have h0w (i : Fin 5) : moment 0 i w = 0 := by simp [moment, hw]
  ext i j
  change moment i j z = moment i j w
  have h0zr (i : Fin 5) : moment i 0 z = 0 := by rw [moment_skew, h0z, neg_zero]
  have h0wr (i : Fin 5) : moment i 0 w = 0 := by rw [moment_skew, h0w, neg_zero]
  fin_cases i <;> fin_cases j <;>
    first | exact h12 | exact h34 | exact h13 | exact h24 | exact h14 | exact h23 |
      (change moment 0 _ z = moment 0 _ w; rw [h0z, h0w]) |
      (change moment _ 0 z = moment _ 0 w; rw [h0zr, h0wr]) |
      solve | simp only [hzero] |
      (rw [moment_skew _ _ z, moment_skew _ _ w]; congr 1)

end ArnoldCounterexample.Factors

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric

def hermitian (z w : CV) : ℂ := ∑ i, star (z i) * w i

def complexDot (z w : CV) : ℂ := ∑ i, z i * w i

lemma hermitian_self (z : UnitQuadric) : hermitian z z = 1 := by
  have he : hermitian z z = (normSquared z : ℂ) := by
    simp only [hermitian, normSquared, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (Complex.normSq_eq_conj_mul_self).symm
  rw [he, z.property.1, Complex.ofReal_one]

lemma complexDot_self (z : UnitQuadric) : complexDot z z = 0 := by
  simpa only [complexDot, quadricPolynomial, pow_two] using z.property.2

lemma moment_complex (a b : Fin 5) (z : CV) :
    (moment a b z : ℂ) = Complex.I * (z a * star (z b) - star (z a) * z b) := by
  apply Complex.ext <;> simp [moment_real, Complex.mul_re, Complex.mul_im]
  ring

lemma matrix_apply (z w : CV) (a : Fin 5) :
    (∑ b, (moment a b z : ℂ) * w b) =
      Complex.I * (z a * hermitian z w - star (z a) * complexDot z w) := by
  simp only [hermitian, complexDot, Finset.mul_sum, moment_complex]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma planeMatrix_project_injective (z w : UnitQuadric) (h : planeMatrix z = planeMatrix w) :
    project z = project w := by
  have hw (a : Fin 5) : (w : CV) a = (z : CV) a * hermitian z w - star ((z : CV) a) * complexDot z w := by
    have hm : (∑ b, (moment a b z : ℂ) * (w : CV) b) = ∑ b, (moment a b w : ℂ) * (w : CV) b := by
      apply Finset.sum_congr rfl
      intro b _
      have hab := congrFun (congrFun h a) b
      change moment a b z = moment a b w at hab
      rw [hab]
    rw [matrix_apply, matrix_apply, hermitian_self, complexDot_self, mul_one, mul_zero, sub_zero] at hm
    exact (mul_left_cancel₀ Complex.I_ne_zero hm).symm
  have hb : complexDot z w = 0 := by
    have he : complexDot z w = complexDot z z * hermitian z w - hermitian z z * complexDot z w := by
      simp only [complexDot, hermitian, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [hw a]
      dsimp [complexDot, hermitian]
      ring
    rw [complexDot_self, hermitian_self, zero_mul, one_mul, zero_sub] at he
    have he' := congrArg (fun c : ℂ ↦ c + complexDot z w) he
    simp only [neg_add_cancel] at he'
    exact (add_self_eq_zero.mp he')
  have he : (w : CV) = hermitian z w • (z : CV) := by
    ext a
    rw [hw a, hb, mul_zero, sub_zero]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  apply Subtype.ext
  change Projectivization.mk ℂ (z : CV) _ = Projectivization.mk ℂ (w : CV) _
  symm
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨hermitian z w, he.symm⟩

lemma sphereFactors_project_injective (z w : UnitQuadric)
    (hz : (z : CV) 0 = 0) (hw : (w : CV) 0 = 0) (h : sphereFactors z = sphereFactors w) :
    project z = project w :=
  planeMatrix_project_injective z w (planeMatrix_of_sphereFactors z w hz hw h)

end ArnoldCounterexample.Factors

end

end OAI
