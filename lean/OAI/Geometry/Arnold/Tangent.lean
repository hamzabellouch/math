import OAI.Geometry.Arnold.Rotation

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

def normSquaredDiff (z : CV) : CV →L[ℝ] ℝ :=
  ∑ j, ((2 * (z j).re) • realCoord j + (2 * (z j).im) • imagCoord j)

lemma normSquared_hasFDerivAt (z : CV) :
    HasFDerivAt normSquared (normSquaredDiff z) z := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun (j : Fin 5) _ ↦
    ((realCoord j).hasFDerivAt (x := z) |>.pow 2).add
      ((imagCoord j).hasFDerivAt (x := z) |>.pow 2))
  convert! h using 1
  · ext y
    simp [normSquared, Complex.normSq_apply, pow_two]
  · simp [normSquaredDiff, two_mul]

lemma normSquaredDiff_apply (z v : CV) :
    normSquaredDiff z v = 2 * (bilinear (star z) v).re := by
  have hs : (bilinear (star z) v).re = ∑ j, (star (z j) * v j).re := by
    simpa only [bilinear, Pi.star_apply, Complex.coe_reAddGroupHom] using
      (map_sum Complex.reAddGroupHom (fun j : Fin 5 ↦ star (z j) * v j) Finset.univ)
  rw [hs]
  simp only [normSquaredDiff, sum_apply, add_apply,
    smul_apply, realCoord_apply, imagCoord_apply, smul_eq_mul,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma normSquared_smooth : ContDiff ℝ ∞ normSquared := by
  unfold normSquared
  simp only [Complex.normSq_apply]
  fun_prop

lemma quadricPolynomial_smooth : ContDiff ℝ ∞ quadricPolynomial := by
  unfold quadricPolynomial
  fun_prop

/-- Normalizing a nonzero isotropic vector gives a legitimate unit representative. -/
def normalize (w : CV) : CV := (Real.sqrt (normSquared w))⁻¹ • w

lemma normalize_unit {w : CV} (hw : w ≠ 0) (hp : quadricPolynomial w = 0) :
    IsUnitQuadric (normalize w) := by
  have hn : 0 < normSquared w := normSquared_pos hw
  have hs : Real.sqrt (normSquared w) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have heq : normalize w = (((Real.sqrt (normSquared w))⁻¹ : ℝ) : ℂ) • w := rfl
  rw [heq]
  constructor
  · rw [normSquared_smul, Complex.normSq_ofReal]
    field_simp [hs]
    nlinarith only [Real.sq_sqrt hn.le]
  · rw [quadricPolynomial_smul, hp, mul_zero]

lemma normalize_unit_self (z : UnitQuadric) : normalize (z : CV) = z := by
  simp [normalize, z.property.1]

/-- A polynomial curve on the nonzero isotropic cone realizing a horizontal vector. -/
def rawTangentCurve (z v : CV) (t : ℝ) : CV :=
  z + t • v - (t ^ 2 / 2) • (quadricPolynomial v • star z)

lemma rawTangentCurve_eq (z v : CV) (t : ℝ) :
    rawTangentCurve z v t = localSection z ((t : ℂ) • v) := by
  rw [localSection, quadricPolynomial_smul]
  funext j
  simp only [rawTangentCurve, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

@[simp] lemma rawTangentCurve_zero (z v : CV) : rawTangentCurve z v 0 = z := by
  simp [rawTangentCurve]

lemma rawTangentCurve_hasDerivAt_zero (z v : CV) :
    HasDerivAt (rawTangentCurve z v) v 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id 0).smul_const v)).sub
    (((hasDerivAt_id (0 : ℝ)).pow 2 |>.div_const 2).smul_const
      (quadricPolynomial v • star z))
  convert! h using 1
  simp

lemma rawTangentCurve_ne_zero (z : UnitQuadric) {v : CV} (hv : Horizontal z v) (t : ℝ) :
    rawTangentCurve z v t ≠ 0 := by
  rw [rawTangentCurve_eq]
  exact localSection_ne_zero z (horizontal_smul hv (t : ℂ))

lemma rawTangentCurve_polynomial (z : UnitQuadric) {v : CV} (hv : Horizontal z v) (t : ℝ) :
    quadricPolynomial (rawTangentCurve z v t) = 0 := by
  rw [rawTangentCurve_eq]
  exact localSection_on_quadric z (horizontal_smul hv (t : ℂ))

/-- A genuine curve in the unit cone, not an assumed tangent parametrization. -/
def tangentCurve (z : UnitQuadric) (v : CV) (hv : Horizontal z v) (t : ℝ) : UnitQuadric :=
  ⟨normalize (rawTangentCurve z v t), normalize_unit (rawTangentCurve_ne_zero z hv t)
    (rawTangentCurve_polynomial z hv t)⟩

@[simp] lemma tangentCurve_zero (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    tangentCurve z v hv 0 = z := by
  apply Subtype.ext
  exact (congrArg normalize (rawTangentCurve_zero z v)).trans (normalize_unit_self z)

/-- Every declared horizontal tangent is realized by an actual differentiable
curve in the literal unit isotropic cone. -/
theorem tangentCurve_hasDerivAt_zero (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    HasDerivAt (fun t ↦ (tangentCurve z v hv t : CV)) v 0 := by
  have hr := rawTangentCurve_hasDerivAt_zero z v
  have hn : HasDerivAt (fun t ↦ normSquared (rawTangentCurve z v t)) 0 0 := by
    have hn' := (normSquared_hasFDerivAt (rawTangentCurve z v 0)).comp_hasDerivAt 0 hr
    simpa only [rawTangentCurve_zero, normSquaredDiff_apply, show bilinear (star (z : CV)) v = 0 from hv.1,
      Complex.zero_re, mul_zero, Function.comp_def] using hn'
  have hnzero : normSquared (rawTangentCurve z v 0) = 1 := by
    rw [rawTangentCurve_zero, z.property.1]
  have hs := hn.sqrt (by rw [hnzero]; norm_num)
  have hi := hs.inv (by rw [hnzero]; norm_num)
  have h := hi.smul hr
  convert! h using 1
  simp [z.property.1]

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

/-- Smoothness in the local-lift definition implies actual continuity
on the compact unit cone. No topology on a substitute finite model is used. -/
theorem smoothFunction_continuous_pullback {h : Q3 → ℝ} (hh : IsSmoothFunction h) :
    Continuous (h ∘ project) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨U, g, hU, hz, hg, hagree⟩ := hh z
  have hc : ContinuousAt (fun y : UnitQuadric ↦ g (y : CV)) z :=
    (hg.contDiffAt (hU.mem_nhds hz)).continuousAt.comp continuous_subtype_val.continuousAt
  have heq : (h ∘ project) =ᶠ[nhds z] (fun y : UnitQuadric ↦ g (y : CV)) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hU.mem_nhds hz)] with y hy
    exact (hagree y hy).symm
  exact hc.congr heq.symm

/-- The criticality definition is nonvacuous: every global minimum is
critical with respect to every local ambient lift. -/
theorem isCritical_of_global_min {h : Q3 → ℝ} {q : Q3}
    (hmin : ∀ r, h q ≤ h r) : IsCritical h q := by
  intro z hz U g hg v hv
  obtain ⟨hU, hzU, hgs, hagree⟩ := hg
  have hc := tangentCurve_hasDerivAt_zero z v hv
  have hd := (hgs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by norm_num)
  have hd' : HasFDerivAt g (fderiv ℝ g z) (tangentCurve z v hv 0 : CV) := by
    simpa only [tangentCurve_zero] using hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt 0 hc
  have hmem : ∀ᶠ t in nhds (0 : ℝ), (tangentCurve z v hv t : CV) ∈ U :=
    hc.continuousAt.eventually (by
      convert! hU.mem_nhds hzU using 1
      simp)
  have hlocal : IsLocalMin (fun t ↦ g (tangentCurve z v hv t)) 0 := by
    change ∀ᶠ t in nhds (0 : ℝ), g (tangentCurve z v hv 0) ≤ g (tangentCurve z v hv t)
    filter_upwards [hmem] with t ht
    calc
      g (tangentCurve z v hv 0) = h q := by rw [tangentCurve_zero, hagree z hzU, hz]
      _ ≤ h (project (tangentCurve z v hv t)) := hmin _
      _ = g (tangentCurve z v hv t) := (hagree _ ht).symm
  have hcomp' : HasDerivAt (fun t ↦ g (tangentCurve z v hv t)) (fderiv ℝ g z v) 0 := by
    simpa only [Function.comp_def, tangentCurve_zero] using hcomp
  exact hlocal.hasDerivAt_eq_zero hcomp'

theorem isClosed_unitQuadric : IsClosed {z : CV | IsUnitQuadric z} :=
  (isClosed_eq normSquared_smooth.continuous continuous_const).inter
    (isClosed_eq quadricPolynomial_smooth.continuous continuous_const)

lemma unitQuadric_norm_le (z : UnitQuadric) : ‖(z : CV)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  have hj : Complex.normSq ((z : CV) j) ≤ normSquared z :=
    Finset.single_le_sum (fun i _ ↦ Complex.normSq_nonneg ((z : CV) i)) (Finset.mem_univ j)
  rw [z.property.1, Complex.normSq_eq_norm_sq] at hj
  nlinarith [norm_nonneg ((z : CV) j)]

/-- Compactness of the literal unit cone, obtained from finite-dimensional
Heine--Borel and the exact polynomial constraints. -/
theorem isCompact_unitQuadric : IsCompact {z : CV | IsUnitQuadric z} := by
  apply (isCompact_closedBall (0 : CV) 1).of_isClosed_subset isClosed_unitQuadric
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using unitQuadric_norm_le ⟨z, hz⟩

instance unitQuadric_compactSpace : CompactSpace UnitQuadric :=
  isCompact_iff_compactSpace.mp isCompact_unitQuadric

def baseVector : CV := ![1, Complex.I, 0, 0, 0]

lemma baseVector_ne_zero : baseVector ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [baseVector] at hh

lemma baseVector_polynomial : quadricPolynomial baseVector = 0 := by
  norm_num [quadricPolynomial, baseVector, Fin.sum_univ_five, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Complex.I_sq]

def basePoint : UnitQuadric := ⟨normalize baseVector,
  normalize_unit baseVector_ne_zero baseVector_polynomial⟩

instance unitQuadric_nonempty : Nonempty UnitQuadric := ⟨basePoint⟩

/-- Every smooth function on the actual quadric attains a critical minimum. -/
theorem criticalSet_nonempty (h : SmoothFunction) : (criticalSet h).Nonempty := by
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty :
    (Set.univ : Set UnitQuadric).Nonempty) (smoothFunction_continuous_pullback h.smooth).continuousOn
  refine ⟨project z, isCritical_of_global_min ?_⟩
  intro q
  obtain ⟨w, rfl⟩ := project_surjective q
  exact hz (Set.mem_univ w)

end ArnoldCounterexample.Quadric

end

end OAI
