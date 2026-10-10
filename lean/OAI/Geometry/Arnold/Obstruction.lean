import OAI.Geometry.Arnold.Volume

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The literal orthogonal action, bundled as a real continuous linear map. -/
def actCLM (A : RM) : CV →L[ℝ] CV :=
  ((complexMat A).mulVecLin.restrictScalars ℝ).toContinuousLinearMap

@[simp] lemma actCLM_apply (A : RM) (z : CV) : actCLM A z = act A z := rfl

lemma symplectic_act (A : O5) :
    (symplectic 5).bilinearComp (actCLM A) (actCLM A) = symplectic 5 := by
  ext u v
  simpa only [ContinuousLinearMap.bilinearComp_apply, actCLM_apply, symplectic_eq,
    omega] using omega_act A u v

lemma cubeForm_orbit (A : O5) :
    cubeForm (symplectic 5) (fun i ↦ act A (velocities i)) = 48 := by
  have h := congrArg (fun θ : CV [⋀^Fin 6]→L[ℝ] ℝ ↦ θ velocities)
    (cubeForm_pullback (symplectic 5) (actCLM A))
  simpa only [compContinuousLinearMap_apply, Function.comp_def, actCLM_apply,
    symplectic_act, cubeForm_velocities] using h

/-- Standard join homotopy of the two equivariant sphere maps. -/
def joinHomotopy (F : CV → CSpace 3) (p : ℝ × RM) : ProductSpace :=
  (Real.cos p.1 • orbitProjection p.2, Real.sin p.1 • F (orbitProjection p.2))

lemma joinHomotopy_contDiff (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (joinHomotopy F) := by
  exact (Real.contDiff_cos.comp contDiff_fst |>.smul (orbitProjection.contDiff.comp contDiff_snd)).prodMk
    (Real.contDiff_sin.comp contDiff_fst |>.smul (hF.comp (orbitProjection.contDiff.comp contDiff_snd)))

lemma joinHomotopy_unit (F : CV → CSpace 3)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (t : ℝ) (A : O5) :
    productNormSq (joinHomotopy F (t, A)) = 1 := by
  simp only [productNormSq, joinHomotopy, normSq_real_smul]
  rw [show normSq 5 (orbitProjection A) = 1 from (orbitProjection_unit A).1,
    hunit ⟨orbitProjection A, orbitProjection_unit A⟩]
  nlinarith [Real.sin_sq_add_cos_sq t]

lemma joinHomotopy_fderiv_spatial (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (A B : RM) :
    fderiv ℝ (joinHomotopy F) (t, A) (0, B) =
      (Real.cos t • orbitProjection B,
       Real.sin t • fderiv ℝ F (orbitProjection A) (orbitProjection B)) := by
  have hp : HasDerivAt (fun s : ℝ ↦ (t, A + s • B)) (0, B) 0 := by
    convert (hasDerivAt_const 0 t).prodMk ((hasDerivAt_const 0 A).add
      ((hasDerivAt_id (0 : ℝ)).smul_const B)) using 1 <;> simp
  have hd := (joinHomotopy_contDiff F hF |>.differentiable (by simp) (t, A + 0 • B)).hasFDerivAt.comp_hasDerivAt 0 hp
  have ho : HasDerivAt (fun s : ℝ ↦ orbitProjection (A + s • B)) (orbitProjection B) 0 := by
    convert! orbitProjection.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 A).add ((hasDerivAt_id (0 : ℝ)).smul_const B)) using 1; simp
  have hf := (hF.differentiable (by simp) (orbitProjection (A + 0 • B))).hasFDerivAt.comp_hasDerivAt 0 ho
  have hh := (ho.const_smul (Real.cos t)).prodMk (hf.const_smul (Real.sin t))
  simpa only [Function.comp_def, zero_smul, add_zero, joinHomotopy] using hd.unique hh

lemma joinHomotopy_spatial_tangent (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1)
    (t : ℝ) (A : O5) (X : RM) (hX : star X = -X) :
    productSymplectic (Complex.I • joinHomotopy F (t, A))
      (fderiv ℝ (joinHomotopy F) (t, A) (0, (A : RM) * X)) = 0 := by
  have hd := (joinHomotopy_contDiff F hF |>.differentiable (by simp)
      (t, ((A * expCurve X hX 0 : O5) : RM))).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const 0 t).prodMk (right_expCurve_hasDerivAt X hX A 0))
  have hz := productNormSq_curve_orthogonal hd
    (fun s ↦ joinHomotopy_unit F hunit t (A * expCurve X hX s))
  simpa [expCurve] using hz

lemma joinHomotopy_time_tangent (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (t : ℝ) (A : O5) :
    productSymplectic (Complex.I • joinHomotopy F (t, A))
      (fderiv ℝ (joinHomotopy F) (t, A) (1, 0)) = 0 :=
  productNormSq_time_tangent (joinHomotopy F) (joinHomotopy_contDiff F hF) (A : RM)
    (fun s ↦ joinHomotopy_unit F hunit s A) t

lemma joinHomotopy_bracket (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z)
    (t : ℝ) (A : O5) (i j : Fin 6) :
    fderiv ℝ (joinHomotopy F) (t, A)
      (0, (A : RM) * (generators i * generators j - generators j * generators i)) =
    bracketCoefficient i j • (Complex.I • joinHomotopy F (t, A)) := by
  rw [joinHomotopy_fderiv_spatial F hF]
  simp only [orbitProjection_apply, act_mul, generators_bracket_base, act_smul]
  have heq : ((bracketCoefficient i j : ℝ) : ℂ) • (Complex.I • act A base) =
      bracketCoefficient i j • (Complex.I • act A base) := by
    ext k
    simp [Complex.real_smul]
  have hfp : fderiv ℝ F (act A base) (Complex.I • act A base) = Complex.I • F (act A base) :=
    fderiv_circle_equivariant F (hF.differentiable (by simp)) (act A base)
      (hphase ⟨orbitProjection A, orbitProjection_unit A⟩)
  rw [heq, map_smul, hfp]
  ext k <;> simp only [joinHomotopy, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, orbitProjection_apply] <;> ring

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

lemma haar_mass_pos : 0 < (haar Set.univ).toReal := by
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos haar Set.univ_nonempty).ne'
    (measure_ne_top _ _)

local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

lemma productSymplectic_inl :
    productSymplectic.bilinearComp (ContinuousLinearMap.inl ℝ (CSpace 5) (CSpace 3))
      (ContinuousLinearMap.inl ℝ (CSpace 5) (CSpace 3)) = symplectic 5 := by
  ext u v
  simp [productSymplectic_apply]

lemma productSymplectic_inr :
    productSymplectic.bilinearComp (ContinuousLinearMap.inr ℝ (CSpace 5) (CSpace 3))
      (ContinuousLinearMap.inr ℝ (CSpace 5) (CSpace 3)) = symplectic 3 := by
  ext u v
  simp [productSymplectic_apply]

lemma joinHomotopy_zero_cube (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F) (A : O5) :
    cubeForm productSymplectic
      (fun i ↦ fderiv ℝ (joinHomotopy F) (0, A) (0, (A : RM) * generators i)) = 48 := by
  have h := congrArg (fun θ : CV [⋀^Fin 6]→L[ℝ] ℝ ↦ θ (fun i ↦ act A (velocities i)))
    (cubeForm_pullback productSymplectic (ContinuousLinearMap.inl ℝ (CSpace 5) (CSpace 3)))
  simp only [productSymplectic_inl, cubeForm_orbit] at h
  simpa only [joinHomotopy_fderiv_spatial F hF, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, orbitProjection_apply, act_mul, generators_base,
    compContinuousLinearMap_apply, Function.comp_def, ContinuousLinearMap.inl_apply] using h

lemma sphere_map_tangent (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (A : O5) (i : Fin 6) :
    fderiv ℝ (normSq 3) (F (orbitProjection A))
      (fderiv ℝ F (orbitProjection A) (act A (velocities i))) = 0 := by
  have hf := (hF.differentiable (by simp)
      (orbitProjection ((A * expCurve (generators i) (generators_skew i) 0 : O5) : RM))).hasFDerivAt.comp_hasDerivAt 0
    (orbitProjection.hasFDerivAt.comp_hasDerivAt 0
      (right_expCurve_hasDerivAt (generators i) (generators_skew i) A 0))
  have hn := (normSq_contDiff 3 |>.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 hf
  have heq : (fun t ↦ normSq 3 (F (orbitProjection
      ((A * expCurve (generators i) (generators_skew i) t : O5) : RM)))) =
      fun _ : ℝ ↦ 1 := funext (fun t ↦ hunit
        ⟨orbitProjection ((A * expCurve (generators i) (generators_skew i) t : O5) : RM),
          orbitProjection_unit _⟩)
  dsimp only [Function.comp_def] at hn
  rw [heq] at hn
  have hz := hn.unique (hasDerivAt_const 0 1)
  simpa [expCurve, orbitProjection_apply, act_mul, generators_base] using hz

lemma joinHomotopy_half_pi_cube (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (A : O5) :
    cubeForm productSymplectic
      (fun i ↦ fderiv ℝ (joinHomotopy F) (Real.pi / 2, A) (0, (A : RM) * generators i)) = 0 := by
  let v : Fin 6 → CSpace 3 := fun i ↦ fderiv ℝ F (orbitProjection A) (act A (velocities i))
  have h := congrArg (fun θ : CSpace 3 [⋀^Fin 6]→L[ℝ] ℝ ↦ θ v)
    (cubeForm_pullback productSymplectic (ContinuousLinearMap.inr ℝ (CSpace 5) (CSpace 3)))
  rw [productSymplectic_inr] at h
  have hz : cubeForm (symplectic 3) v = 0 := six_form_vanishes_on_unit_sphere _
    (F (orbitProjection A)) (hunit ⟨orbitProjection A, orbitProjection_unit A⟩) v
    (fun i ↦ sphere_map_tangent F hF hunit A i)
  rw [hz] at h
  simpa only [joinHomotopy_fderiv_spatial F hF, Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_smul, zero_smul, orbitProjection_apply, act_mul, generators_base,
    compContinuousLinearMap_apply, Function.comp_def, ContinuousLinearMap.inr_apply, v] using h

/-- The concrete cup-length obstruction: there is no smooth circle-equivariant
map from the literal unit isotropic cone in C5 into the unit sphere in C3.
The obstruction is the nonzero third symplectic power. -/
theorem no_unit_equivariant_map (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) :
    False := by
  let Θ : ℝ × RM → (ℝ × RM) [⋀^Fin 6]→L[ℝ] ℝ :=
    fun p ↦ (cubeForm productSymplectic).compContinuousLinearMap (fderiv ℝ (joinHomotopy F) p)
  have hΘ : ContDiff ℝ ∞ Θ := contDiff_pullback_form contDiff_const
    ((joinHomotopy_contDiff F hF).fderiv_right (by simp))
  have hclosed (p : ℝ × RM) : extDeriv Θ p = 0 :=
    pullback_constant_closed (cubeForm productSymplectic) (joinHomotopy F)
      (joinHomotopy_contDiff F hF) p
  have hv (t : ℝ) (A : O5) (i j : Fin 5) :
      sliceContraction Θ t A
        (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
          generators j.succ * generators i.castSucc))
          (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0 := by
    change cubeForm productSymplectic ((fderiv ℝ (joinHomotopy F) (t, A)) ∘ _ ) = 0
    change cubeForm productSymplectic ((fderiv ℝ (joinHomotopy F) (t, A)) ∘
      (Fin.cons (1, 0) (spatial ∘ Fin.cons _ _))) = 0
    rw [Fin.comp_cons, Fin.comp_cons, Fin.comp_cons]
    simp only [spatial, ContinuousLinearMap.prod_apply, _root_.zero_apply,
      ContinuousLinearMap.id_apply]
    rw [joinHomotopy_bracket F hF hphase]
    apply cubeForm_second_radical_on productSymplectic productSymplectic_skew
    · simp only [map_smul, _root_.smul_apply,
        joinHomotopy_time_tangent F hF hunit, smul_zero]
    · intro k
      simp only [map_smul, _root_.smul_apply, Function.comp_def, Fin.removeNth_apply,
        ContinuousLinearMap.prod_apply, _root_.zero_apply, ContinuousLinearMap.id_apply]
      rw [joinHomotopy_spatial_tangent F hF hunit t A _ (generators_skew _), smul_zero]
  have hi := haar_homotopy_invariant Θ hΘ hclosed hv 0 (Real.pi / 2)
  have h0 (A : O5) : Θ (0, A) (fun i ↦ (0, (A : RM) * generators i)) = 48 :=
    joinHomotopy_zero_cube F hF A
  have h1 (A : O5) : Θ (Real.pi / 2, A) (fun i ↦ (0, (A : RM) * generators i)) = 0 :=
    joinHomotopy_half_pi_cube F hF hunit A
  simp_rw [h0, h1] at hi
  have hmass : 0 < (haar Set.univ).toReal := haar_mass_pos
  simp only [integral_const, smul_eq_mul, mul_zero] at hi
  change (haar Set.univ).toReal * 48 = 0 at hi
  nlinarith

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample
open CriticalBound

/-- The lower bound for every smooth function, including all
possible degenerate critical points. No Morse assumption is made. -/
theorem four_le_criticalSet (h : SmoothFunction) : 4 ≤ (criticalSet h).encard := by
  by_contra hn
  have hs : (criticalSet h).encard ≤ 3 := by
    exact Order.le_of_lt_add_one (lt_of_not_ge hn)
  obtain ⟨F₀, hF₀, hne, hphase₀⟩ := cover_map h hs
  obtain ⟨F, hF, hunit, hphase⟩ := normalize_cover_map hF₀ hne hphase₀
  exact no_unit_equivariant_map F hF hunit hphase

/-- The critical-number half of the exact main theorem. -/
theorem four_le_criticalNumber : 4 ≤ criticalNumber :=
  le_iInf four_le_criticalSet

end ArnoldCounterexample

end

end OAI
