import OAI.Geometry.Riemannian.HarmonicCore.Model

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace HarmonicCounterexample.Main.SmoothMetric3

def dirichletTests (R : ℝ) : Submodule ℝ (E3 → ℝ) where
  carrier := {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Metric.ball 0 R}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro u v hu hv
    refine ⟨hu.1.add hv.1,hu.2.1.add hv.2.1,?_⟩
    exact (tsupport_add u v).trans (union_subset hu.2.2 hv.2.2)
  smul_mem' := by
    intro c u hu
    refine ⟨hu.1.const_smul c,hu.2.1.smul_left,?_⟩
    exact (tsupport_smul_subset_right (fun _ : E3 ↦ c) u).trans hu.2.2

abbrev DirichletTest (R : ℝ) := ↥(dirichletTests R)
abbrev Derivative3 := StrongDual ℝ E3
abbrev ValueL2 := Lp ℝ 2 (volume : Measure E3)
abbrev DerivativeL2 := Lp E3 2 (volume : Measure E3)
abbrev SobolevPair := WithLp 2 (ValueL2 × DerivativeL2)

lemma DirichletTest.value_memLp {R : ℝ} (u : DirichletTest R) :
    MemLp (u : E3 → ℝ) 2 (volume : Measure E3) :=
  u.property.1.continuous.memLp_of_hasCompactSupport u.property.2.1

lemma gradient_continuous {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (gradient u) := by
  exact (InnerProductSpace.toDual ℝ E3).symm.continuous.comp
    (hu.continuous_fderiv (by simp))

lemma gradient_compact {u : E3 → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (gradient u) := by
  exact (hu.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E3).symm)

lemma gradient_norm_fderiv (u : E3 → ℝ) (x : E3) :
    ‖gradient u x‖ = ‖fderiv ℝ u x‖ :=
  (InnerProductSpace.toDual ℝ E3).symm.norm_map _

lemma DirichletTest.derivative_memLp {R : ℝ} (u : DirichletTest R) :
    MemLp (gradient (u : E3 → ℝ)) 2 (volume : Measure E3) :=
  (gradient_continuous u.property.1).memLp_of_hasCompactSupport
    (gradient_compact u.property.2.1)

noncomputable def DirichletTest.value {R : ℝ} (u : DirichletTest R) : ValueL2 :=
  u.value_memLp.toLp u

noncomputable def DirichletTest.derivative {R : ℝ} (u : DirichletTest R) : DerivativeL2 :=
  u.derivative_memLp.toLp (gradient (u : E3 → ℝ))

lemma DirichletTest.poincare {R : ℝ} (u : DirichletTest R) :
    ‖u.value‖ ≤ (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure E3)
        (Metric.ball (0:E3) R) 2 2 : ℝ)*‖u.derivative‖ := by
  have hh := eLpNorm_le_eLpNorm_fderiv_of_le (volume : Measure E3)
    (u.property.1.of_le (by norm_cast) : ContDiff ℝ 1 (u : E3 → ℝ))
    ((subset_tsupport (u:E3 → ℝ)).trans u.property.2.2) (p:=2) (q:=2) (by norm_num)
    (by norm_num [E3,finrank_euclideanSpace])
    (by norm_num [E3,finrank_euclideanSpace]) (Metric.isBounded_ball)
  have hn : eLpNorm (fderiv ℝ (u : E3 → ℝ)) 2 (volume : Measure E3) =
      eLpNorm (gradient (u : E3 → ℝ)) 2 (volume : Measure E3) :=
    eLpNorm_congr_norm_ae (u.property.1.continuous_fderiv (by simp)).aestronglyMeasurable
      u.derivative_memLp.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (gradient_norm_fderiv u x).symm))
  norm_num only [ENNReal.coe_ofNat] at hh
  rw [hn] at hh
  rw [DirichletTest.value,DirichletTest.derivative,Lp.norm_toLp,Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top u.derivative_memLp.ne) hh

lemma gradient_add_smooth {u v : E3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) : gradient (u + v) = gradient u + gradient v := by
  funext x
  simp only [gradient, Pi.add_apply]
  rw [fderiv_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x), map_add]

lemma gradient_smul_smooth {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) :
    gradient (c • u) = c • gradient u := by
  funext x
  simp only [gradient, Pi.smul_apply]
  rw [fderiv_const_smul (hu.differentiable (by simp) x), map_smul]

noncomputable def testValueLinear (R : ℝ) : DirichletTest R →ₗ[ℝ] ValueL2 where
  toFun u := u.value
  map_add' u v := u.value_memLp.toLp_add v.value_memLp
  map_smul' c u := u.value_memLp.toLp_const_smul c

noncomputable def testDerivativeLinear (R : ℝ) : DirichletTest R →ₗ[ℝ] DerivativeL2 where
  toFun u := u.derivative
  map_add' u v := by
    change (u+v).derivative_memLp.toLp _ = _
    have he : gradient ((u+v : DirichletTest R) : E3 → ℝ) = gradient (u : E3 → ℝ) + gradient (v : E3 → ℝ) :=
      gradient_add_smooth u.property.1 v.property.1
    simp only [he]
    exact u.derivative_memLp.toLp_add v.derivative_memLp
  map_smul' c u := by
    change (c • u).derivative_memLp.toLp _ = _
    have he : gradient ((c • u : DirichletTest R) : E3 → ℝ) = c • gradient (u : E3 → ℝ) :=
      gradient_smul_smooth u.property.1 c
    simp only [he]
    exact u.derivative_memLp.toLp_const_smul c

noncomputable def testGraph (R : ℝ) : DirichletTest R →ₗ[ℝ] SobolevPair :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).symm.toLinearMap.comp
    ((testValueLinear R).prod (testDerivativeLinear R))

def zeroSobolevSpace (R : ℝ) : Submodule ℝ SobolevPair :=
  (testGraph R).range.topologicalClosure

abbrev ZeroSobolev (R : ℝ) := ↥(zeroSobolevSpace R)

instance zeroSobolev_complete (R : ℝ) : CompleteSpace (ZeroSobolev R) :=
  (testGraph R).range.isClosed_topologicalClosure.completeSpace_coe

noncomputable def sobolevValue (R : ℝ) : ZeroSobolev R →L[ℝ] ValueL2 :=
  (WithLp.fstL 2 ℝ ValueL2 DerivativeL2).comp (zeroSobolevSpace R).subtypeL

noncomputable def sobolevDerivative (R : ℝ) : ZeroSobolev R →L[ℝ] DerivativeL2 :=
  (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).comp (zeroSobolevSpace R).subtypeL

noncomputable def poincareConstant (R : ℝ) : ℝ :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure E3) (Metric.ball (0:E3) R) 2 2

lemma poincareConstant_nonneg (R : ℝ) : 0 ≤ poincareConstant R := NNReal.coe_nonneg _

lemma sobolev_poincare (R : ℝ) (u : ZeroSobolev R) :
    ‖sobolevValue R u‖ ≤ poincareConstant R * ‖sobolevDerivative R u‖ := by
  have hc : IsClosed {v : SobolevPair | ‖v.fst‖ ≤ poincareConstant R * ‖v.snd‖} :=
    isClosed_le ((WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous.norm)
      (continuous_const.mul ((WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous.norm))
  have hs : Set.range (testGraph R) ⊆ {v : SobolevPair | ‖v.fst‖ ≤ poincareConstant R * ‖v.snd‖} := by
    rintro v ⟨w,rfl⟩
    exact w.poincare
  exact closure_minimal hs hc u.property

lemma sobolev_norm_sq_le (R : ℝ) (u : ZeroSobolev R) :
    ‖u‖^2 ≤ (poincareConstant R ^ 2 + 1)*‖sobolevDerivative R u‖^2 := by
  have hp := sobolev_poincare R u
  have hn : ‖sobolevValue R u‖^2 ≤ (poincareConstant R * ‖sobolevDerivative R u‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hid := WithLp.prod_norm_sq_eq_of_L2 (u : SobolevPair)
  change ‖u‖^2 = ‖sobolevValue R u‖^2 + ‖sobolevDerivative R u‖^2 at hid
  nlinarith

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
