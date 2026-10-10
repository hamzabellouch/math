import OAI.Dynamics.TriangleBilliards.Generators

namespace OAI

universe uH

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis.HilbertFlow
open Filter
open scoped Topology
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (W : HilbertFlow H)

/-- A genuine strong derivative at zero determines the entire closed
unitary generator; the group law transports it to every time. -/
lemma hasGenerator_of_hasDerivAt_zero {u v : H}
    (h : HasDerivAt (fun t => W.act t u) v 0) : W.HasGenerator u v := by
  apply W.hasGenerator_of_hasDerivAt
  intro t
  have hs : HasDerivAt (fun s => W.act (s - t) u) v t := by
    have h0 : HasDerivAt (fun s => W.act s u) v (id t - t) := by simpa using h
    have hh := h0.scomp (h := fun s : ℝ => s - t) t ((hasDerivAt_id t).sub_const t)
    simpa only [Function.comp_def, id_eq, sub_self, one_smul] using hh
  have hh := ((W.act t).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hs
  apply hh.congr_of_eventuallyEq
  filter_upwards [] with s
  change W.act s u = W.act t (W.act (s - t) u)
  rw [← W.add, show t + (s - t) = s by ring]

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis
open scoped NNReal

/-- The spatial derivative of a smooth seam field is the actual strong
Koopman generator, including trajectories with arbitrarily many reflections.
The asserted generator is proved, not added as a hypothetical analytic input. -/
lemma seam_geodesic_generator {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hxf : MemLp (xDerivative f) 2 (doubleMeasure Q)) :
    (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hxf.toLp (xDerivative f)) := by
  apply (geodesicHilbertFlow Q).hasGenerator_of_hasDerivAt_zero
  apply koopman_hasDerivAt_zero (doubleFlow Q) (measurePreserving_doubleFlow Q)
    (doubleFlow_zero Q) hf hxf
  · filter_upwards [(measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)).quasiMeasurePreserving.ae
      (ae_regularAt Q 0)] with z hz
    obtain ⟨c⟩ := hz.1
    simpa only [doubleFlow_zero] using seam_orbit_hasDerivAt c hs hd 0
  · filter_upwards [(measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)).quasiMeasurePreserving.ae
      (ae_regularAt Q 0)] with z hz
    obtain ⟨c⟩ := hz.1
    exact seam_orbit_lipschitz c hs hd hC
  · exact Filter.Eventually.of_forall fun z => by
      calc
        ‖xDerivative f z‖ ≤ ‖fderiv ℝ (fun y => f ((y,z.1.2),z.2)) z.1.1‖ * ‖(z.1.2 : ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ C := by rw [Circle.norm_coe, mul_one]; exact hC _ _ _

end TriangularBilliards

namespace TriangularBilliards
open Filter Analysis
open scoped Topology ContDiff

lemma parity_add_one_ne_zero_iff (b : ZMod 2) : b + 1 = 0 ↔ b ≠ 0 := by
  exact (show ∀ c : ZMod 2, c + 1 = 0 ↔ c ≠ 0 by decide) b

lemma reflectedDirection_mul (Q : Triangle) (i : Fin 3) (a v : Circle) :
    reflectedDirection Q i (a * v) = a⁻¹ * reflectedDirection Q i v := by
  apply Subtype.ext
  change reflect (Q.tangent i) ((a : ℂ) * (v : ℂ)) =
    (a⁻¹ : Circle) * reflect (Q.tangent i) (v : ℂ)
  rw [Circle.coe_inv_eq_conj]
  simp only [reflect, star_mul', Complex.star_def]
  ring

lemma doubleRotate_seam (Q : Triangle) (i : Fin 3) (a : Circle)
    (x : ℂ) (v : Circle) (b : ZMod 2) :
    doubleRotate a ((wallReflection Q i x, reflectedDirection Q i v), b + 1) =
      ((wallReflection Q i x, reflectedDirection Q i
        ((if b = 0 then a else a⁻¹) * v)), b + 1) := by
  simp only [doubleRotate, reflectedDirection_mul]
  by_cases hb : b = 0
  · simp [hb]
  · simp [hb, (parity_add_one_ne_zero_iff b).mpr hb]

lemma SeamCompatible.rotate {Q : Triangle} {f : DoublePhase → ℂ}
    (hf : SeamCompatible Q f) (a : Circle) : SeamCompatible Q (f ∘ doubleRotate a) := by
  intro i x hx v b
  filter_upwards [hf i x hx ((if b = 0 then a else a⁻¹) * v) b] with y hy
  change f (doubleRotate a ((wallReflection Q i y, reflectedDirection Q i v), b+1)) =
    f (doubleRotate a ((y,v),b))
  rw [doubleRotate_seam]
  exact hy

lemma wallReflection_hasFDerivAt (Q : Triangle) (i : Fin 3) (x : ℂ) :
    HasFDerivAt (wallReflection Q i)
      (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap x := by
  let L : ℂ →L[ℝ] ℂ := (reflectIsometry (Q.tangent i)
    (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : HasFDerivAt (fun y : ℂ => L (y - Q.vertex i)) L x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (Q.vertex i))
  exact hL.const_add (Q.vertex i)

lemma SeamCompatible.xDerivative {Q : Triangle} {f : DoublePhase → ℂ}
    (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) :
    SeamCompatible Q (xDerivative f) := by
  intro i x hx v b
  have he0 : (fun y => f ((wallReflection Q i y, reflectedDirection Q i v),b+1)) =ᶠ[𝓝 x]
      (fun y => f ((y,v),b)) := hf i x hx v b
  have he := he0.fderiv (𝕜 := ℝ)
  filter_upwards [he] with y hy
  have hchain := ((hd (reflectedDirection Q i v) (b+1) (wallReflection Q i y)).hasFDerivAt).comp y
    (wallReflection_hasFDerivAt Q i y)
  have ht := congrArg (fun L : ℂ →L[ℝ] ℂ => L (v : ℂ)) (hchain.fderiv.symm.trans hy)
  exact ht

/-- Spatial smoothness does not require angular differentiability. -/
lemma xDerivative_contDiff {f : DoublePhase → ℂ}
    (hf : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) (v : Circle) (b : ZMod 2) :
    ContDiff ℝ ∞ (fun x => xDerivative f ((x,v),b)) := by
  change ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => f ((y,v),b)) x _)
  exact ((hf v b).fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := (v : ℂ)))

/-- The transverse velocity in the oriented sheet. -/
def transverseVelocity (v : Circle) (b : ZMod 2) : ℂ :=
  (if b = 0 then Complex.I else -Complex.I) * (v : ℂ)

def yDerivative (f : DoublePhase → ℂ) (z : DoublePhase) : ℂ :=
  fderiv ℝ (fun x => f ((x,z.1.2),z.2)) z.1.1 (transverseVelocity z.1.2 z.2)

lemma yDerivative_contDiff {f : DoublePhase → ℂ}
    (hf : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) (v : Circle) (b : ZMod 2) :
    ContDiff ℝ ∞ (fun x => yDerivative f ((x,v),b)) := by
  change ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => f ((y,v),b)) x (transverseVelocity v b))
  exact ((hf v b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma reflect_transverseVelocity (Q : Triangle) (i : Fin 3) (v : Circle) (b : ZMod 2) :
    reflect (Q.tangent i) (transverseVelocity v b) =
      transverseVelocity (reflectedDirection Q i v) (b + 1) := by
  have hneg (e u : ℂ) : reflect e (-u) = -reflect e u := by simp [reflect]
  have hI (e u : ℂ) : reflect e (Complex.I * u) = -Complex.I * reflect e u := by
    simp only [reflect, star_mul', Complex.star_def, Complex.conj_I]; ring
  by_cases hb : b = 0
  · simp only [transverseVelocity, hb, ite_eq_left, zero_add]
    simp only [one_ne_zero, ite_false]
    exact hI _ _
  · simp only [transverseVelocity, hb, ite_false, (parity_add_one_ne_zero_iff b).mpr hb, ite_eq_left]
    change reflect (Q.tangent i) (-Complex.I * (v : ℂ)) =
      Complex.I * reflect (Q.tangent i) (v : ℂ)
    rw [neg_mul, hneg, hI, ← neg_mul, neg_neg]

lemma SeamCompatible.yDerivative {Q : Triangle} {f : DoublePhase → ℂ}
    (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) :
    SeamCompatible Q (yDerivative f) := by
  intro i x hx v b
  have he0 : (fun y => f ((wallReflection Q i y, reflectedDirection Q i v),b+1)) =ᶠ[𝓝 x]
      (fun y => f ((y,v),b)) := hf i x hx v b
  have he := he0.fderiv (𝕜 := ℝ)
  filter_upwards [he] with y hy
  have hchain := ((hd (reflectedDirection Q i v) (b+1) (wallReflection Q i y)).hasFDerivAt).comp y
    (wallReflection_hasFDerivAt Q i y)
  have ht := congrArg (fun L : ℂ →L[ℝ] ℂ => L (transverseVelocity v b)) (hchain.fderiv.symm.trans hy)
  change fderiv ℝ (fun x => f ((x,reflectedDirection Q i v),b+1)) (wallReflection Q i y)
    (reflect (Q.tangent i) (transverseVelocity v b)) = _ at ht
  rw [reflect_transverseVelocity] at ht
  exact ht

lemma x_y_commute {f : DoublePhase → ℂ}
    (hf : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) (z : DoublePhase) :
    xDerivative (yDerivative f) z = yDerivative (xDerivative f) z := by
  have hd := ((hf z.1.2 z.2).fderiv_right (m := ∞) (by simp)).differentiable (by simp) z.1.1
  simp only [xDerivative, yDerivative]
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp
  exact ((hf z.1.2 z.2).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)).eq _ _

end TriangularBilliards

namespace TriangularBilliards.Analysis.HilbertFlow
open scoped Topology
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma HasGenerator.conjugate {W V : HilbertFlow H} {θ : ℝ} {u v : H}
    (h : W.HasGenerator (V.act (-θ) u) (V.act (-θ) v)) :
    (W.conjugate V θ).HasGenerator u v := by
  apply (W.conjugate V θ).hasGenerator_of_hasDerivAt_zero
  have hd := ((V.act θ).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (HasGenerator.hasDerivAt W h 0)
  change HasDerivAt (fun t => V.act θ (W.act t (V.act (-θ) u)))
    (V.act θ (W.act 0 (V.act (-θ) v))) 0 at hd
  rw [W.zero, ← V.add, add_neg_cancel, V.zero] at hd
  exact hd

lemma commuting_generators_inner {X Y : HilbertFlow H} {u a b c : H}
    (hxu : X.HasGenerator u a) (hyu : Y.HasGenerator u b)
    (hxy : X.HasGenerator b c) (hyx : Y.HasGenerator a c) :
    inner ℂ a b = inner ℂ b a := by
  have hx := X.generator_skew hxu hxy
  have hy := Y.generator_skew hyu hyx
  linear_combination hx - hy

lemma commuting_generators_CR {X Y : HilbertFlow H} {u a b c : H}
    (hxu : X.HasGenerator u a) (hyu : Y.HasGenerator u b)
    (hxy : X.HasGenerator b c) (hyx : Y.HasGenerator a c) :
    ‖a + Complex.I • b‖ = ‖a - Complex.I • b‖ := by
  have hi := congrArg Complex.im (commuting_generators_inner hxu hyu hxy hyx)
  have hs := inner_conj_symm (𝕜 := ℂ) a b
  have hsi := congrArg Complex.im hs
  have him : (inner ℂ a b).im = 0 := by simp only [Complex.conj_im] at hsi; linarith
  have hr : (inner ℂ a (Complex.I • b)).re = 0 := by
    rw [inner_smul_right]
    simp [Complex.mul_re, him]
  have he : ‖a + Complex.I • b‖ ^ 2 = ‖a - Complex.I • b‖ ^ 2 := by
    rw [@norm_add_sq ℂ, @norm_sub_sq ℂ]
    change _ + 2 * (inner ℂ a (Complex.I • b)).re + _ =
      _ - 2 * (inner ℂ a (Complex.I • b)).re + _
    rw [hr]; ring
  nlinarith [norm_nonneg (a + Complex.I • b), norm_nonneg (a - Complex.I • b)]

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis
open scoped Topology NNReal

lemma circle_exp_quarter_coe : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  rw [Circle.coe_exp]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

lemma transverseVelocity_neg_quarter (v : Circle) (b : ZMod 2) :
    transverseVelocity ((doubleRotate (Circle.exp (-(Real.pi / 2))) ((0,v),b)).1.2) b = (v : ℂ) := by
  by_cases hb : b = 0
  · simp only [doubleRotate, hb, ite_eq_left, transverseVelocity, Circle.exp_neg,
      Circle.coe_mul, Circle.coe_inv_eq_conj, circle_exp_quarter_coe, Complex.conj_I]
    ring_nf
    simp
  · simp only [doubleRotate, hb, ite_false, transverseVelocity, Circle.exp_neg,
      inv_inv, Circle.coe_mul, circle_exp_quarter_coe]
    ring_nf
    simp

lemma xDerivative_rotate_neg_quarter (f : DoublePhase → ℂ) (z : DoublePhase) :
    xDerivative (f ∘ doubleRotate (Circle.exp (-(Real.pi / 2)))) z =
      yDerivative f (doubleRotate (Circle.exp (-(Real.pi / 2))) z) := by
  exact congrArg (fun u : ℂ => fderiv ℝ
    (fun x => f ((x, (doubleRotate (Circle.exp (-(Real.pi / 2))) z).1.2), z.2))
      z.1.1 u) (transverseVelocity_neg_quarter z.1.2 z.2).symm

lemma angular_toLp (Q : Triangle) (θ : ℝ) {f : DoublePhase → ℂ}
    (hf : MemLp f 2 (doubleMeasure Q)) :
    (angularHilbertFlow Q).act θ (hf.toLp f) =
      (hf.comp_measurePreserving (measurePreserving_doubleRotate Q (Circle.exp θ))).toLp
        (f ∘ doubleRotate (Circle.exp θ)) := by
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_doubleRotate Q (Circle.exp θ))

lemma seam_transverse_generator {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hyf : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    (transverseHilbertFlow Q).HasGenerator (hf.toLp f) (hyf.toLp (yDerivative f)) := by
  apply HilbertFlow.HasGenerator.conjugate
  rw [angular_toLp, angular_toLp]
  let a := Circle.exp (-(Real.pi / 2))
  have he : xDerivative (f ∘ doubleRotate a) = yDerivative f ∘ doubleRotate a :=
    funext (xDerivative_rotate_neg_quarter f)
  have hxy : MemLp (xDerivative (f ∘ doubleRotate a)) 2 (doubleMeasure Q) := by
    rw [he]
    exact hyf.comp_measurePreserving (measurePreserving_doubleRotate Q a)
  convert seam_geodesic_generator (hs.rotate a)
    (fun v b => hd ((if b = 0 then a else a⁻¹) * v) b)
    (fun x v b => hC x ((if b = 0 then a else a⁻¹) * v) b)
    (hf.comp_measurePreserving (measurePreserving_doubleRotate Q a)) hxy using 1
  apply Lp.ext
  filter_upwards [(hyf.comp_measurePreserving (measurePreserving_doubleRotate Q a)).coeFn_toLp,
    hxy.coeFn_toLp] with z hz hzz
  rw [hz, hzz]
  exact congrFun he.symm z

end TriangularBilliards

end
end
end
end
end

end OAI
