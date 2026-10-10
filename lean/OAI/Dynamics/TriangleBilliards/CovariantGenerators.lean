import OAI.Dynamics.TriangleBilliards.CircleFourier

namespace OAI

universe uA uH

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
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis
open scoped Topology

/-- The actual oriented tangent-circle representation on the double. -/
def angularCircleAction (Q : Triangle) : CircleAction (DoubleL2 Q) (2 * Real.pi) where
  act θ := Lp.compMeasurePreservingₗᵢ ℂ (doubleRotate θ.toCircle)
    (measurePreserving_doubleRotate Q θ.toCircle)
  zero u := by
    apply Lp.ext
    change (Lp.compMeasurePreserving (doubleRotate (AddCircle.toCircle (0 : AddCircle (2 * Real.pi)))) _ u : DoublePhase → ℂ) =ᵐ[doubleMeasure Q] u
    filter_upwards [Lp.coeFn_compMeasurePreserving u
      (measurePreserving_doubleRotate Q (AddCircle.toCircle (0 : AddCircle (2 * Real.pi))))] with z hz
    simpa only [AddCircle.toCircle_zero, doubleRotate_one, Function.comp_apply] using hz
  add θ φ u := by
    apply Lp.ext
    have h₁ := Lp.coeFn_compMeasurePreserving u
      (measurePreserving_doubleRotate Q (θ+φ).toCircle)
    have h₂ := Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (doubleRotate φ.toCircle)
        (measurePreserving_doubleRotate Q φ.toCircle) u)
      (measurePreserving_doubleRotate Q θ.toCircle)
    have h₃ := (measurePreserving_doubleRotate Q θ.toCircle).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving u (measurePreserving_doubleRotate Q φ.toCircle))
    filter_upwards [h₁, h₂, h₃] with z h1 h2 h3
    change (Lp.compMeasurePreserving (doubleRotate (θ+φ).toCircle) _ u) z =
      (Lp.compMeasurePreserving (doubleRotate θ.toCircle) _ (Lp.compMeasurePreserving (doubleRotate φ.toCircle) _ u)) z
    rw [h1, h2]
    change u (doubleRotate (θ+φ).toCircle z) = (Lp.compMeasurePreserving (doubleRotate φ.toCircle) _ u) (doubleRotate θ.toCircle z)
    rw [h3]
    change u (doubleRotate (θ+φ).toCircle z) = u (doubleRotate φ.toCircle (doubleRotate θ.toCircle z))
    rw [← doubleRotate_mul, AddCircle.toCircle_add, mul_comm]
  continuous u := by
    apply continuous_coinduced_dom.mpr
    change Continuous (fun t : ℝ => Lp.compMeasurePreservingₗᵢ ℂ
      (doubleRotate (AddCircle.toCircle (t : AddCircle (2 * Real.pi)))) _ u)
    have he (t : ℝ) : AddCircle.toCircle (t : AddCircle (2 * Real.pi)) = Circle.exp t := by
      rw [AddCircle.toCircle_apply_mk, div_self (by positivity : 2 * Real.pi ≠ 0), one_mul]
    simp_rw [he]
    exact (angularHilbertFlow Q).continuous u

lemma angularCircleAction_coe (Q : Triangle) (θ : AddCircle (2 * Real.pi)) (u : DoubleL2 Q) :
    ((angularCircleAction Q).act θ u : DoublePhase → ℂ) =ᵐ[doubleMeasure Q]
      u ∘ doubleRotate θ.toCircle :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_doubleRotate Q θ.toCircle)

instance circlePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- These are actual Fourier projections of the double, not externally
specified coefficient operators. -/
def angularProjection (Q : Triangle) (j : ℤ) : DoubleL2 Q →L[ℂ] DoubleL2 Q :=
  (angularCircleAction Q).projection j

lemma angular_projection_complete (Q : Triangle) (u : DoubleL2 Q) :
    HasSum (fun j : ℤ => angularProjection Q j u) u :=
  (angularCircleAction Q).hasSum_projection u

end TriangularBilliards

namespace TriangularBilliards.Analysis.HilbertFlow
open MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {W : HilbertFlow H}

omit [CompleteSpace H] in
lemma HasGenerator.add {u v a b : H} (h : W.HasGenerator u a) (k : W.HasGenerator v b) :
    W.HasGenerator (u+v) (a+b) := by
  intro t
  rw [map_add, map_add, ← h t, ← k t]
  abel

omit [CompleteSpace H] in
lemma HasGenerator.smul {u a : H} (h : W.HasGenerator u a) (c : ℂ) :
    W.HasGenerator (c • u) (c • a) := by
  intro t
  rw [map_smul, map_smul, ← h t, smul_sub]

lemma HasGenerator.integral {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {u a : A → H} (hu : Integrable u μ) (ha : Integrable a μ)
    (h : ∀ᵐ x ∂μ, W.HasGenerator (u x) (a x)) :
    W.HasGenerator (∫ x, u x ∂μ) (∫ x, a x ∂μ) := by
  intro t
  change (W.act t).toContinuousLinearMap (∫ x, u x ∂μ) - (∫ x, u x ∂μ) =
    (W.timeIntegral 0 t) (∫ x, a x ∂μ)
  rw [← (W.act t).toContinuousLinearMap.integral_comp_comm hu,
    ← (W.timeIntegral 0 t).integral_comp_comm ha,
    ← integral_sub ((W.act t).toContinuousLinearMap.integrable_comp hu) hu]
  exact integral_congr_ae (h.mono fun x hx => hx t)

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis
open scoped Topology

lemma rotated_velocity_decompose (a v : Circle) (b : ZMod 2) :
    (v : ℂ) = (a : ℂ).re • (((if b = 0 then a else a⁻¹) * v : Circle) : ℂ) -
      (a : ℂ).im • transverseVelocity ((if b = 0 then a else a⁻¹) * v) b := by
  have ha := Circle.normSq_coe a
  by_cases hb : b = 0 <;>
    simp only [hb, ite_eq_left, ite_false, transverseVelocity, Circle.coe_mul,
      Circle.coe_inv_eq_conj, Complex.real_smul] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at * <;>
    nlinarith [congrArg (fun t : ℝ => t * (v : ℂ).re) ha,
      congrArg (fun t : ℝ => t * (v : ℂ).im) ha]

lemma rotated_transverse_decompose (a v : Circle) (b : ZMod 2) :
    transverseVelocity v b =
      (a : ℂ).im • (((if b = 0 then a else a⁻¹) * v : Circle) : ℂ) +
      (a : ℂ).re • transverseVelocity ((if b = 0 then a else a⁻¹) * v) b := by
  have ha := Circle.normSq_coe a
  by_cases hb : b = 0 <;>
    simp only [hb, ite_eq_left, ite_false, transverseVelocity, Circle.coe_mul,
      Circle.coe_inv_eq_conj, Complex.real_smul] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at * <;>
    nlinarith [congrArg (fun t : ℝ => t * (v : ℂ).re) ha,
      congrArg (fun t : ℝ => t * (v : ℂ).im) ha]

lemma xDerivative_rotate (a : Circle) (f : DoublePhase → ℂ) (z : DoublePhase) :
    xDerivative (f ∘ doubleRotate a) z =
      (a : ℂ).re • xDerivative f (doubleRotate a z) -
        (a : ℂ).im • yDerivative f (doubleRotate a z) := by
  change fderiv ℝ (fun x => f ((x, _), z.2)) z.1.1 (z.1.2 : ℂ) = _
  rw [rotated_velocity_decompose a z.1.2 z.2, map_sub, map_smul, map_smul]
  rfl

lemma yDerivative_rotate (a : Circle) (f : DoublePhase → ℂ) (z : DoublePhase) :
    yDerivative (f ∘ doubleRotate a) z =
      (a : ℂ).im • xDerivative f (doubleRotate a z) +
        (a : ℂ).re • yDerivative f (doubleRotate a z) := by
  change fderiv ℝ (fun x => f ((x, _), z.2)) z.1.1 (transverseVelocity z.1.2 z.2) = _
  rw [rotated_transverse_decompose a z.1.2 z.2, map_add, map_smul, map_smul]
  rfl

end TriangularBilliards

namespace TriangularBilliards
open Analysis
open scoped Topology NNReal

lemma circleAction_toLp (Q : Triangle) (θ : AddCircle (2 * Real.pi))
    {f : DoublePhase → ℂ} (hf : MemLp f 2 (doubleMeasure Q)) :
    (angularCircleAction Q).act θ (hf.toLp f) =
      (hf.comp_measurePreserving (measurePreserving_doubleRotate Q θ.toCircle)).toLp
        (f ∘ doubleRotate θ.toCircle) :=
  Lp.toLp_compMeasurePreserving hf (measurePreserving_doubleRotate Q θ.toCircle)

lemma rotate_x_memLp (Q : Triangle) (a : Circle) {f : DoublePhase → ℂ}
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    MemLp (xDerivative (f ∘ doubleRotate a)) 2 (doubleMeasure Q) := by
  have he : xDerivative (f ∘ doubleRotate a) =
      (a : ℂ).re • (xDerivative f ∘ doubleRotate a) -
        (a : ℂ).im • (yDerivative f ∘ doubleRotate a) := funext (xDerivative_rotate a f)
  rw [he]
  exact ((hx.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _).sub
    ((hy.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _)

lemma rotate_y_memLp (Q : Triangle) (a : Circle) {f : DoublePhase → ℂ}
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    MemLp (yDerivative (f ∘ doubleRotate a)) 2 (doubleMeasure Q) := by
  have he : yDerivative (f ∘ doubleRotate a) =
      (a : ℂ).im • (xDerivative f ∘ doubleRotate a) +
        (a : ℂ).re • (yDerivative f ∘ doubleRotate a) := funext (yDerivative_rotate a f)
  rw [he]
  exact ((hx.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _).add
    ((hy.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _)

lemma seam_rotated_generators {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q))
    (θ : AddCircle (2 * Real.pi)) :
    (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).act θ (hf.toLp f))
      ((θ.toCircle : ℂ).re • (angularCircleAction Q).act θ (hx.toLp (xDerivative f)) -
        (θ.toCircle : ℂ).im • (angularCircleAction Q).act θ (hy.toLp (yDerivative f))) ∧
    (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).act θ (hf.toLp f))
      ((θ.toCircle : ℂ).im • (angularCircleAction Q).act θ (hx.toLp (xDerivative f)) +
        (θ.toCircle : ℂ).re • (angularCircleAction Q).act θ (hy.toLp (yDerivative f))) := by
  let a := θ.toCircle
  have hxf := rotate_x_memLp Q a hx hy
  have hyf := rotate_y_memLp Q a hx hy
  have h₁ := seam_geodesic_generator (hs.rotate a)
    (fun v b => hd ((if b = 0 then a else a⁻¹) * v) b)
    (fun x v b => hC x ((if b = 0 then a else a⁻¹) * v) b)
    (hf.comp_measurePreserving (measurePreserving_doubleRotate Q a)) hxf
  have h₂ := seam_transverse_generator (hs.rotate a)
    (fun v b => hd ((if b = 0 then a else a⁻¹) * v) b)
    (fun x v b => hC x ((if b = 0 then a else a⁻¹) * v) b)
    (hf.comp_measurePreserving (measurePreserving_doubleRotate Q a)) hyf
  rw [← circleAction_toLp Q θ hf] at h₁ h₂
  have ex : hxf.toLp _ = (a : ℂ).re • (angularCircleAction Q).act θ (hx.toLp _) -
      (a : ℂ).im • (angularCircleAction Q).act θ (hy.toLp _) := by
    apply Lp.ext
    filter_upwards [hxf.coeFn_toLp,
      Lp.coeFn_sub ((a : ℂ).re • (angularCircleAction Q).act θ (hx.toLp _))
        ((a : ℂ).im • (angularCircleAction Q).act θ (hy.toLp _)),
      Lp.coeFn_smul (a : ℂ).re ((angularCircleAction Q).act θ (hx.toLp _)),
      Lp.coeFn_smul (a : ℂ).im ((angularCircleAction Q).act θ (hy.toLp _)),
      angularCircleAction_coe Q θ (hx.toLp _), angularCircleAction_coe Q θ (hy.toLp _),
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hx.coeFn_toLp,
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hy.coeFn_toLp]
      with z h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Pi.sub_apply, Pi.smul_apply] at h1 h2 h3
    rw [h0, h1, h2, h3, h4, h5]
    change _ = (a : ℂ).re • (hx.toLp _) (doubleRotate a z) -
      (a : ℂ).im • (hy.toLp _) (doubleRotate a z)
    rw [h6, h7, xDerivative_rotate]
  have ey : hyf.toLp _ = (a : ℂ).im • (angularCircleAction Q).act θ (hx.toLp _) +
      (a : ℂ).re • (angularCircleAction Q).act θ (hy.toLp _) := by
    apply Lp.ext
    filter_upwards [hyf.coeFn_toLp,
      Lp.coeFn_add ((a : ℂ).im • (angularCircleAction Q).act θ (hx.toLp _))
        ((a : ℂ).re • (angularCircleAction Q).act θ (hy.toLp _)),
      Lp.coeFn_smul (a : ℂ).im ((angularCircleAction Q).act θ (hx.toLp _)),
      Lp.coeFn_smul (a : ℂ).re ((angularCircleAction Q).act θ (hy.toLp _)),
      angularCircleAction_coe Q θ (hx.toLp _), angularCircleAction_coe Q θ (hy.toLp _),
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hx.coeFn_toLp,
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hy.coeFn_toLp]
      with z h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Pi.add_apply, Pi.smul_apply] at h1 h2 h3
    rw [h0, h1, h2, h3, h4, h5]
    change _ = (a : ℂ).im • (hx.toLp _) (doubleRotate a z) +
      (a : ℂ).re • (hy.toLp _) (doubleRotate a z)
    rw [h6, h7, yDerivative_rotate]
  exact ⟨by simpa only [ex] using h₁, by simpa only [ey] using h₂⟩

end TriangularBilliards

namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]

/-- Covariant first-derivative data, stated as actual generator graphs.
The smooth seam producer below supplies these graphs for billiard fields. -/
def RotationalCR (X Y : HilbertFlow H) (V : CircleAction H T) (u a b : H) : Prop :=
  ∀ θ, X.HasGenerator (V.act θ u)
      (fourier (-1) θ • V.act θ a + fourier 1 θ • V.act θ b) ∧
    Y.HasGenerator (V.act θ u)
      (Complex.I • (fourier (-1) θ • V.act θ a - fourier 1 θ • V.act θ b))

namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T} {u a b : H}

omit [CompleteSpace H] [Fact (0 < T)] in
lemma generators (h : RotationalCR X Y V u a b) :
    X.HasGenerator u (a+b) ∧ Y.HasGenerator u (Complex.I • (a-b)) := by
  simpa only [fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one, one_smul,
    V.zero] using h 0

lemma projection (h : RotationalCR X Y V u a b) (j : ℤ) :
    X.HasGenerator (V.projection j u) (V.projection (j+1) a + V.projection (j-1) b) ∧
    Y.HasGenerator (V.projection j u)
      (Complex.I • (V.projection (j+1) a - V.projection (j-1) b)) := by
  have hx (θ : AddCircle T) : X.HasGenerator (fourier (-j) θ • V.act θ u)
      (fourier (-(j+1)) θ • V.act θ a + fourier (-(j-1)) θ • V.act θ b) := by
    have hh := (h θ).1.smul (fourier (-j) θ)
    simpa only [smul_add, smul_smul, ← fourier_add, show -j + -1 = -(j+1) by ring,
      show -j + 1 = -(j-1) by ring] using hh
  have hy (θ : AddCircle T) : Y.HasGenerator (fourier (-j) θ • V.act θ u)
      (Complex.I • (fourier (-(j+1)) θ • V.act θ a - fourier (-(j-1)) θ • V.act θ b)) := by
    have hh := (h θ).2.smul (fourier (-j) θ)
    rw [smul_comm (fourier (-j) θ) Complex.I] at hh
    simpa only [smul_sub, smul_smul, ← fourier_add, show -j + -1 = -(j+1) by ring,
      show -j + 1 = -(j-1) by ring] using hh
  have hxi := HilbertFlow.HasGenerator.integral (V.weighted_integrable j u)
    ((V.weighted_integrable (j+1) a).add (V.weighted_integrable (j-1) b))
    (Filter.Eventually.of_forall hx)
  have hyi := HilbertFlow.HasGenerator.integral (V.weighted_integrable j u)
    (((V.weighted_integrable (j+1) a).sub (V.weighted_integrable (j-1) b)).smul Complex.I)
    (Filter.Eventually.of_forall hy)
  simp only [Pi.add_apply] at hxi
  simp only [Pi.sub_apply, Pi.smul_apply] at hyi
  rw [integral_add (V.weighted_integrable (j+1) a) (V.weighted_integrable (j-1) b)] at hxi
  rw [integral_smul, integral_sub (V.weighted_integrable (j+1) a)
    (V.weighted_integrable (j-1) b)] at hyi
  exact ⟨hxi, hyi⟩

end RotationalCR
end TriangularBilliards.Analysis

end
end
end
end
end
end
end

end OAI
